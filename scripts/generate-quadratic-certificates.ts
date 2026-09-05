import { parseArgs } from "node:util";
import { mkdir } from "node:fs/promises";
import { dirname } from "node:path";
import {
  analyzeConfigurationGeometry,
  manifestSchema,
  packingConfigurationSchema,
  type ExactNumber,
  type PackingConfiguration,
} from "@square-packing/domain";
import { fromExact } from "../packages/domain/src/exact.ts";

export const certificateNamespace = (identifier: string): string =>
  identifier
    .split("-")
    .map((part) => part[0]!.toUpperCase() + part.slice(1))
    .join("");

const rational = (value: { numerator: bigint; denominator: bigint }): string =>
  value.denominator === 1n
    ? `(${value.numerator} : ℚ)`
    : `((${value.numerator} : ℚ) / ${value.denominator})`;

const quadratic = (value: ExactNumber): string => {
  const exact = fromExact(value);
  return `{ rational := ${rational(exact.rational)}, radical := ${rational(exact.radical)} }`;
};

export const certificateValue = (
  configuration: PackingConfiguration,
): string => {
  const exact = fromExact(configuration.containerSide);
  if (exact.radical.numerator === 0n)
    return `(${rational(exact.rational)} : ℝ)`;
  return `(${rational(exact.rational)} : ℝ) + (${rational(exact.radical)} : ℝ) * Real.sqrt ${exact.radicand}`;
};

export const renderQuadraticCertificate = (
  configuration: PackingConfiguration,
): string => {
  const checked = packingConfigurationSchema.parse(configuration);
  const { errors, separatingAxes } = analyzeConfigurationGeometry(checked);
  if (errors.length > 0) throw new Error(errors.join("\n"));
  const values = [
    checked.containerSide,
    ...checked.squares.flatMap(({ center, orientation }) => [
      center.x,
      center.y,
      orientation.cosine,
      orientation.sine,
    ]),
  ];
  const radicand = values.reduce((field, value) => {
    const candidate = fromExact(value).radicand;
    return candidate > field ? candidate : field;
  }, 0n);
  const namespace = certificateNamespace(checked.id);
  const squares = checked.squares
    .map(
      ({ center, orientation }) =>
        `    { centerX := ${quadratic(center.x)}, centerY := ${quadratic(center.y)}, cosine := ${quadratic(orientation.cosine)}, sine := ${quadratic(orientation.sine)} }`,
    )
    .join(",\n");
  const axes = separatingAxes
    .map((row) => `    #v[${row.map((axis) => `.${axis}`).join(", ")}]`)
    .join(",\n");
  const rowProofs = checked.squares
    .map(
      (_, index) =>
        `private theorem separated_row_${index} : certificate.SeparatedRow ${index} := by decide +kernel`,
    )
    .join("\n\n");
  const rowCases = checked.squares
    .map((_, index) => `  · exact separated_row_${index}`)
    .join("\n");
  return `import SquarePackingArchive.QuadraticCertificate
import Mathlib.Tactic.FinCases

namespace SquarePackingArchive.Records.${namespace}

def certificate : QuadraticCertificate ${radicand} ${checked.n} where
  side := ${quadratic(checked.containerSide)}
  squares := #v[
${squares}
  ]
  separatingAxes := #v[
${axes}
  ]

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem boundaries_valid : certificate.BoundariesValid := by decide +kernel

${rowProofs}

theorem certificate_valid : certificate.Valid := by
  apply QuadraticCertificate.valid_of_rows boundaries_valid
  intro left
  fin_cases left
${rowCases}

theorem upper_bound : HasPacking ${checked.n} (${certificateValue(checked)}) := by
  simpa [certificate, QuadraticNumber.toReal] using QuadraticCertificate.valid_sound certificate_valid

end SquarePackingArchive.Records.${namespace}
`;
};

if (import.meta.main) {
  const { values, positionals } = parseArgs({
    args: process.argv.slice(2),
    options: {
      check: { type: "boolean", default: false },
      "check-all": { type: "boolean", default: false },
    },
    allowPositionals: true,
  });
  if (values["check-all"]) {
    const manifest = manifestSchema.parse(
      await Bun.file("archive/manifest.json").json(),
    );
    for (const reference of manifest.configurations) {
      if (!("path" in reference)) continue;
      const configuration = packingConfigurationSchema.parse(
        await Bun.file(`archive/${reference.path}`).json(),
      );
      if (
        configuration.certificate.method !== "exact-quadratic-separating-axis"
      )
        continue;
      const artifact = `formal/SquarePackingArchive/Records/${certificateNamespace(reference.id)}.lean`;
      const actual = await Bun.file(artifact).text();
      if (actual !== renderQuadraticCertificate(configuration))
        throw new Error(`Stale certificate: ${artifact}`);
    }
  } else {
    if (positionals.length !== 2)
      throw new Error(
        "Usage: generate-quadratic-certificates.ts configuration.json destination.lean [--check]",
      );
    const [source, destination] = positionals as [string, string];
    const configuration = packingConfigurationSchema.parse(
      await Bun.file(source).json(),
    );
    const generated = renderQuadraticCertificate(configuration);
    if (values.check) {
      if ((await Bun.file(destination).text()) !== generated)
        throw new Error(`Stale certificate: ${destination}`);
    } else {
      await mkdir(dirname(destination), { recursive: true });
      await Bun.write(destination, generated);
      console.log(destination);
    }
  }
}
