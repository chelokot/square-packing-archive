import { renderToStaticMarkup } from "react-dom/server";
import { describe, expect, test } from "vitest";
import {
  goebelConfiguration,
  gridBaselineFor,
  gridBaselineConfiguration,
} from "@square-packing/domain";
import { PackingViewer } from "./PackingViewer.tsx";
import { formatExact } from "../geometry.ts";
import { archive } from "../archive.ts";

describe("packing reconstructions", () => {
  test.each([5, 6, 10, 13, 22, 33, 99])(
    "renders all %s squares at the archived bound",
    (count) => {
      const configuration = archive.configurationData.find(
        ({ n }) => n === count,
      )!;
      const claim = archive.claims.find(
        (claim) => claim.configuration === configuration.id,
      );
      const markup = renderToStaticMarkup(
        <PackingViewer configuration={configuration} claim={claim} />,
      );
      expect(markup.match(/data-square-id=/g)).toHaveLength(count);
      expect(markup).toContain(configuration.containerSide.decimal);
      expect(markup).not.toContain("Basic grid bound");
    },
  );

  test("shows a checked baseline with its proof and explicit non-optimality notice", () => {
    const baseline = gridBaselineFor(archive, 61)!;
    const markup = renderToStaticMarkup(
      <PackingViewer
        configuration={gridBaselineConfiguration(baseline)}
        claim={baseline}
      />,
    );
    expect(markup).toContain("Basic grid bound");
    expect(markup).toContain("not its optimality");
    expect(markup).toContain("not a historical record");
    expect(markup).toContain("Lean verified");
    expect(markup).toContain(
      'href="https://github.com/chelokot/square-packing-archive/blob/main/formal/SquarePackingArchive/Records/GridBounds.lean"',
    );
    expect(markup).toContain(
      'title="SquarePackingArchive.Records.GridBounds.grid_hasPacking"',
    );
    expect(markup.match(/data-square-id=/g)).toHaveLength(61);
  });

  test("preserves square-root expressions for inspection and downloads", () => {
    const configuration = goebelConfiguration(
      "square-10-goebel",
      10,
      "2026-09-05",
    );
    expect(formatExact(configuration.squares[4]!.center.x)).toBe("1 + 1/4·√2");
    expect(
      formatExact(configuration.squares[4]!.orientation.tangentHalfAngle),
    ).toBe("-1 + √2");
    expect(formatExact(configuration.containerSide)).toBe("3 + 1/2·√2");
    expect(
      JSON.parse(JSON.stringify(configuration)).containerSide.sqrtTwo,
    ).toEqual({ numerator: "1", denominator: "2" });
  });
});
