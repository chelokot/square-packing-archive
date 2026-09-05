import { renderToStaticMarkup } from "react-dom/server";
import { describe, expect, test } from "vitest";
import { goebelConfiguration, gridConfiguration } from "@square-packing/domain";
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
      expect(markup).not.toContain("Grid example, not a best-known record");
    },
  );

  test("labels an uncatalogued grid as an example, without a verification badge", () => {
    const markup = renderToStaticMarkup(
      <PackingViewer
        configuration={gridConfiguration(
          "square-61-example",
          61,
          8,
          "2026-09-05",
        )}
        claim={undefined}
        isGridExample
      />,
    );
    expect(markup).toContain("Grid example, not a best-known record");
    expect(markup).not.toContain("Lean verified");
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
