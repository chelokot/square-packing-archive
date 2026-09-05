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

  test("shows the baseline inequality and its proof without a repeated verification badge", () => {
    const baseline = gridBaselineFor(archive, 61)!;
    const markup = renderToStaticMarkup(
      <PackingViewer
        configuration={gridBaselineConfiguration(baseline)}
        claim={baseline}
      />,
    );
    expect(markup).toContain("Basic grid bound");
    expect(markup).toContain("s(61) ≤ 8");
    expect(markup).not.toContain("Lean verified");
    expect(markup).toContain(
      'href="https://github.com/chelokot/square-packing-archive/blob/main/formal/SquarePackingArchive/Records/GridBounds.lean"',
    );
    expect(markup).toContain(
      'title="SquarePackingArchive.Records.GridBounds.grid_hasPacking"',
    );
    expect(markup.match(/data-square-id=/g)).toHaveLength(61);
  });

  test.each([6, 11])(
    "shows orientation controls only for multiple groups at n=%i",
    (count) => {
      const configuration = archive.configurationData.find(
        ({ n }) => n === count,
      )!;
      const markup = renderToStaticMarkup(
        <PackingViewer configuration={configuration} claim={undefined} />,
      );
      expect(markup.includes(">Orientation groups</h4>")).toBe(count === 11);
      expect(markup).toContain('aria-label="Viewer help"');
      expect(markup.match(/<details[^>]*open/g)).toBeNull();
      const help = markup.match(/<details[\s\S]*?<\/details>/)![0];
      expect(help).toContain("Drag to pan");
      expect(help).toContain("Select a square in the drawing");
      expect(help.includes("Angles grouped")).toBe(count === 11);
      expect(markup.match(/Select a square in the drawing/g)).toHaveLength(1);
    },
  );

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
