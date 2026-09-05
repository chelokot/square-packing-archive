import { describe, expect, test } from "vitest";
import { renderToStaticMarkup } from "react-dom/server";
import { archive } from "../archive.ts";
import { CoverageOverview } from "./CoverageOverview.tsx";

const markup = renderToStaticMarkup(<CoverageOverview archive={archive} />);

describe("README coverage overview", () => {
  test("shows only a number in each cell, with a two-color legend", () => {
    expect(markup.match(/<text /g)).toHaveLength(105);
    expect(markup).toContain("Proved optimal");
    expect(markup).toContain("Bound only");
    expect(markup).not.toContain("Lean verified");
    expect(markup).not.toContain(">≤</text>");
    expect(markup).not.toContain(">=</text>");
  });

  test("renders every square count exactly once in order", () => {
    const counts = [...markup.matchAll(/data-n="(\d+)"/g)].map((match) =>
      Number(match[1]),
    );
    expect(counts).toEqual(
      Array.from({ length: 100 }, (_, index) => index + 1),
    );
  });

  test.each([
    [5, "Exact", "#e1e9dc"],
    [6, "Exact", "#e1e9dc"],
    [10, "Exact", "#e1e9dc"],
    [64, "Exact", "#e1e9dc"],
    [69, "Upper bound", "#fffef9"],
    [13, "Exact", "#e1e9dc"],
    [22, "Exact", "#e1e9dc"],
    [33, "Exact", "#e1e9dc"],
    [61, "Upper bound", "#fffef9"],
  ])(
    "renders the actual claim and exactness color for n=%i",
    (count, label, fill) => {
      const cell = markup.match(new RegExp(`<g data-n="${count}"[^]*?</g>`));
      expect(cell).not.toBeNull();
      expect(cell![0]).toContain(`n = ${count}: ${label}`);
      expect(cell![0]).toContain(`fill="${fill}"`);
    },
  );

  test("takes the update date and claim changes from the supplied archive", () => {
    const updated = renderToStaticMarkup(
      <CoverageOverview
        archive={{
          ...archive,
          updatedAt: "2026-10-01",
          claims: archive.claims.filter((claim) => claim.n !== 69),
        }}
      />,
    );
    expect(updated).toContain("2026-10-01");
    expect(updated).toContain(
      "n = 69: Upper bound · s(69) ≤ 9 · Basic grid bound",
    );
    expect(updated).not.toContain("s(69) ≤ 8.8272");
  });

  test("does not manufacture verification without a baseline policy", () => {
    const withoutBaseline = renderToStaticMarkup(
      <CoverageOverview archive={{ ...archive, gridBaseline: undefined }} />,
    );
    expect(withoutBaseline).toContain("n = 61: Not catalogued");
    expect(withoutBaseline).not.toContain("s(61)");
  });
});
