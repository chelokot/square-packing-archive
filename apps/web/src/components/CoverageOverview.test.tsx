import { describe, expect, test } from "vitest";
import { renderToStaticMarkup } from "react-dom/server";
import { archive } from "../archive.ts";
import { CoverageOverview } from "./CoverageOverview.tsx";

const markup = renderToStaticMarkup(<CoverageOverview archive={archive} />);

describe("README coverage overview", () => {
  test("renders every square count exactly once in order", () => {
    const counts = [...markup.matchAll(/data-n="(\d+)"/g)].map((match) =>
      Number(match[1]),
    );
    expect(counts).toEqual(
      Array.from({ length: 100 }, (_, index) => index + 1),
    );
  });

  test.each([
    [5, "Exact · Lean verified", "=", "#e1e9dc"],
    [6, "Exact · Lean verified", "=", "#e1e9dc"],
    [64, "Exact · Lean verified", "=", "#e1e9dc"],
    [69, "Upper bound · Lean verified", "≤", "#e1e9dc"],
    [13, "Exact · Published · awaiting Lean", "=", "#f3e8d4"],
  ])(
    "renders the claim and evidence together for n=%i",
    (count, label, symbol, fill) => {
      const cell = markup.match(new RegExp(`<g data-n="${count}"[^]*?</g>`));
      expect(cell).not.toBeNull();
      expect(cell![0]).toContain(`n = ${count}: ${label}`);
      expect(cell![0]).toContain(`>${symbol}</text>`);
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
    expect(updated).toContain("n = 69: Not catalogued");
    expect(updated).not.toContain("s(69)");
  });
});
