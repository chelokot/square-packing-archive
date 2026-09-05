import { describe, expect, test } from "vitest";
import { renderToStaticMarkup } from "react-dom/server";
import { archive } from "../archive.ts";
import { CoverageMatrix } from "./CoverageMatrix.tsx";

const markup = renderToStaticMarkup(
  <CoverageMatrix archive={archive} selectedCount={69} onSelect={() => {}} />,
);

const cellMarkup = (count: number): string => {
  const cell = markup.match(
    new RegExp(`<button[^>]*aria-label="n = ${count}:[\\s\\S]*?</button>`),
  );
  if (cell === null) throw new Error(`Missing matrix cell ${count}`);
  return cell[0];
};

describe("coverage matrix claim types", () => {
  test("highlights upper-bound symbols without changing evidence colors", () => {
    for (const count of [11, 12, 68, 69]) {
      expect(cellMarkup(count)).toMatch(
        /<span[^>]*class="[^"]*text-bound[^"]*"[^>]*>≤<\/span>/,
      );
    }
    expect(cellMarkup(11)).toContain("bg-paper");
    for (const count of [12, 68, 69]) {
      expect(cellMarkup(count)).toContain("bg-forest-soft");
    }
    expect(cellMarkup(13)).not.toContain("text-bound");
    expect(markup).toMatch(
      /<span[^>]*class="[^"]*text-bound[^"]*"[^>]*>≤<\/span>/,
    );
  });

  test("bounds tooltips by the grid instead of the surrounding window", () => {
    expect(markup).toContain('class="@container grid grid-cols-10 gap-1"');
    for (let count = 1; count <= 100; count += 1) {
      const cell = cellMarkup(count);
      expect(cell).toContain("max-w-[min(16rem,50cqw)]");
      expect(cell).not.toContain("45vw");
      expect(cell).toContain((count - 1) % 10 < 5 ? 'left-0"' : 'right-0"');
    }
  });

  test.each([
    [6, "Exact", "=", "s(6) = 3"],
    [10, "Exact", "=", "s(10) = 3 + √2 / 2"],
    [13, "Exact", "=", "s(13) = 4"],
    [22, "Exact", "=", "s(22) = 5"],
    [33, "Exact", "=", "s(33) = 6"],
    [64, "Exact", "=", "s(64) = 8"],
    [69, "Upper bound", "≤", "s(69) ≤ 8.8272"],
  ])(
    "labels n=%i with its own relation and evidence",
    (count, relation, symbol, value) => {
      const cell = cellMarkup(count);
      expect(cell).toContain(
        `aria-label="n = ${count}: ${relation} · Lean verified · ${value}"`,
      );
      expect(cell).toContain(`>${symbol}</span>`);
      expect(cell).toContain("bg-forest-soft");
    },
  );

  test("shows exactness when the archive also has a checked construction", () => {
    expect(cellMarkup(5)).toContain("n = 5: Exact · Lean verified");
    expect(cellMarkup(5)).toContain(">=</span>");
  });

  test("keeps a published exact claim amber until it has Lean evidence", () => {
    const published = renderToStaticMarkup(
      <CoverageMatrix
        archive={{
          ...archive,
          claims: archive.claims.map((claim) =>
            claim.id === "exact-13-bentz"
              ? {
                  ...claim,
                  evidence: claim.evidence.filter(
                    (evidence) => evidence.kind !== "lean-proof",
                  ),
                }
              : claim,
          ),
        }}
        selectedCount={13}
        onSelect={() => {}}
      />,
    );
    const cell = published.match(
      /<button[^>]*aria-label="n = 13:[\s\S]*?<\/button>/,
    );
    expect(cell).not.toBeNull();
    expect(cell![0]).toContain("n = 13: Exact · Published · awaiting Lean");
    expect(cell![0]).toContain("bg-ochre-soft");
    expect(cell![0]).toContain(">=</span>");
  });

  test("fills uncatalogued cells with checked grid bounds, never exactness", () => {
    expect(cellMarkup(61)).toContain(
      "n = 61: Upper bound · Lean verified · s(61) ≤ 8 · Basic grid bound",
    );
    expect(cellMarkup(61)).toContain("bg-forest-soft");
    expect(cellMarkup(61)).toMatch(
      /<span[^>]*class="[^"]*text-bound[^"]*"[^>]*>≤<\/span>/,
    );
    for (const symbol of ["=", "≥"]) {
      expect(cellMarkup(61)).not.toContain(`>${symbol}</span>`);
    }
  });
});
