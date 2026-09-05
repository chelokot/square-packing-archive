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

  test("keeps published exact results amber and uncatalogued cells unmarked", () => {
    expect(cellMarkup(6)).toContain("n = 6: Exact · Published · awaiting Lean");
    expect(cellMarkup(6)).toContain("bg-ochre-soft");
    expect(cellMarkup(61)).toContain("n = 61: Not catalogued");
    for (const symbol of ["=", "≤", "≥"]) {
      expect(cellMarkup(61)).not.toContain(`>${symbol}</span>`);
    }
  });
});
