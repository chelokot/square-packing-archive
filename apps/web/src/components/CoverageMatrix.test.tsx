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

describe("coverage matrix", () => {
  test("uses green only for proved optima and white for bounds", () => {
    for (const count of [5, 6, 10, 13, 22, 33, 64]) {
      expect(cellMarkup(count)).toContain("bg-forest-soft");
    }
    for (const count of [11, 12, 61, 68, 69, 100]) {
      expect(cellMarkup(count)).toContain("bg-surface");
      expect(cellMarkup(count)).not.toContain("bg-forest-soft");
    }
    expect(markup).toContain("Proved optimal");
    expect(markup).toContain("Bound only");
  });

  test("offers exactly 100 direct selections without redundant controls or symbols", () => {
    expect(markup.match(/<button /g)).toHaveLength(100);
    expect(cellMarkup(69)).toContain('aria-pressed="true"');
    expect(cellMarkup(68)).toContain('aria-pressed="false"');
    for (const removed of [
      "<select",
      "Rotated packings",
      "Lean verified",
      "Lean checked",
      "Counts without catalogued records",
      ">=</span>",
      ">≤</span>",
      ">≥</span>",
    ]) {
      expect(markup).not.toContain(removed);
    }
  });

  test("bounds tooltips by the grid instead of the surrounding window", () => {
    expect(markup).toContain('class="@container mt-4 grid grid-cols-10 gap-1"');
    for (let count = 1; count <= 100; count += 1) {
      const cell = cellMarkup(count);
      expect(cell).toContain("max-w-[min(16rem,50cqw)]");
      expect(cell).not.toContain("45vw");
      expect(cell).toContain((count - 1) % 10 < 5 ? 'left-0"' : 'right-0"');
    }
  });

  test.each([
    [6, "Exact · s(6) = 3"],
    [10, "Exact · s(10) = 3 + √2 / 2"],
    [11, "Upper bound · s(11) ≤ 97 / 25"],
    [13, "Exact · s(13) = 4"],
    [69, "Upper bound · s(69) ≤ 8.8272"],
    [61, "Upper bound · s(61) ≤ 8 · Basic grid bound"],
  ])(
    "keeps the actual relation and value accessible for n=%i",
    (count, description) => {
      expect(cellMarkup(count)).toContain(
        `aria-label="n = ${count}: ${description}"`,
      );
    },
  );
});
