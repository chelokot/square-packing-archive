import { expect, test, vi } from "vitest";
import { renderToStaticMarkup } from "react-dom/server";
import { App } from "./App.tsx";
import { archive } from "./archive.ts";

vi.mock("./selection.ts", () => ({ useSelection: () => [61, () => {}] }));

test("an uncatalogued selection uses the same verified grid bound throughout the page", () => {
  const markup = renderToStaticMarkup(<App />);
  expect(markup).toContain(
    "n = 61: Upper bound · s(61) ≤ 8 · Basic grid bound",
  );
  expect(markup).toContain("61 unit squares");
  expect(markup.match(/data-square-id=/g)).toHaveLength(61);
  expect(markup).toContain("s(61) ≤ 8");
  expect(markup).not.toContain("Lean verified");
  expect(markup).not.toContain("Rotated packings");
  expect(markup).toContain("Every result has a proof");
  expect(markup).toContain(
    'href="https://github.com/chelokot/square-packing-archive/blob/main/formal/SquarePackingArchive/Records/GridBounds.lean"',
  );
  expect(markup).toContain("No results catalogued for this n yet.");
  expect(markup).toContain(`>${archive.claims.length}</dd>`);
  expect(markup).toContain(">34</dd>");
  expect(markup).not.toContain("Coordinates not yet in the archive");
});
