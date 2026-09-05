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
  expect(markup).toContain(">34</span> proved optimal");
  expect(markup).not.toContain("Coordinates not yet in the archive");
});

test("keeps the introduction compact without removing the catalog or proof policy", () => {
  const markup = renderToStaticMarkup(<App />);
  expect(markup).toContain("<h1>Square Packing Archive</h1>");
  for (const removed of [
    "Small squares. A surprisingly hard problem.",
    "Discrete geometry",
    "claims catalogued",
    "catalogued coordinate sets",
    ">01<",
    ">02<",
    ">03<",
  ]) {
    expect(markup).not.toContain(removed);
  }
  expect(markup).toContain("lg:grid-cols-[21rem_minmax(0,1fr)]");
  expect(markup).toContain('id="claims"');
  expect(markup).toContain('id="formalization"');
  expect(markup).toContain("Every result has a proof");
  const footer = markup.slice(markup.indexOf("<footer"));
  expect(footer).toContain(`Data updated ${archive.updatedAt}`);
  expect(markup.slice(0, markup.indexOf("<footer"))).not.toContain(
    "Data updated",
  );
});
