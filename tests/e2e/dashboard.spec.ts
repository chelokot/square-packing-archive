import { expect, test } from "@playwright/test";
import { activeClaims, manifestSchema } from "@square-packing/domain";
import manifestJson from "../../archive/manifest.json";

const claims = activeClaims(manifestSchema.parse(manifestJson));

test("opens a packing, inspects exact coordinates, and controls the view", async ({
  page,
}) => {
  await page.goto("./?n=68");
  await expect(page.getByRole("heading", { level: 1 })).toHaveText(
    "Small squares. A surprisingly hard problem.",
  );
  const viewer = page.locator("#viewer");
  await viewer.getByRole("button", { name: "Square 0", exact: true }).click();
  await expect(viewer.getByText("Exact t = tan(θ/2)")).toBeVisible();
  await expect(
    viewer.getByRole("heading", { name: /^Square 0\b/ }),
  ).toBeVisible();
  await viewer.getByRole("button", { name: "Zoom in", exact: true }).click();
  await expect(viewer.locator("output")).toContainText("1.20×");
  await viewer
    .getByRole("button", { name: "Rotate right", exact: true })
    .click();
  await expect(viewer.locator("output")).toContainText("15°");
  await viewer.getByRole("button", { name: "Reset view", exact: true }).click();
  await expect(viewer.locator("output")).toHaveText("1.00× · 0°");
});

test("matrix, viewer, history and shared URL follow the same selection", async ({
  page,
}) => {
  await page.goto("./?n=11");
  await expect(
    page.getByRole("heading", { name: "11 unit squares", exact: true }),
  ).toBeVisible();
  await expect(
    page.getByRole("heading", { name: "The record for n = 11", exact: true }),
  ).toBeVisible();
  await page
    .locator("#matrix")
    .getByRole("button", { name: /^n = 69:/ })
    .click();
  await expect(page).toHaveURL(/n=69/);
  await expect(
    page.getByRole("heading", { name: "69 unit squares", exact: true }),
  ).toBeVisible();
  await expect(
    page.getByRole("heading", { name: "The record for n = 69", exact: true }),
  ).toBeVisible();
  await page.goBack();
  await expect(
    page.getByRole("heading", { name: "11 unit squares", exact: true }),
  ).toBeVisible();
  await page.reload();
  await expect(
    page.getByRole("heading", { name: "11 unit squares", exact: true }),
  ).toBeVisible();
  await page
    .locator("#matrix")
    .getByRole("button", { name: /^n = 61:/ })
    .click();
  await expect(
    page.getByRole("heading", { name: "61 unit squares" }),
  ).toBeVisible();
  await expect(page.locator("#viewer")).toContainText("Basic grid bound");
  await expect(page.locator("#viewer")).toContainText("s(61) ≤ 8");
  await expect(page.locator("#viewer")).not.toContainText("Lean verified");
  await expect(
    page.locator("#viewer").getByRole("link", { name: "Lean proof" }),
  ).toHaveAttribute("href", /Records\/GridBounds\.lean$/);
  await expect(
    page.locator("#matrix").getByRole("button", {
      name: "n = 61: Upper bound · s(61) ≤ 8 · Basic grid bound",
      exact: true,
    }),
  ).toHaveAttribute("aria-pressed", "true");
  await expect(page.locator("#history")).toContainText(
    "No results catalogued for this n yet.",
  );
  await expect(page.locator("#viewer [data-square-id]")).toHaveCount(61);
});

test("the catalog searches formalized results without an evidence filter", async ({
  page,
}) => {
  await page.goto("./#claims");
  const catalog = page.locator("#claims");
  await expect(catalog.getByRole("combobox")).toHaveCount(0);
  await expect(catalog.locator("tbody tr")).toHaveCount(claims.length);
  for (const row of await catalog.locator("tbody tr").all()) {
    await expect(row.getByRole("link", { name: "Lean proof" })).not.toHaveCount(
      0,
    );
  }
  await catalog.getByRole("searchbox").fill("Nagamochi");
  const nagamochiClaims = claims.filter((claim) =>
    claim.contributors.some(
      (contributor) => contributor.author === "nagamochi",
    ),
  );
  await expect(catalog.locator("tbody th")).toHaveText(
    [...nagamochiClaims]
      .sort((left, right) => left.n - right.n)
      .map((claim) => String(claim.n)),
  );
  await catalog.getByRole("searchbox").fill("no-such-archive-claim");
  await expect(
    catalog.getByText("No matching claims. Try another search."),
  ).toBeVisible();
  await catalog.getByRole("searchbox").fill("68");
  await expect(catalog.locator("tbody tr")).toHaveCount(1);
  await expect(catalog.locator("tbody tr")).toContainText("s(68) ≤ 8.80339");
});

test("keyboard inspection, orientation groups and coordinate downloads work", async ({
  page,
}) => {
  await page.goto("./?n=11");
  const viewer = page.locator("#viewer");
  const square = viewer.getByRole("button", { name: "Square 0", exact: true });
  await square.focus();
  await page.keyboard.press("Enter");
  await expect(
    viewer.getByRole("heading", { name: /^Square 0\b/ }),
  ).toBeVisible();
  await viewer.getByLabel("Inspect square", { exact: true }).selectOption("1");
  await expect(
    viewer.getByRole("heading", { name: /^Square 1\b/ }),
  ).toBeVisible();
  const group = viewer.getByRole("button", { name: /^0.0°/ });
  const originalCount = await viewer.locator("[data-square-id]").count();
  await group.click();
  expect(await viewer.locator("[data-square-id]").count()).toBeLessThan(
    originalCount,
  );
  await expect(group).toHaveAttribute("aria-pressed", "false");
  await group.click();
  await expect(viewer.locator("[data-square-id]")).toHaveCount(originalCount);
  const downloaded = page.waitForEvent("download");
  await viewer.getByRole("button", { name: "Download coordinates" }).click();
  expect((await downloaded).suggestedFilename()).toBe(
    "square-11-trump-rationalized.json",
  );
});

test("mobile selection and controls remain reachable", async ({ page }) => {
  await page.setViewportSize({ width: 390, height: 844 });
  await page.goto("./?n=69");
  const matrix = page.locator("#matrix");
  await expect(matrix.getByRole("button")).toHaveCount(100);
  await expect(matrix.getByRole("combobox")).toHaveCount(0);
  await expect(matrix.getByRole("button", { name: /^n = 13:/ })).toHaveClass(
    /bg-forest-soft/,
  );
  await expect(
    matrix.getByRole("button", { name: /^n = 11:/ }),
  ).not.toHaveClass(/bg-forest-soft/);
  await matrix.getByRole("button", { name: /^n = 11:/ }).click();
  await expect(
    page.getByRole("heading", { name: "11 unit squares", exact: true }),
  ).toBeVisible();
  await page
    .locator("#viewer")
    .getByRole("button", { name: "Zoom in", exact: true })
    .click();
  await expect(page.locator("#viewer output")).toContainText("1.20×");
  expect(
    await page.evaluate(
      () => document.documentElement.scrollWidth <= window.innerWidth,
    ),
  ).toBe(true);
});
