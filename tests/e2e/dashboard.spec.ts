import { expect, test } from "@playwright/test";

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
    .getByRole("button", { name: "n = 69", exact: true })
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
    .getByLabel("Number of squares", { exact: true })
    .selectOption("61");
  await expect(
    page.getByRole("heading", { name: "Coordinates not yet in the archive" }),
  ).toBeVisible();
  await expect(page.locator('#viewer svg[role="group"]')).toHaveCount(0);
});

test("catalog filters preserve the distinction between published and checked proofs", async ({
  page,
}) => {
  await page.goto("./#claims");
  const catalog = page.locator("#claims");
  await expect(
    catalog.locator("tbody").getByText("Published · awaiting Lean").first(),
  ).toBeVisible();
  await expect(
    catalog.locator("tbody").getByText("Lean verified").first(),
  ).toBeVisible();
  await catalog.getByRole("searchbox").fill("Nagamochi");
  await expect(catalog.locator("tbody tr").first()).toContainText("Nagamochi");
  await catalog.getByLabel("Filter by evidence").selectOption("lean-verified");
  await expect(
    catalog.getByText(
      "No matching claims. Try another search or evidence filter.",
    ),
  ).toBeVisible();
  await catalog.getByRole("searchbox").fill("68");
  await expect(catalog.locator("tbody tr")).toHaveCount(1);
  await expect(catalog.locator("tbody tr")).toContainText("Lean verified");
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
  await expect(
    page.getByLabel("Number of squares", { exact: true }),
  ).toBeVisible();
  await page
    .getByLabel("Number of squares", { exact: true })
    .selectOption("11");
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
