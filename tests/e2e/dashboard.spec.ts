import { expect, test } from "@playwright/test";

test("renders the archive and inspects an exact square", async ({ page }) => {
  await page.goto("/");
  await expect(
    page.getByRole("heading", { name: /Every packing/ }),
  ).toBeVisible();
  await expect(page.getByText("Lean-verified claims")).toBeVisible();
  await page.locator("#viewer svg rect.cursor-pointer").first().click();
  await expect(page.getByText("Exact t = tan(θ/2)")).toBeVisible();
  await expect(page.getByText("Square 0", { exact: true })).toBeVisible();
});

test("keeps published proofs visibly separate from Lean verification", async ({
  page,
}) => {
  await page.goto("/#claims");
  await expect(
    page.getByText("Published · awaiting Lean").first(),
  ).toBeVisible();
  await expect(page.getByText("Lean verified").first()).toBeVisible();
});
