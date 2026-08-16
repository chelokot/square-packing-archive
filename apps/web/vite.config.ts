import tailwindcss from "@tailwindcss/vite";
import react from "@vitejs/plugin-react";
import { defineConfig } from "vite";

export default defineConfig({
  base: "/square-packing-archive/",
  plugins: [react(), tailwindcss()],
});
