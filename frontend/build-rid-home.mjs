import { build } from "esbuild";
import { mkdir } from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const rootDir = path.resolve(__dirname, "..");
const outDir = path.join(rootDir, "station_edition", "light_rid", "assets", "vue");

await mkdir(outDir, { recursive: true });

for (const entry of ["rid-home", "nodes-center", "viewer-settings", "station-settings"]) {
  await build({
    absWorkingDir: __dirname,
    entryPoints: [path.join(__dirname, "src", `${entry}.js`)],
    bundle: true,
    format: "iife",
    platform: "browser",
    target: ["es2020"],
    define: {
      __VUE_OPTIONS_API__: "false",
      __VUE_PROD_DEVTOOLS__: "false",
      __VUE_PROD_HYDRATION_MISMATCH_DETAILS__: "false",
    },
    outfile: path.join(outDir, `${entry}.js`),
    sourcemap: false,
    minify: false,
    legalComments: "none",
    charset: "utf8",
    logLevel: "info",
  });
}
