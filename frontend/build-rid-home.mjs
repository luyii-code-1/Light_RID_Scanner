import { build } from "esbuild";
import { mkdir } from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const rootDir = path.resolve(__dirname, "..");
const outDir = path.join(rootDir, "station_edition", "light_rid", "assets", "vue");

await mkdir(outDir, { recursive: true });

await build({
  entryPoints: [path.join(__dirname, "src", "rid-home.js")],
  bundle: true,
  format: "iife",
  platform: "browser",
  target: ["es2020"],
  outfile: path.join(outDir, "rid-home.js"),
  sourcemap: false,
  minify: false,
  legalComments: "none",
  charset: "utf8",
  logLevel: "info",
});
