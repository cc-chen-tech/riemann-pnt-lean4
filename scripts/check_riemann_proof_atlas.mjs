import fs from "node:fs";
import path from "node:path";

const target = process.argv[2];
if (!target) {
  console.error("usage: node scripts/check_riemann_proof_atlas.mjs <html-path>");
  process.exit(2);
}

const html = fs.readFileSync(path.resolve(target), "utf8");
const required = [
  "<!doctype html>",
  "<html lang=\"zh-CN\">",
  "id=\"atlas-map\"",
  "id=\"concept-view\"",
  "data-action=\"toggle-network\"",
  "prefers-reduced-motion",
  "@media (max-width: 720px)",
  "location.hash",
  "status: \"proved\"",
  "status: \"route\"",
  "status: \"frontier\"",
  ...[
    "zeta", "zeta-tools", "three-four-one", "zero-free", "perron",
    "explicit-formula", "psi-error", "pnt", "pnt-error", "existing-pnt",
    "zero-density", "rh-error", "rh"
  ].map((id) => `id: \"${id}\"`)
];

const errors = required
  .filter((needle) => !html.toLowerCase().includes(needle.toLowerCase()))
  .map((needle) => `missing: ${needle}`);

for (const pattern of [/https?:\/\//i, /<script[^>]+src=/i, /<link[^>]+href=/i]) {
  if (pattern.test(html)) errors.push(`external resource: ${pattern}`);
}

for (const claim of ["本项目已经证明素数定理", "本项目已经证明黎曼猜想"]) {
  if (html.includes(claim)) errors.push(`prohibited claim: ${claim}`);
}

if (!/<button[^>]+class="[^"]*map-node/i.test(html)) {
  errors.push("map nodes are not semantic buttons");
}

if (errors.length) {
  console.error(errors.join("\n"));
  process.exit(1);
}

console.log("proof atlas contract: PASS");
