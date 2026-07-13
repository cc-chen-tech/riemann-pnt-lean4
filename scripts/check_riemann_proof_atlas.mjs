import fs from "node:fs";
import path from "node:path";

const target = process.argv[2];
if (!target) {
  console.error("usage: node scripts/check_riemann_proof_atlas.mjs <html-path>");
  process.exit(2);
}

const REQUIRED_STATUS_BY_ID = Object.freeze({
  zeta: "proved",
  "zeta-tools": "proved",
  "three-four-one": "proved",
  "zero-free": "proved",
  perron: "route",
  "explicit-formula": "route",
  "psi-error": "route",
  pnt: "route",
  "pnt-error": "frontier",
  "existing-pnt": "frontier",
  "zero-density": "frontier",
  "rh-error": "frontier",
  rh: "frontier"
});

const REQUIRED_CONTENT_FIELDS = [
  "id",
  "title",
  "english",
  "status",
  "core",
  "summary",
  "formula",
  "intuition",
  "leanEvidence",
  "impact",
  "warning",
  "dependsOn",
  "compact",
  "expanded"
];

const ALLOWED_STATUSES = new Set(["proved", "route", "frontier"]);

function stripDelimitedComments(source, removeLineComments) {
  let result = "";
  let quote = null;

  for (let index = 0; index < source.length; index += 1) {
    const character = source[index];
    const next = source[index + 1];

    if (quote) {
      result += character;
      if (character === "\\") {
        result += next ?? "";
        index += 1;
      } else if (character === quote) {
        quote = null;
      }
      continue;
    }

    if (character === "\"" || character === "'" || character === "`") {
      quote = character;
      result += character;
      continue;
    }

    if (character === "/" && next === "*") {
      const end = source.indexOf("*/", index + 2);
      index = end === -1 ? source.length : end + 1;
      result += " ";
      continue;
    }

    if (removeLineComments && character === "/" && next === "/") {
      const end = source.indexOf("\n", index + 2);
      index = end === -1 ? source.length : end - 1;
      result += "\n";
      continue;
    }

    result += character;
  }

  return result;
}

function stripComments(source) {
  const withoutHtmlComments = source.replace(/<!--[\s\S]*?-->/g, " ");
  return withoutHtmlComments.replace(
    /<(script|style)\b[^>]*>([\s\S]*?)<\/\1\s*>/gi,
    (match, tag, body) => {
      const cleanBody = stripDelimitedComments(body, tag.toLowerCase() === "script");
      return match.replace(body, cleanBody);
    }
  );
}

function findMatching(source, start, open, close) {
  let depth = 0;
  let quote = null;

  for (let index = start; index < source.length; index += 1) {
    const character = source[index];

    if (quote) {
      if (character === "\\") {
        index += 1;
      } else if (character === quote) {
        quote = null;
      }
      continue;
    }

    if (character === "\"" || character === "'" || character === "`") {
      quote = character;
    } else if (character === open) {
      depth += 1;
    } else if (character === close) {
      depth -= 1;
      if (depth === 0) return index;
    }
  }

  return -1;
}

function extractConceptObjects(source) {
  const declaration = /\b(?:const|let|var)\s+CONCEPTS\s*=\s*(?:Object\.freeze\s*\(\s*)?\[/m.exec(source);
  if (!declaration) return null;

  const arrayStart = source.indexOf("[", declaration.index);
  const arrayEnd = findMatching(source, arrayStart, "[", "]");
  if (arrayEnd === -1) return null;

  const objects = [];
  let depth = 0;
  let quote = null;
  let objectStart = -1;

  for (let index = arrayStart + 1; index < arrayEnd; index += 1) {
    const character = source[index];

    if (quote) {
      if (character === "\\") {
        index += 1;
      } else if (character === quote) {
        quote = null;
      }
      continue;
    }

    if (character === "\"" || character === "'" || character === "`") {
      quote = character;
      continue;
    }

    if (character === "{") {
      if (depth === 0) objectStart = index;
      depth += 1;
    } else if (character === "}") {
      depth -= 1;
      if (depth === 0 && objectStart !== -1) {
        objects.push(source.slice(objectStart, index + 1));
        objectStart = -1;
      }
    }
  }

  return objects;
}

function topLevelProperties(objectSource) {
  const properties = new Map();
  let depth = 0;
  let quote = null;

  for (let index = 0; index < objectSource.length; index += 1) {
    const character = objectSource[index];

    if (quote) {
      if (character === "\\") {
        index += 1;
      } else if (character === quote) {
        quote = null;
      }
      continue;
    }

    if (character === "\"" || character === "'" || character === "`") {
      quote = character;
      continue;
    }

    if (character === "{") {
      depth += 1;
      continue;
    }
    if (character === "}") {
      depth -= 1;
      continue;
    }

    if (depth !== 1 || (index !== 1 && objectSource[index - 1] !== ",")) continue;
    const property = /^\s*([A-Za-z_$][\w$]*)\s*:\s*/.exec(objectSource.slice(index));
    if (!property) continue;

    properties.set(property[1], {
      valueStart: index + property[0].length,
      value: objectSource.slice(index + property[0].length)
    });
  }

  return properties;
}

function stringValue(property) {
  const match = /^(["'])(.*?)\1/s.exec(property?.value.trimStart() ?? "");
  return match?.[2] ?? null;
}

function hasNonemptyString(property) {
  return Boolean(stringValue(property)?.trim());
}

function attributeMatches(source, tag, attribute, allowHashAnchor = false) {
  const matches = source.matchAll(new RegExp(`<${tag}\\b[^>]*\\b${attribute}\\s*=\\s*(["'])(.*?)\\1`, "gi"));
  return [...matches].filter((match) => !(allowHashAnchor && match[2].trim().startsWith("#")));
}

const html = fs.readFileSync(path.resolve(target), "utf8");
const source = stripComments(html);
const errors = [];

for (const [label, pattern] of [
  ["<!doctype html>", /<!doctype\s+html\s*>/i],
  ["<html lang=\"zh-CN\">", /<html\b[^>]*\blang\s*=\s*(["'])zh-CN\1/i],
  ["id=\"atlas-map\"", /\bid\s*=\s*(["'])atlas-map\1/i],
  ["id=\"concept-view\"", /\bid\s*=\s*(["'])concept-view\1/i],
  ["data-action=\"toggle-network\"", /\bdata-action\s*=\s*(["'])toggle-network\1/i],
  ["prefers-reduced-motion", /@media\s*\(\s*prefers-reduced-motion\s*:\s*reduce\s*\)/i],
  ["@media (max-width: 720px)", /@media\s*\(\s*max-width\s*:\s*720px\s*\)/i],
  ["visible focus", /:focus-visible\s*\{[^}]*\boutline\s*:/is],
  ["hash routing", /\brouteFromHash\s*\(/],
  ["hashchange listener", /\bhashchange\b/],
  ["location.hash", /\blocation\.hash\b/],
  ["network expansion", /\bexpanded\b[\s\S]*\brenderMap\s*\(/],
  ["concept rendering", /\brenderConceptPage\s*\(/]
]) {
  if (!pattern.test(source)) errors.push(`missing: ${label}`);
}

const staticMapButton = /<button\b[^>]*\bclass\s*=\s*(["'])[^"']*\bmap-node\b[^"']*\1[^>]*>/i.test(source);
const dynamicMapButton = /document\.createElement\s*\(\s*(["'])button\1\s*\)/.test(source) &&
  (/(?:\.classList\.add\s*\(\s*["']map-node["']\s*\))|(?:\.className\s*=\s*["'][^"']*\bmap-node\b)/.test(source)) &&
  (/(?:\.dataset\.conceptId\s*=)|(?:\.setAttribute\s*\(\s*["']data-concept-id["'])/.test(source));
if (!staticMapButton && !dynamicMapButton) {
  errors.push("map nodes are not real semantic button markup or executable creation code");
}

if (/\b@import\b/i.test(source)) errors.push("external resource: @import");

for (const match of source.matchAll(/\burl\s*\(\s*(["']?)(.*?)\1\s*\)/gi)) {
  const resource = match[2].trim();
  if (resource && !resource.startsWith("#")) errors.push(`external resource: CSS url(${resource})`);
}

for (const match of source.matchAll(/\b(?:src|href|poster|data)\s*=\s*(["'])\s*(\/\/[^"']*)\1/gi)) {
  errors.push(`external resource: protocol-relative ${match[2]}`);
}

for (const match of attributeMatches(source, "script", "src")) {
  errors.push(`external resource: script src=${match[2]}`);
}
for (const match of attributeMatches(source, "link", "href", true)) {
  errors.push(`external resource: link href=${match[2]}`);
}
for (const tag of ["img", "embed", "object", "iframe", "audio", "video", "source", "track"]) {
  for (const attribute of ["src", "href", "data", "poster"]) {
    for (const match of attributeMatches(source, tag, attribute, true)) {
      errors.push(`external resource: <${tag}> ${attribute}=${match[2]}`);
    }
  }
}

const conceptObjects = extractConceptObjects(source);
if (!conceptObjects) {
  errors.push("missing: CONCEPTS array");
} else {
  const concepts = conceptObjects.map((objectSource) => ({
    objectSource,
    properties: topLevelProperties(objectSource)
  }));
  const coreCount = concepts.filter(({ properties }) => /^true\b/.test(properties.get("core")?.value.trimStart() ?? "")).length;
  if (coreCount !== 6) errors.push(`expected exactly six core:true concept objects, found ${coreCount}`);

  for (const { properties } of concepts) {
    const status = stringValue(properties.get("status"));
    if (status && !ALLOWED_STATUSES.has(status)) errors.push(`unknown status: ${status}`);
  }

  for (const [id, expectedStatus] of Object.entries(REQUIRED_STATUS_BY_ID)) {
    const matches = concepts.filter(({ properties }) => stringValue(properties.get("id")) === id);
    if (matches.length !== 1) {
      errors.push(`expected exactly one concept object for ${id}, found ${matches.length}`);
      continue;
    }

    const { properties } = matches[0];
    for (const field of REQUIRED_CONTENT_FIELDS) {
      if (!properties.has(field)) errors.push(`concept ${id} missing field: ${field}`);
    }
    for (const field of ["title", "english", "summary", "formula", "intuition", "impact", "warning"]) {
      if (properties.has(field) && !hasNonemptyString(properties.get(field))) {
        errors.push(`concept ${id} has empty field: ${field}`);
      }
    }

    const status = stringValue(properties.get("status"));
    if (!ALLOWED_STATUSES.has(status)) {
      errors.push(`concept ${id} has invalid status: ${status ?? "missing"}`);
    } else if (status !== expectedStatus) {
      errors.push(`concept ${id} must use status ${expectedStatus}, found ${status}`);
    }
    if (id === "pnt" && status === "proved") errors.push("concept pnt must not use status proved");
    if (id === "rh" && status === "proved") errors.push("concept rh must not use status proved");
  }
}

for (const claim of ["本项目已经证明素数定理", "本项目已经证明黎曼猜想"]) {
  if (source.includes(claim)) errors.push(`prohibited claim: ${claim}`);
}

if (errors.length) {
  console.error(errors.join("\n"));
  process.exit(1);
}

console.log("proof atlas contract: PASS");
