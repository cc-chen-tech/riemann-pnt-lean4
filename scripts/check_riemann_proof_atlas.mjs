import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

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
const SCRIPT_DIRECTORY = path.dirname(fileURLToPath(import.meta.url));
const REPOSITORY_ROOT = path.resolve(SCRIPT_DIRECTORY, "..");
const CANONICAL_SOURCE = path.join(REPOSITORY_ROOT, "docs", "assets", "riemann-proof-atlas.html");
const DEPLOYED_ARTIFACT = "/Users/luicy/.codex/visualizations/2026/05/23/019e55d5-94a4-7802-b7f0-8df5066f27b1/riemann-proof-atlas.html";

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

function attributeValue(tagSource, attribute) {
  const match = new RegExp(`\\b${attribute}\\s*=\\s*(["'])(.*?)\\1`, "i").exec(tagSource);
  return match?.[2] ?? null;
}

function elementContentById(source, id) {
  const openingTag = /<([A-Za-z][\w:-]*)\b[^>]*>/g;
  let match;

  while ((match = openingTag.exec(source))) {
    const [tagSource, tagName] = match;
    if (attributeValue(tagSource, "id") !== id) continue;

    const nestedTag = new RegExp(`<\\/?${tagName}\\b[^>]*>`, "gi");
    nestedTag.lastIndex = openingTag.lastIndex;
    let depth = 1;
    let nested;
    while ((nested = nestedTag.exec(source))) {
      if (nested[0].startsWith("</")) {
        depth -= 1;
        if (depth === 0) return source.slice(openingTag.lastIndex, nested.index);
      } else if (!nested[0].endsWith("/>")) {
        depth += 1;
      }
    }
    return null;
  }

  return null;
}

function staticMapNodeCount(source) {
  // Ignore executable/style text so only no-JS HTML fallback nodes count.
  const markup = source.replace(/<(script|style)\b[^>]*>[\s\S]*?<\/\1\s*>/gi, " ");
  const mapContent = elementContentById(markup, "atlas-map");
  if (mapContent === null) return 0;

  let count = 0;
  for (const match of mapContent.matchAll(/<button\b[^>]*>/gi)) {
    const classNames = attributeValue(match[0], "class")?.split(/\s+/) ?? [];
    const conceptId = attributeValue(match[0], "data-concept-id");
    if (classNames.includes("map-node") && conceptId?.trim()) count += 1;
  }
  return count;
}

function hasNonemptyArray(property) {
  const value = property?.value.trimStart() ?? "";
  if (!value.startsWith("[")) return false;
  const end = findMatching(value, 0, "[", "]");
  return end > 1 && value.slice(1, end).trim().length > 0;
}

function isHashAnchorExpression(expression) {
  return /^\s*(["'])#.*\1\s*$/.test(expression);
}

function hasVisibleFocusRule(source, selectorPattern) {
  for (const match of source.matchAll(/([^{}]+)\{([^{}]*)\}/gis)) {
    if (!/\boutline\s*:/i.test(match[2])) continue;
    for (const selector of match[1].split(",")) {
      if (/:focus-visible\b/i.test(selector) && selectorPattern.test(selector)) return true;
    }
  }
  return false;
}

function runtimeResourceErrors(source) {
  const errors = [];
  const forbiddenCalls = [
    ["Worker", /\b(?:new\s+)?(?:window\s*\.\s*)?Worker\s*\(/i],
    ["SharedWorker", /\b(?:new\s+)?(?:window\s*\.\s*)?SharedWorker\s*\(/i],
    ["serviceWorker.register", /\b(?:navigator\s*\.\s*)?serviceWorker\s*\.\s*register\s*\(/i],
    ["importScripts", /\bimportScripts\s*\(/i],
    ["navigator.sendBeacon", /\bnavigator\s*\.\s*sendBeacon\s*\(/i],
    ["fetch", /\b(?:window\s*\.\s*)?fetch\s*\(/i],
    ["XMLHttpRequest", /\b(?:new\s+)?(?:window\s*\.\s*)?XMLHttpRequest\s*\(/i],
    ["XMLHttpRequest.open", /\.\s*open\s*\(\s*["'](?:GET|POST|PUT|PATCH|DELETE|HEAD|OPTIONS)["']\s*,/i],
    ["WebSocket", /\bnew\s+(?:window\s*\.\s*)?WebSocket\s*\(/i],
    ["EventSource", /\bnew\s+(?:window\s*\.\s*)?EventSource\s*\(/i],
    ["dynamic import", /\bimport\s*\(/i],
    ["new URL", /\bnew\s+(?:window\s*\.\s*)?URL\s*\(/i],
    ["URL.createObjectURL", /\b(?:window\s*\.\s*)?URL\s*\.\s*createObjectURL\s*\(/i],
    ["constructed resource element", /\b(?:document|window|globalThis)\s*\.\s*createElement\s*\(\s*["'](?:script|link|img|iframe|embed|object|audio|video|source|track)["']/i],
    ["constructed resource element", /\b(?:document|window|globalThis)\s*\.\s*createElementNS\s*\([^,]+,\s*["'](?:script|image|foreignObject)["']/i],
    ["constructed Image", /\bnew\s+(?:window\s*\.\s*)?Image\s*\(/i],
    ["constructed Audio", /\bnew\s+(?:window\s*\.\s*)?Audio\s*\(/i]
  ];
  for (const [label, pattern] of forbiddenCalls) {
    if (pattern.test(source)) errors.push(`runtime resource: ${label}`);
  }

  for (const match of source.matchAll(/\.\s*(?:src|href)\s*=\s*([^;\n]+)/gi)) {
    if (!isHashAnchorExpression(match[1])) errors.push("runtime resource: dynamic src/href assignment");
  }
  for (const match of source.matchAll(/\[\s*(["'])(?:src|href)\1\s*\]\s*=\s*([^;\n]+)/gi)) {
    if (!isHashAnchorExpression(match[2])) errors.push("runtime resource: dynamic src/href assignment");
  }
  for (const match of source.matchAll(/\.\s*setAttribute\s*\(\s*(["'])(?:src|href)\1\s*,\s*([^)]*)\)/gi)) {
    if (!isHashAnchorExpression(match[2])) errors.push("runtime resource: dynamic src/href assignment");
  }

  return errors;
}

const resolvedTarget = path.resolve(target);
const html = fs.readFileSync(resolvedTarget, "utf8");
const source = stripComments(html);
const errors = [];

for (const [label, pattern] of [
  ["<!doctype html>", /<!doctype\s+html\s*>/i],
  ["<html lang=\"zh-CN\">", /<html\b[^>]*\blang\s*=\s*(["'])zh-CN\1/i],
  ["id=\"atlas-map\"", /\bid\s*=\s*(["'])atlas-map\1/i],
  ["id=\"concept-view\"", /\bid\s*=\s*(["'])concept-view\1/i],
  ["prefers-reduced-motion", /@media\s*\(\s*prefers-reduced-motion\s*:\s*reduce\s*\)/i],
  ["@media (max-width: 720px)", /@media\s*\(\s*max-width\s*:\s*720px\s*\)/i],
  ["@media (max-width: 360px)", /@media\s*\(\s*max-width\s*:\s*360px\s*\)/i],
  ["hash routing", /\brouteFromHash\s*\(/],
  ["hashchange listener", /\bhashchange\b/],
  ["location.hash", /\blocation\.hash\b/],
  ["network expansion", /\bexpanded\b[\s\S]*\brenderMap\s*\(/],
  ["concept rendering", /\brenderConceptPage\s*\(/]
]) {
  if (!pattern.test(source)) errors.push(`missing: ${label}`);
}

if (!/<button\b[^>]*\bdata-action\s*=\s*(["'])toggle-network\1[^>]*>/i.test(source)) {
  errors.push("missing: button[data-action=\"toggle-network\"]");
}
if (!hasVisibleFocusRule(source, /(?:^|[\s>+~])(?:button|\.map-node)[^\s>+~]*:focus-visible\b/i)) {
  errors.push("missing: visible focus for button or map-node controls");
}
if (!hasVisibleFocusRule(source, /(?:^|[\s>+~])(?:button)?\[data-action\s*=\s*(["'])toggle-network\1\][^\s>+~]*:focus-visible\b/i)) {
  errors.push("missing: visible focus for network toggle");
}

const staticFallbackCount = staticMapNodeCount(source);
if (staticFallbackCount < 6) {
  errors.push(`expected at least six static #atlas-map fallback buttons, found ${staticFallbackCount}`);
}

if (/\b@import\b/i.test(source)) errors.push("external resource: @import");

if (/(?:https?:)?\/\//i.test(source)) errors.push("external resource: http(s) or protocol-relative literal");

errors.push(...runtimeResourceErrors(source));

for (const match of source.matchAll(/\burl\s*\(\s*(["']?)(.*?)\1\s*\)/gi)) {
  const prefix = source.slice(Math.max(0, match.index - 8), match.index);
  if (/new\s*$/i.test(prefix)) continue;
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
    if (properties.has("leanEvidence") && !hasNonemptyArray(properties.get("leanEvidence"))) {
      errors.push(`concept ${id} has empty leanEvidence array`);
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

if (resolvedTarget === CANONICAL_SOURCE) {
  if (!fs.existsSync(DEPLOYED_ARTIFACT)) {
    errors.push(`missing deployed artifact: ${DEPLOYED_ARTIFACT}`);
  } else if (!fs.readFileSync(resolvedTarget).equals(fs.readFileSync(DEPLOYED_ARTIFACT))) {
    errors.push(`deployed artifact differs from canonical source: ${DEPLOYED_ARTIFACT}`);
  }
}

if (errors.length) {
  console.error(errors.join("\n"));
  process.exit(1);
}

console.log("proof atlas contract: PASS");
