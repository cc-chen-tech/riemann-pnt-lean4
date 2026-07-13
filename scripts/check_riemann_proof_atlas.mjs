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

function extractTagBodies(source, tag) {
  const bodies = [];
  const pattern = new RegExp(`<${tag}\\b[^>]*>([\\s\\S]*?)<\\/${tag}\\s*>`, "gi");
  for (const match of source.matchAll(pattern)) bodies.push(match[1]);
  return bodies;
}

function maskJavaScriptStrings(source) {
  let result = "";
  let quote = null;

  for (let index = 0; index < source.length; index += 1) {
    const character = source[index];
    if (quote) {
      if (character === "\\") {
        result += " ";
        if (source[index + 1] !== undefined) {
          result += source[index + 1] === "\n" ? "\n" : " ";
          index += 1;
        }
      } else if (character === quote) {
        result += quote === "`" ? " " : character;
        quote = null;
      } else {
        result += character === "\n" ? "\n" : " ";
      }
      continue;
    }

    if (character === "\"" || character === "'") {
      quote = character;
      result += character;
    } else if (character === "`") {
      quote = character;
      result += " ";
    } else {
      result += character;
    }
  }

  return result;
}

function markupWithoutExecutableBodies(source) {
  return source.replace(/<(script|style)\b([^>]*)>[\s\S]*?<\/\1\s*>/gi, "<$1$2></$1>");
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
  const code = maskJavaScriptStrings(source);
  const declaration = /\b(?:const|let|var)\s+CONCEPTS\s*=\s*(?:Object\.freeze\s*\(\s*)?\[/m.exec(code);
  if (!declaration) return null;

  const arrayStart = code.indexOf("[", declaration.index);
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
  const tagPattern = new RegExp(`<${tag}\\b[^>]*>`, "gi");
  const attributePattern = new RegExp(
    `\\b${attribute}\\s*=\\s*(?:"([^"]*)"|'([^']*)'|([^\\s"'=<>\\x60]+))`,
    "i"
  );
  const matches = [];
  for (const tagMatch of source.matchAll(tagPattern)) {
    const attributeMatch = attributePattern.exec(tagMatch[0]);
    if (!attributeMatch) continue;
    const value = attributeMatch[1] ?? attributeMatch[2] ?? attributeMatch[3] ?? "";
    if (!(allowHashAnchor && value.trim().startsWith("#"))) {
      matches.push({ tag: tagMatch[0], value });
    }
  }
  return matches;
}

function attributeValue(tagSource, attribute) {
  const match = new RegExp(
    `\\b${attribute}\\s*=\\s*(?:"([^"]*)"|'([^']*)'|([^\\s"'=<>\\x60]+))`,
    "i"
  ).exec(tagSource);
  return match?.[1] ?? match?.[2] ?? match?.[3] ?? null;
}

function inlineEventHandlerBodies(source) {
  const handlers = [];
  for (const tagMatch of source.matchAll(/<[A-Za-z][\w:-]*\b[^>]*>/g)) {
    const eventAttribute = /(?:^|\s)on[a-z][\w:-]*\s*=\s*(?:"([^"]*)"|'([^']*)'|([^\s"'=<>\x60]+))/gi;
    for (const attributeMatch of tagMatch[0].matchAll(eventAttribute)) {
      handlers.push(attributeMatch[1] ?? attributeMatch[2] ?? attributeMatch[3] ?? "");
    }
  }
  return handlers;
}

function resourceBearingAttributeMatches(source) {
  const matches = [];
  for (const tagMatch of source.matchAll(/<([A-Za-z][\w:-]*)\b[^>]*>/g)) {
    const [, tagName] = tagMatch;
    const resourceAttribute = /(?:^|\s)(src|href|data|poster|action|formaction)\s*=\s*(?:"([^"]*)"|'([^']*)'|([^\s"'=<>\x60]+))/gi;
    for (const attributeMatch of tagMatch[0].matchAll(resourceAttribute)) {
      const attribute = attributeMatch[1].toLowerCase();
      const value = attributeMatch[2] ?? attributeMatch[3] ?? attributeMatch[4] ?? "";
      const isInternalHashAnchor = tagName.toLowerCase() === "a" && attribute === "href" && /^#[^\s]*$/.test(value.trim());
      if (!isInternalHashAnchor) matches.push({ tag: tagName, attribute, value });
    }
  }
  return matches;
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
  const mapContent = elementContentById(source, "atlas-map");
  if (mapContent === null) return 0;

  let count = 0;
  for (const match of mapContent.matchAll(/<button\b[^>]*>/gi)) {
    const classNames = attributeValue(match[0], "class")?.split(/\s+/) ?? [];
    const conceptId = attributeValue(match[0], "data-concept-id");
    if (classNames.includes("map-node") && conceptId?.trim()) count += 1;
  }
  return count;
}

function staticMapNodeConceptIds(source) {
  const mapContent = elementContentById(source, "atlas-map");
  if (mapContent === null) return [];

  const conceptIds = new Set();
  for (const match of mapContent.matchAll(/<button\b[^>]*>/gi)) {
    const classNames = attributeValue(match[0], "class")?.split(/\s+/) ?? [];
    const conceptId = attributeValue(match[0], "data-concept-id")?.trim();
    if (classNames.includes("map-node") && conceptId) conceptIds.add(conceptId);
  }
  return [...conceptIds];
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

function hasVisibleFocusRule(styleBodies, selectorPattern) {
  for (const styleBody of styleBodies) {
    for (const match of styleBody.matchAll(/([^{}]+)\{([^{}]*)\}/gis)) {
      if (!hasVisibleOutline(match[2])) continue;
      for (const selector of match[1].split(",")) {
        if (/:focus-visible\b/i.test(selector) && selectorPattern.test(selector)) return true;
      }
    }
  }
  return false;
}

function hasVisibleOutline(declarations) {
  const shorthand = /(?:^|;)\s*outline\s*:\s*([^;]+)/i.exec(declarations)?.[1] ?? "";
  const width = /(?:^|;)\s*outline-width\s*:\s*([^;]+)/i.exec(declarations)?.[1] ?? shorthand;
  const style = /(?:^|;)\s*outline-style\s*:\s*([^;]+)/i.exec(declarations)?.[1] ?? shorthand;
  const color = /(?:^|;)\s*outline-color\s*:\s*([^;]+)/i.exec(declarations)?.[1] ?? "";
  const colorValues = [shorthand, color].filter(Boolean).join(" ");
  const outlineValues = `${shorthand} ${width} ${style} ${color}`;
  if (
    !hasLiteralOutlineColor(colorValues) ||
    /\bnone\b|\btransparent\b/i.test(outlineValues) ||
    hasAlphaZeroColor(outlineValues)
  ) return false;
  if (!hasNonzeroOutlineWidth(width)) return false;
  return /\b(?:solid|dashed|double)\b/i.test(style);
}

const CSS_LITERAL_COLOR_FUNCTIONS = /\b(?:rgb|rgba|hsl|hsla|hwb|lab|lch|oklab|oklch|color)\([^)]*\)/i;
const CSS_NAMED_COLORS = new Set([
  "aliceblue", "antiquewhite", "aqua", "aquamarine", "azure", "beige", "bisque", "black",
  "blanchedalmond", "blue", "blueviolet", "brown", "burlywood", "cadetblue", "chartreuse",
  "chocolate", "coral", "cornflowerblue", "cornsilk", "crimson", "cyan", "darkblue",
  "darkcyan", "darkgoldenrod", "darkgray", "darkgreen", "darkgrey", "darkkhaki", "darkmagenta",
  "darkolivegreen", "darkorange", "darkorchid", "darkred", "darksalmon", "darkseagreen",
  "darkslateblue", "darkslategray", "darkslategrey", "darkturquoise", "darkviolet", "deeppink",
  "deepskyblue", "dimgray", "dimgrey", "dodgerblue", "firebrick", "floralwhite", "forestgreen",
  "fuchsia", "gainsboro", "ghostwhite", "gold", "goldenrod", "gray", "green", "greenyellow",
  "grey", "honeydew", "hotpink", "indianred", "indigo", "ivory", "khaki", "lavender",
  "lavenderblush", "lawngreen", "lemonchiffon", "lightblue", "lightcoral", "lightcyan",
  "lightgoldenrodyellow", "lightgray", "lightgreen", "lightgrey", "lightpink", "lightsalmon",
  "lightseagreen", "lightskyblue", "lightslategray", "lightslategrey", "lightsteelblue",
  "lightyellow", "lime", "limegreen", "linen", "magenta", "maroon", "mediumaquamarine",
  "mediumblue", "mediumorchid", "mediumpurple", "mediumseagreen", "mediumslateblue",
  "mediumspringgreen", "mediumturquoise", "mediumvioletred", "midnightblue", "mintcream",
  "mistyrose", "moccasin", "navajowhite", "navy", "oldlace", "olive", "olivedrab", "orange",
  "orangered", "orchid", "palegoldenrod", "palegreen", "paleturquoise", "palevioletred",
  "papayawhip", "peachpuff", "peru", "pink", "plum", "powderblue", "purple", "rebeccapurple",
  "red", "rosybrown", "royalblue", "saddlebrown", "salmon", "sandybrown", "seagreen", "seashell",
  "sienna", "silver", "skyblue", "slateblue", "slategray", "slategrey", "snow", "springgreen",
  "steelblue", "tan", "teal", "thistle", "tomato", "turquoise", "violet", "wheat", "white",
  "whitesmoke", "yellow", "yellowgreen"
]);

function hasLiteralOutlineColor(value) {
  if (
    !value ||
    /\b(?:var|env|attr|calc|color-mix)\s*\(/i.test(value) ||
    /\b(?:currentcolor|inherit|initial|unset|revert(?:-layer)?)\b/i.test(value)
  ) return false;
  if (/#(?:[0-9a-f]{3,4}|[0-9a-f]{6}(?:[0-9a-f]{2})?)\b/i.test(value)) return true;
  if (CSS_LITERAL_COLOR_FUNCTIONS.test(value)) return true;
  return [...value.matchAll(/\b[a-z]+\b/gi)].some(([token]) => CSS_NAMED_COLORS.has(token.toLowerCase()));
}

function hasNonzeroOutlineWidth(value) {
  return (
    /\b(?:thin|medium|thick)\b/i.test(value) ||
    /(?:^|\s)(?:0*\.\d*[1-9]\d*|0*[1-9]\d*(?:\.\d+)?)(?:[a-z%]+)\b/i.test(value)
  );
}

function hasAlphaZeroColor(value) {
  if (/#(?:[0-9a-f]{3}0|[0-9a-f]{6}00)\b/i.test(value)) return true;
  for (const match of value.matchAll(/\b(?:rgba?|hsla?|hwb|lab|lch|oklab|oklch|color)\(([^)]*)\)/gi)) {
    const components = match[1].trim();
    const alpha = components.includes("/")
      ? components.slice(components.lastIndexOf("/") + 1).trim()
      : components.split(",").length === 4
        ? components.split(",").at(-1).trim()
        : null;
    if (alpha && /^(?:0+(?:\.0+)?|\.0+)%?$/.test(alpha)) return true;
  }
  return false;
}

function normalizeStaticStringConcatenations(source) {
  let normalized = source;
  for (let pass = 0; pass < 4; pass += 1) {
    const next = normalized.replace(
      /(["'`])([^\\\n]*?)\1\s*\+\s*(["'`])([^\\\n]*?)\3/g,
      (_, quote, left, _rightQuote, right) => `${quote}${left}${right}${quote}`
    );
    if (next === normalized) break;
    normalized = next;
  }
  return normalized;
}

function appendComputedPropertyTokens(source) {
  let computedTokens = "";
  for (const match of source.matchAll(/\b(?:window|globalThis|document)\s*\[([^\]]*)\]/gi)) {
    const literals = [...match[1].matchAll(/(["'`])([^\\\n]*?)\1/g)].map((literal) => literal[2]);
    if (literals.length > 0) computedTokens += ` ${literals.join("")} `;
  }
  return `${source} ${computedTokens}`;
}

function runtimeResourceErrors(scriptBodies) {
  const source = appendComputedPropertyTokens(normalizeStaticStringConcatenations(scriptBodies.join("\n")));
  const code = maskJavaScriptStrings(scriptBodies.join("\n"));
  const errors = [];
  const forbiddenTokens = [
    ["SharedWorker", /\bSharedWorker\b/],
    ["Worker", /\bWorker\b/],
    ["serviceWorker.register", /\bserviceWorker\b/],
    ["importScripts", /\bimportScripts\b/],
    ["navigator.sendBeacon", /\bsendBeacon\b/],
    ["fetch", /\bfetch\b/],
    ["XMLHttpRequest", /\bXMLHttpRequest\b/],
    ["WebSocket", /\bWebSocket\b/],
    ["EventSource", /\bEventSource\b/],
    ["dynamic import", /\bimport\s*\(/],
    ["URL construction/object URL", /\b(?:URL|createObjectURL)\b/],
    ["document.write", /\bwrite\b/],
    ["constructed resource element", /\bcreateElement(?:NS)?\b/],
    ["constructed Image", /\bImage\b/],
    ["constructed Audio", /\bAudio\b/]
  ];
  for (const [label, pattern] of forbiddenTokens) {
    if (pattern.test(source)) errors.push(`runtime resource: ${label}`);
  }
  if (
    /\bimport\s+(?:(?:[\w$*{}\s,]+)\s+from\s+)?["']/m.test(code) ||
    /\bexport\s+(?:\*|\{[^}]*\}|[\w$]+)\s+from\s+["']/m.test(code)
  ) {
    errors.push("runtime resource: static ES module import/export");
  }
  if (/\.\s*open\s*\(\s*["'](?:GET|POST|PUT|PATCH|DELETE|HEAD|OPTIONS)["']\s*,/i.test(source)) {
    errors.push("runtime resource: XMLHttpRequest.open");
  }

  for (const match of source.matchAll(/\.\s*(?:src|href)\s*=\s*([^;\n]+)/gi)) {
    if (!isHashAnchorExpression(match[1])) errors.push("runtime resource: dynamic src/href assignment");
  }
  for (const match of source.matchAll(/\[\s*(?:(["'])(?:src|href)\1|[^\]]*(?:src|href)[^\]]*)\s*\]\s*=\s*([^;\n]+)/gi)) {
    if (!isHashAnchorExpression(match[2])) errors.push("runtime resource: dynamic src/href assignment");
  }
  for (const match of source.matchAll(/\.\s*setAttribute\s*\(\s*(["'])(?:src|href)\1\s*,\s*([^)]*)\)/gi)) {
    if (!isHashAnchorExpression(match[2])) errors.push("runtime resource: dynamic src/href assignment");
  }

  return errors;
}

const resolvedTarget = path.resolve(target);
const html = fs.readFileSync(resolvedTarget, "utf8");
const commentStrippedHtml = html.replace(/<!--[\s\S]*?-->/g, " ");
const source = stripComments(html);
const scriptlessHtml = commentStrippedHtml.replace(/<script\b[^>]*>[\s\S]*?<\/script\s*>/gi, " ");
const stylelessHtml = commentStrippedHtml.replace(/<style\b[^>]*>[\s\S]*?<\/style\s*>/gi, " ");
const scriptBodies = extractTagBodies(stylelessHtml, "script").map((body) => stripDelimitedComments(body, true));
const styleBodies = extractTagBodies(scriptlessHtml, "style").map((body) => stripDelimitedComments(body, false));
const documentMarkup = markupWithoutExecutableBodies(commentStrippedHtml);
const inlineEventHandlers = inlineEventHandlerBodies(documentMarkup).map((body) => stripDelimitedComments(body, true));
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

const hasNetworkToggle = [...documentMarkup.matchAll(/<button\b[^>]*>/gi)].some(([tagSource]) => {
  return attributeValue(tagSource, "data-action") === "toggle-network";
});
if (!hasNetworkToggle) {
  errors.push("missing: button[data-action=\"toggle-network\"]");
}
if (!hasVisibleFocusRule(styleBodies, /(?:^|[\s>+~])(?:button|\.map-node)[^\s>+~]*:focus-visible\b/i)) {
  errors.push("missing: visible focus for button or map-node controls");
}
if (!hasVisibleFocusRule(styleBodies, /\[data-action\s*=\s*(?:(["'])toggle-network\1|toggle-network)\s*\][^\s>+~]*:focus-visible\b/i)) {
  errors.push("missing: visible focus for network toggle");
}

const staticFallbackCount = staticMapNodeCount(documentMarkup);
const staticFallbackIds = staticMapNodeConceptIds(documentMarkup);
if (staticFallbackCount < 6) {
  errors.push(`expected at least six static #atlas-map fallback buttons, found ${staticFallbackCount}`);
}

if (/\b@import\b/i.test(source)) errors.push("external resource: @import");

if (/(?:https?:)?\/\//i.test(source)) errors.push("external resource: http(s) or protocol-relative literal");

errors.push(...runtimeResourceErrors([...scriptBodies, ...inlineEventHandlers]));

for (const match of source.matchAll(/\burl\s*\(\s*(["']?)(.*?)\1\s*\)/gi)) {
  const prefix = source.slice(Math.max(0, match.index - 8), match.index);
  if (/new\s*$/i.test(prefix)) continue;
  const resource = match[2].trim();
  if (resource && !resource.startsWith("#")) errors.push(`external resource: CSS url(${resource})`);
}

for (const match of source.matchAll(/\b(?:src|href|poster|data)\s*=\s*(["'])\s*(\/\/[^"']*)\1/gi)) {
  errors.push(`external resource: protocol-relative ${match[2]}`);
}

for (const match of resourceBearingAttributeMatches(documentMarkup)) {
  errors.push(`external resource: <${match.tag}> ${match.attribute}=${match.value}`);
}

for (const match of attributeMatches(documentMarkup, "script", "src")) {
  errors.push(`external resource: script src=${match.value}`);
}
for (const match of attributeMatches(documentMarkup, "link", "href")) {
  errors.push(`external resource: link href=${match.value}`);
}
for (const tag of ["img", "embed", "object", "iframe", "audio", "video", "source", "track"]) {
  for (const attribute of ["src", "href", "data", "poster"]) {
    for (const match of attributeMatches(documentMarkup, tag, attribute)) {
      errors.push(`external resource: <${tag}> ${attribute}=${match.value}`);
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
  const coreConceptIds = concepts
    .filter(({ properties }) => /^true\b/.test(properties.get("core")?.value.trimStart() ?? ""))
    .map(({ properties }) => stringValue(properties.get("id")))
    .filter(Boolean);
  const distinctCoreConceptIds = new Set(coreConceptIds);
  if (staticFallbackCount !== staticFallbackIds.length) {
    errors.push("static #atlas-map fallback buttons must not duplicate data-concept-id values");
  }
  if (
    coreConceptIds.length !== distinctCoreConceptIds.size ||
    staticFallbackIds.length !== distinctCoreConceptIds.size ||
    staticFallbackIds.some((id) => !distinctCoreConceptIds.has(id))
  ) {
    errors.push("static #atlas-map fallback IDs must exactly match core:true concept IDs");
  }

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
