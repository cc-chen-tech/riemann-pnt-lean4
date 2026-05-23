#!/bin/bash
# Convert paper from standard article format to LIPIcs conference format.
# Usage: ./switch-to-lipics.sh [paper.tex]
#
# LIPIcs is a lightweight conference format commonly used for
# Interactive Theorem Proving (ITP), Certified Programs and Proofs (CPP),
# and similar venues where formalization papers are published.

set -euo pipefail

PAPER="${1:-main.tex}"

if [ ! -f "$PAPER" ]; then
    echo "Error: $PAPER not found"
    exit 1
fi

# Replace the document class
sed -i.bak 's/\\documentclass\[.*\]{article}/\\documentclass[a4paper,english,lineno]{lipics-v2021}/' "$PAPER"

# Add LIPIcs-specific packages
sed -i.bak '/\\usepackage{hyperref}/a\
\\usepackage[accepted]{lipics-v2021}\
\\EventEditors{...}\
\\EventNoEds{...}\
\\EventLongTitle{...}\
\\EventShortTitle{...}\
\\EventAcronym{...}\
\\EventYear{...}\
\\EventDate{...}\
\\EventLocation{...}\
\\SeriesVolume{...}\
\\ArticleNo{...}' "$PAPER"

# Switch bibliography style
sed -i.bak 's/\\bibliographystyle{alpha}/\\bibliographystyle{plainurl}/' "$PAPER"

# Remove geometry package (LIPIcs has its own layout)
sed -i.bak '/\\usepackage{geometry}/d' "$PAPER"
sed -i.bak '/\\geometry{.*}/d' "$PAPER"

# Clean up backup files
rm -f "$PAPER.bak"

echo "Done. Please fill in the LIPIcs metadata fields (EventEditors, EventLongTitle, etc.)"
echo "Download lipics-v2021.cls from https://www.dagstuhl.de/en/publishing/series/details/LIPIcs"
