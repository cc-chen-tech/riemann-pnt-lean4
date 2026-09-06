#!/bin/sh

set -eu

write_target=
if [ "$#" -eq 1 ]; then
    manifest=$1
elif [ "$#" -eq 3 ] && [ "$1" = "--write" ]; then
    write_target=$2
    manifest=$3
else
    printf '%s\n' "usage: $0 [--write DAG.md] proof-dag.yaml" >&2
    exit 2
fi

if [ ! -r "$manifest" ]; then
    printf 'error: cannot read manifest: %s\n' "$manifest" >&2
    exit 2
fi

awk -v write_target="$write_target" '
function trim(value) {
    sub(/^[[:space:]]+/, "", value)
    sub(/[[:space:]]+$/, "", value)
    return value
}

function report_error(message) {
    errors++
    print "ERROR: " message
}

function set_field(field, value) {
    if (field == "status") {
        if (status_seen[current]) {
            report_error("node " node_id[current] " has duplicate status fields")
        }
        status_seen[current] = 1
        status[current] = value
    } else if (field == "owner") {
        if (owner_seen[current]) {
            report_error("node " node_id[current] " has duplicate owner fields")
        }
        owner_seen[current] = 1
        owner[current] = value
    } else if (field == "worktree") {
        if (worktree_seen[current]) {
            report_error("node " node_id[current] " has duplicate worktree fields")
        }
        worktree_seen[current] = 1
        worktree[current] = value
    } else if (field == "summary") {
        summary[current] = value
    }
}

function visit(node_number_arg, dependency_index, dependency) {
    if (visiting[node_number_arg]) {
        cycle_key = node_id[node_number_arg]
        if (!reported_cycle[cycle_key]) {
            report_error("dependency cycle includes node " cycle_key)
            reported_cycle[cycle_key] = 1
        }
        return
    }
    if (visited[node_number_arg]) {
        return
    }

    visiting[node_number_arg] = 1
    for (dependency_index = 1; dependency_index <= dependency_count[node_number_arg]; dependency_index++) {
        dependency = dependency_at[node_number_arg, dependency_index]
        if (node_index[dependency]) {
            visit(node_index[dependency])
        }
    }
    visiting[node_number_arg] = 0
    visited[node_number_arg] = 1
}

function mermaid_identifier(node_number_arg, safe, candidate, suffix) {
    safe = node_id[node_number_arg]
    gsub(/[^[:alnum:]_]/, "_", safe)
    if (safe == "") {
        safe = "node"
    }
    candidate = "node_" safe
    suffix = 1
    while (used_mermaid_identifier[candidate]) {
        suffix++
        candidate = "node_" safe "_" suffix
    }
    used_mermaid_identifier[candidate] = 1
    mermaid_id[node_number_arg] = candidate
}

function mermaid_escape(value) {
    gsub(/&/, "and", value)
    gsub(/"/, "_", value)
    gsub(/</, "(", value)
    gsub(/>/, ")", value)
    gsub(/\[/, "", value)
    gsub(/\]/, "", value)
    gsub(/\{/, "", value)
    gsub(/\}/, "", value)
    gsub(/\|/, "/", value)
    gsub(/`/, "_", value)
    gsub(/[[:cntrl:]]/, " ", value)
    return value
}

function display_field(seen, value) {
    if (!seen || value == "" || value == "null") {
        return "(unassigned)"
    }
    return value
}

BEGIN {
    nodes_seen = 0
    in_nodes = 0
    current = 0
    errors = 0
    manifest_version = ""
    generated_from = ""
}

{
    sub(/\r$/, "", $0)
    if ($0 ~ /^[[:space:]]*$/ || $0 ~ /^[[:space:]]*#/) {
        next
    }

    if ($0 ~ /^version:/) {
        value = $0
        sub(/^version:[[:space:]]*/, "", value)
        manifest_version = trim(value)
        next
    }

    if ($0 ~ /^generated_from:/) {
        value = $0
        sub(/^generated_from:[[:space:]]*/, "", value)
        generated_from = trim(value)
        next
    }

    if ($0 ~ /^nodes:[[:space:]]*$/) {
        nodes_seen = 1
        in_nodes = 1
        list_mode = ""
        next
    }

    if ($0 ~ /^  - id:/) {
        if (!in_nodes) {
            report_error("node appears before the nodes section")
        }

        raw_id = $0
        sub(/^  - id:[[:space:]]*/, "", raw_id)
        raw_id = trim(raw_id)
        node_number++
        current = node_number
        if (raw_id == "") {
            report_error("node entry has an empty id")
            raw_id = "__invalid_node_" node_number
        } else if (raw_id !~ /^[[:alnum:]][[:alnum:]_-]*$/) {
            report_error("invalid node id: " raw_id)
        }
        if (node_index[raw_id]) {
            report_error("duplicate node id: " raw_id)
        } else {
            node_index[raw_id] = current
        }
        node_id[current] = raw_id
        status_seen[current] = 0
        owner_seen[current] = 0
        worktree_seen[current] = 0
        dependency_declared[current] = 0
        dependency_count[current] = 0
        evidence_declared[current] = 0
        evidence_count[current] = 0
        list_mode = ""
        next
    }

    if ($0 ~ /^  - /) {
        report_error("malformed node entry; expected an id field")
        list_mode = ""
        next
    }

    if ($0 ~ /^    dependencies:/) {
        if (current == 0) {
            report_error("dependencies field appears outside a node")
            next
        }
        if (dependency_declared[current]) {
            report_error("node " node_id[current] " has duplicate dependencies fields")
        }
        dependency_declared[current] = 1
        value = $0
        sub(/^    dependencies:[[:space:]]*/, "", value)
        value = trim(value)
        if (value == "[]") {
            dependency_block[current] = 0
            list_mode = ""
        } else if (value == "") {
            dependency_block[current] = 1
            list_mode = "dependencies"
        } else {
            dependency_block[current] = 0
            report_error("node " node_id[current] " has malformed dependencies")
            list_mode = ""
        }
        next
    }

    if ($0 ~ /^    evidence:/) {
        if (current == 0) {
            report_error("evidence field appears outside a node")
            next
        }
        if (evidence_declared[current]) {
            report_error("node " node_id[current] " has duplicate evidence fields")
        }
        evidence_declared[current] = 1
        value = $0
        sub(/^    evidence:[[:space:]]*/, "", value)
        value = trim(value)
        if (value == "[]") {
            list_mode = ""
        } else if (value == "") {
            list_mode = "evidence"
        } else {
            report_error("node " node_id[current] " has malformed evidence")
            list_mode = ""
        }
        next
    }

    if ($0 ~ /^    status:/ || $0 ~ /^    owner:/ || $0 ~ /^    worktree:/ || $0 ~ /^    summary:/) {
        if (current == 0) {
            report_error("node field appears outside a node")
            next
        }
        field_line = $0
        if (field_line ~ /^    status:/) {
            field = "status"
            sub(/^    status:[[:space:]]*/, "", field_line)
        } else if (field_line ~ /^    owner:/) {
            field = "owner"
            sub(/^    owner:[[:space:]]*/, "", field_line)
        } else if (field_line ~ /^    worktree:/) {
            field = "worktree"
            sub(/^    worktree:[[:space:]]*/, "", field_line)
        } else {
            field = "summary"
            sub(/^    summary:[[:space:]]*/, "", field_line)
        }
        set_field(field, trim(field_line))
        list_mode = ""
        next
    }

    if ($0 ~ /^    -/ || $0 ~ /^      -/) {
        if (current == 0) {
            report_error("list item appears outside a node")
            next
        }
        item = $0
        sub(/^[[:space:]]*-[[:space:]]*/, "", item)
        item = trim(item)
        if (list_mode == "dependencies") {
            if (item == "" || item !~ /^[[:alnum:]][[:alnum:]_-]*$/) {
                report_error("node " node_id[current] " has invalid dependency id: " item)
            } else {
                dependency_count[current]++
                dependency_at[current, dependency_count[current]] = item
            }
        } else if (list_mode == "evidence") {
            if (item == "") {
                report_error("node " node_id[current] " has an empty evidence item")
            } else {
                evidence_count[current]++
            }
        }
        next
    }

    if ($0 ~ /^    [^[:space:]][^:]*:/) {
        list_mode = ""
        next
    }
}

END {
    if (!nodes_seen) {
        report_error("missing nodes section")
    }
    if (node_number == 0) {
        report_error("manifest contains no nodes")
    }

    edge_count = 0
    for (i = 1; i <= node_number; i++) {
        if (!status_seen[i]) {
            report_error("node " node_id[i] " is missing a status")
        } else if (status[i] != "open" && status[i] != "claimed" && status[i] != "blocked" && status[i] != "verified") {
            report_error("node " node_id[i] " has invalid status: " status[i])
        }

        if (!dependency_declared[i]) {
            report_error("node " node_id[i] " is missing a dependencies field")
        } else if (dependency_block[i] && dependency_count[i] == 0) {
            report_error("node " node_id[i] " has an empty dependencies list")
        }
        if (status[i] == "claimed" && (!owner_seen[i] || owner[i] == "" || owner[i] == "null")) {
            report_error("claimed node " node_id[i] " must have an owner")
        }
        if (status[i] == "verified" && evidence_count[i] == 0) {
            report_error("verified node " node_id[i] " must have evidence")
        }

        edge_count += dependency_count[i]
        for (j = 1; j <= dependency_count[i]; j++) {
            dependency = dependency_at[i, j]
            if (dependency == node_id[i]) {
                report_error("node " node_id[i] " has a self-dependency")
            } else if (!node_index[dependency]) {
                report_error("node " node_id[i] " references missing dependency: " dependency)
            }
        }
    }

    if (errors == 0) {
        for (i = 1; i <= node_number; i++) {
            visit(i)
        }
    }

    if (errors > 0) {
        printf "validation=failed\n"
        printf "nodes=%d edges=%d\n", node_number, edge_count
        exit 1
    }

    printf "validation=ok\n"
    printf "nodes=%d edges=%d\n", node_number, edge_count
    print "claimable open nodes (all dependencies verified):"
    claimable_count = 0
    for (i = 1; i <= node_number; i++) {
        if (status[i] != "open") {
            continue
        }
        claimable = 1
        for (j = 1; j <= dependency_count[i]; j++) {
            dependency = dependency_at[i, j]
            if (status[node_index[dependency]] != "verified") {
                claimable = 0
            }
        }
        if (claimable) {
            claimable_count++
            if (summary[i] != "") {
                printf "  %s - %s\n", node_id[i], summary[i]
            } else {
                printf "  %s\n", node_id[i]
            }
        }
    }
    if (claimable_count == 0) {
        print "  none"
    }

    print "blocked nodes (owners):"
    blocked_count = 0
    for (i = 1; i <= node_number; i++) {
        if (status[i] == "blocked") {
            blocked_count++
            if (!owner_seen[i] || owner[i] == "" || owner[i] == "null") {
                printf "  %s - owner: (unassigned)\n", node_id[i]
            } else {
                printf "  %s - owner: %s\n", node_id[i], owner[i]
            }
        }
    }
    if (blocked_count == 0) {
        print "  none"
    }

    print "claimed nodes (owners):"
    claimed_count = 0
    for (i = 1; i <= node_number; i++) {
        if (status[i] == "claimed") {
            claimed_count++
            printf "  %s - owner: %s\n", node_id[i], owner[i]
        }
    }
    if (claimed_count == 0) {
        print "  none"
    }

    if (write_target != "") {
        for (i = 1; i <= node_number; i++) {
            mermaid_identifier(i)
            status_count[status[i]]++
        }

        print "# Proof DAG" > write_target
        print "" > write_target
        print "_Generated from proof-dag.yaml by scripts/dag_status.sh; edit the manifest and regenerate this file._" > write_target
        print "" > write_target
        print "## Snapshot" > write_target
        print "" > write_target
        print "- Validation: `ok`" > write_target
        printf "- Nodes: `%d`\n", node_number > write_target
        printf "- Dependency edges: `%d`\n", edge_count > write_target
        printf "- Status counts: `open=%d`, `claimed=%d`, `blocked=%d`, `verified=%d`\n", status_count["open"], status_count["claimed"], status_count["blocked"], status_count["verified"] > write_target
        if (manifest_version != "") {
            printf "- Manifest version: `%s`\n", mermaid_escape(manifest_version) > write_target
        }
        if (generated_from != "") {
            printf "- Generated from: `%s`\n", mermaid_escape(generated_from) > write_target
        }
        print "" > write_target
        print "> Warning: branch and worktree names are execution metadata. They identify the current coordination context; they are not proof evidence or theorem status." > write_target
        print "" > write_target
        print "## Operating instructions" > write_target
        print "" > write_target
        print "1. Treat `proof-dag.yaml` as the canonical state; do not edit this generated snapshot directly." > write_target
        print "2. Inspect the current state with `scripts/dag_status.sh proof-dag.yaml`." > write_target
        print "3. Regenerate this view after a validated manifest change with `scripts/dag_status.sh --write DAG.md proof-dag.yaml`." > write_target
        print "4. An open node is claimable only when every dependency is `verified`; a verified node requires named acceptance evidence." > write_target
        print "" > write_target
        print "## Status legend" > write_target
        print "" > write_target
        print "The node colors correspond to the manifest status: `open`, `claimed`, `blocked`, and `verified`." > write_target
        print "" > write_target
        print "## Graph" > write_target
        print "" > write_target
        print "```mermaid" > write_target
        print "flowchart TD" > write_target
        for (i = 1; i <= node_number; i++) {
            label = mermaid_escape(node_id[i]) "<br/>status: " mermaid_escape(status[i])
            label = label "<br/>owner: " mermaid_escape(display_field(owner_seen[i], owner[i]))
            label = label "<br/>worktree: " mermaid_escape(display_field(worktree_seen[i], worktree[i]))
            if (summary[i] != "") {
                label = label "<br/>" mermaid_escape(summary[i])
            }
            printf "    %s[\"%s\"]\n", mermaid_id[i], label > write_target
        }
        for (i = 1; i <= node_number; i++) {
            for (j = 1; j <= dependency_count[i]; j++) {
                dependency = dependency_at[i, j]
                printf "    %s --> %s\n", mermaid_id[node_index[dependency]], mermaid_id[i] > write_target
            }
        }
        print "" > write_target
        print "    classDef open fill:#fff2cc,stroke:#bf9000,color:#000;" > write_target
        print "    classDef claimed fill:#cfe2f3,stroke:#3d85c6,color:#000;" > write_target
        print "    classDef blocked fill:#f4cccc,stroke:#cc0000,color:#000;" > write_target
        print "    classDef verified fill:#d9ead3,stroke:#38761d,color:#000;" > write_target
        for (i = 1; i <= node_number; i++) {
            printf "    class %s %s;\n", mermaid_id[i], status[i] > write_target
        }
        print "```" > write_target
        close(write_target)
        printf "graph=%s\n", write_target
    }
}
' "$manifest"
