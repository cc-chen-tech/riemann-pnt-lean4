#!/usr/bin/env ruby

require "psych"
require "set"

STATUSES = %w[open claimed blocked verified].freeze
TYPES = %w[theorem lemma audit integration].freeze
NODE_FIELDS = %w[id type status summary dependencies owner worktree source_paths acceptance_command evidence].freeze
ID_PATTERN = /\A[[:alnum:]][[:alnum:]_-]*\z/

def usage
  warn "usage: scripts/dag_status.sh [--write DAG.md] proof-dag.yaml"
  exit 2
end

def arguments(argv)
  return [nil, argv[0]] if argv.length == 1
  return [argv[1], argv[2]] if argv.length == 3 && argv[0] == "--write"

  usage
end

def duplicate_keys(node, location = "document", errors = [])
  case node
  when Psych::Nodes::Mapping
    seen = Set.new
    node.children.each_slice(2) do |key, value|
      unless key.is_a?(Psych::Nodes::Scalar)
        errors << "non-scalar YAML mapping key at #{location}"
        next
      end
      errors << "duplicate YAML key #{key.value.inspect} at #{location}" if seen.include?(key.value)
      seen << key.value
      duplicate_keys(value, "#{location}.#{key.value}", errors)
    end
  when Psych::Nodes::Sequence
    node.children.each_with_index { |child, index| duplicate_keys(child, "#{location}[#{index}]", errors) }
  when Psych::Nodes::Document, Psych::Nodes::Stream
    node.children.each { |child| duplicate_keys(child, location, errors) }
  end
  errors
end

def load_yaml(path)
  source = File.read(path)
  tree = Psych.parse_stream(source, path)
  errors = duplicate_keys(tree)
  data = Psych.safe_load(
    source,
    permitted_classes: [],
    permitted_symbols: [],
    aliases: false,
    filename: path
  )
  [data, errors]
rescue Psych::Exception => error
  puts "ERROR: invalid YAML: #{error.message.lines.first.strip}"
  puts "validation=failed"
  exit 1
end

def present_string?(value)
  value.is_a?(String) && !value.strip.empty?
end

def source_file(repo_root, path)
  return nil unless present_string?(path)

  candidate = File.expand_path(path, repo_root)
  prefix = "#{repo_root.delete_suffix(File::SEPARATOR)}#{File::SEPARATOR}"
  candidate.start_with?(prefix) ? candidate : nil
end

def detect_cycles(nodes_by_id)
  state = {}
  cycles = []
  visit = lambda do |node_id|
    if state[node_id] == :visiting
      cycles << node_id unless cycles.include?(node_id)
      next
    end
    next if state[node_id] == :visited

    state[node_id] = :visiting
    nodes_by_id[node_id]["dependencies"].each do |dependency|
      visit.call(dependency) if nodes_by_id.key?(dependency)
    end
    state[node_id] = :visited
  end
  nodes_by_id.each_key { |node_id| visit.call(node_id) }
  cycles
end

def mermaid_id(node_id, used)
  safe = node_id.gsub(/[^[:alnum:]_]/, "_")
  safe = "node" if safe.empty?
  base = "node_#{safe}"
  candidate = base
  suffix = 1
  while used.include?(candidate)
    suffix += 1
    candidate = "#{base}_#{suffix}"
  end
  used << candidate
  candidate
end

def mermaid_escape(value)
  value.to_s
       .gsub("&", "and")
       .gsub('"', "_")
       .gsub("<", "(")
       .gsub(">", ")")
       .gsub(/[\[\]{}]/, "")
       .gsub("|", "/")
       .gsub("`", "_")
       .gsub(/[[:cntrl:]]/, " ")
end

def display(value)
  present_string?(value) ? value : "(unassigned)"
end

def graph_markdown(manifest, nodes, edge_count)
  counts = STATUSES.to_h { |status| [status, nodes.count { |node| node["status"] == status }] }
  used = Set.new
  ids = nodes.to_h { |node| [node["id"], mermaid_id(node["id"], used)] }
  lines = [
    "# Proof DAG",
    "",
    "_Generated from proof-dag.yaml by scripts/dag_status.sh; edit the manifest and regenerate this file._",
    "",
    "## Snapshot",
    "",
    "- Validation: `ok`",
    "- Nodes: `#{nodes.length}`",
    "- Dependency edges: `#{edge_count}`",
    "- Status counts: `open=#{counts['open']}`, `claimed=#{counts['claimed']}`, `blocked=#{counts['blocked']}`, `verified=#{counts['verified']}`",
    "- Manifest version: `#{mermaid_escape(manifest['version'])}`",
    "- Generated from: `#{mermaid_escape(manifest['generated_from'])}`",
    "",
    "> Warning: branch and worktree names are execution metadata. They identify the current coordination context; they are not proof evidence or theorem status.",
    "",
    "## Operating instructions",
    "",
    "1. Treat `proof-dag.yaml` as the canonical state; do not edit this generated snapshot directly.",
    "2. Inspect the current state with `scripts/dag_status.sh proof-dag.yaml`.",
    "3. Regenerate this view after a validated manifest change with `scripts/dag_status.sh --write DAG.md proof-dag.yaml`.",
    "4. An open node is claimable only when every dependency is `verified`; a verified node requires named acceptance evidence.",
    "",
    "## Status legend",
    "",
    "The node colors correspond to the manifest status: `open`, `claimed`, `blocked`, and `verified`.",
    "",
    "## Graph",
    "",
    "```mermaid",
    "flowchart TD",
  ]
  nodes.each do |node|
    label = "#{mermaid_escape(node['id'])}<br/>status: #{mermaid_escape(node['status'])}"
    label += "<br/>owner: #{mermaid_escape(display(node['owner']))}"
    label += "<br/>worktree: #{mermaid_escape(display(node['worktree']))}"
    label += "<br/>#{mermaid_escape(node['summary'])}"
    lines << "    #{ids[node['id']]}[\"#{label}\"]"
  end
  nodes.each do |node|
    node["dependencies"].each { |dependency| lines << "    #{ids[dependency]} --> #{ids[node['id']]}" }
  end
  lines.concat([
    "",
    "    classDef open fill:#fff2cc,stroke:#bf9000,color:#000;",
    "    classDef claimed fill:#cfe2f3,stroke:#3d85c6,color:#000;",
    "    classDef blocked fill:#f4cccc,stroke:#cc0000,color:#000;",
    "    classDef verified fill:#d9ead3,stroke:#38761d,color:#000;",
  ])
  nodes.each { |node| lines << "    class #{ids[node['id']]} #{node['status']};" }
  lines << "```"
  "#{lines.join("\n")}\n"
end

write_target, manifest_path = arguments(ARGV)
unless File.readable?(manifest_path)
  warn "error: cannot read manifest: #{manifest_path}"
  exit 2
end

manifest, errors = load_yaml(manifest_path)
unless manifest.is_a?(Hash)
  errors << "manifest root must be a mapping"
  manifest = {}
end
%w[version generated_from nodes].each do |field|
  errors << "manifest is missing required field: #{field}" unless manifest.key?(field)
end
if manifest.key?("generated_from") && !present_string?(manifest["generated_from"])
  errors << "generated_from must be a non-empty string"
end

nodes = manifest["nodes"]
unless nodes.is_a?(Array)
  errors << "nodes must be a sequence"
  nodes = []
end
errors << "manifest contains no nodes" if nodes.empty?

repo_root = File.expand_path("..", __dir__)
nodes_by_id = {}
nodes.each_with_index do |node, index|
  unless node.is_a?(Hash)
    errors << "node entry #{index + 1} must be a mapping"
    next
  end

  node_name = present_string?(node["id"]) ? node["id"] : "entry #{index + 1}"
  NODE_FIELDS.each do |field|
    errors << "node #{node_name} is missing required field: #{field}" unless node.key?(field)
  end

  node_id = node["id"]
  if !present_string?(node_id)
    errors << "node entry #{index + 1} has an empty id" if node.key?("id")
  elsif !ID_PATTERN.match?(node_id)
    errors << "invalid node id: #{node_id}"
  elsif nodes_by_id.key?(node_id)
    errors << "duplicate node id: #{node_id}"
  else
    nodes_by_id[node_id] = node
  end

  errors << "node #{node_name} has invalid type: #{node['type']}" if node.key?("type") && !TYPES.include?(node["type"])
  errors << "node #{node_name} has invalid status: #{node['status']}" if node.key?("status") && !STATUSES.include?(node["status"])
  if node.key?("summary") && !present_string?(node["summary"])
    errors << "node #{node_name} must have a non-empty summary"
  end

  dependencies = node["dependencies"]
  if node.key?("dependencies") && !dependencies.is_a?(Array)
    errors << "node #{node_name} dependencies must be a sequence"
  elsif dependencies.is_a?(Array)
    dependencies.each do |dependency|
      unless present_string?(dependency) && ID_PATTERN.match?(dependency)
        errors << "node #{node_name} has invalid dependency id: #{dependency}"
      end
    end
    errors << "node #{node_name} has duplicate dependencies" if dependencies.uniq.length != dependencies.length
  end

  if node.key?("owner") && !node["owner"].nil? && !present_string?(node["owner"])
    errors << "node #{node_name} owner must be null or a non-empty string"
  end
  if node.key?("worktree") && !node["worktree"].nil? && !present_string?(node["worktree"])
    errors << "node #{node_name} worktree must be null or a non-empty string"
  end

  source_paths = node["source_paths"]
  if node.key?("source_paths") && !source_paths.is_a?(Array)
    errors << "node #{node_name} source_paths must be a sequence"
  elsif source_paths.is_a?(Array)
    errors << "node #{node_name} source_paths must not be empty" if source_paths.empty?
    source_paths.each do |path|
      resolved = source_file(repo_root, path)
      if resolved.nil?
        errors << "node #{node_name} has invalid source path: #{path}"
      elsif !File.file?(resolved)
        errors << "node #{node_name} references missing source path: #{path}"
      end
    end
  end

  if node.key?("acceptance_command") && !present_string?(node["acceptance_command"])
    errors << "node #{node_name} must have a non-empty acceptance_command"
  end
  evidence = node["evidence"]
  if node.key?("evidence") && !evidence.is_a?(Array)
    errors << "node #{node_name} evidence must be a sequence"
  elsif evidence.is_a?(Array)
    evidence.each { |item| errors << "node #{node_name} has an empty evidence item" unless present_string?(item) }
  end
  if node["status"] == "claimed" && !present_string?(node["owner"])
    errors << "claimed node #{node_name} must have an owner"
  end
  if node["status"] == "verified" && (!evidence.is_a?(Array) || evidence.empty?)
    errors << "verified node #{node_name} must have evidence"
  end
end

nodes.each do |node|
  next unless node.is_a?(Hash) && present_string?(node["id"]) && node["dependencies"].is_a?(Array)

  node["dependencies"].each do |dependency|
    if dependency == node["id"]
      errors << "node #{node['id']} has a self-dependency"
    elsif present_string?(dependency) && !nodes_by_id.key?(dependency)
      errors << "node #{node['id']} references missing dependency: #{dependency}"
    end
  end
end
detect_cycles(nodes_by_id).each { |node_id| errors << "dependency cycle includes node #{node_id}" } if errors.empty?

edge_count = nodes.sum do |node|
  node.is_a?(Hash) && node["dependencies"].is_a?(Array) ? node["dependencies"].length : 0
end
unless errors.empty?
  errors.each { |error| puts "ERROR: #{error}" }
  puts "validation=failed"
  puts "nodes=#{nodes.length} edges=#{edge_count}"
  exit 1
end

puts "validation=ok"
puts "nodes=#{nodes.length} edges=#{edge_count}"
puts "claimable open nodes (all dependencies verified):"
claimable = nodes.select do |node|
  node["status"] == "open" && node["dependencies"].all? { |dependency| nodes_by_id[dependency]["status"] == "verified" }
end
claimable.empty? ? puts("  none") : claimable.each { |node| puts "  #{node['id']} - #{node['summary']}" }

puts "blocked nodes (owners):"
blocked = nodes.select { |node| node["status"] == "blocked" }
blocked.empty? ? puts("  none") : blocked.each { |node| puts "  #{node['id']} - owner: #{display(node['owner'])}" }

puts "claimed nodes (owners):"
claimed = nodes.select { |node| node["status"] == "claimed" }
claimed.empty? ? puts("  none") : claimed.each { |node| puts "  #{node['id']} - owner: #{node['owner']}" }

if write_target
  File.write(write_target, graph_markdown(manifest, nodes, edge_count))
  puts "graph=#{write_target}"
end
