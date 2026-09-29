#!/usr/bin/env ruby
# Validate formalization.yaml against the repository.
#
# Metadata checks (no Lean):
# * project.lean_toolchain, comparator toolchain and every workspace's lean-toolchain equal the
#   root lean-toolchain; every dependency revision equals the one locked in lake-manifest.json;
# * every target's module file exists and declares the target's declaration, and every related
#   declaration is declared somewhere in the library; each target's expected_axioms equal
#   axioms.expected. A target of kind `sanity-check` has no library declaration: it is certified
#   by its challenge workspace alone, so it has no module, declaration or related declarations;
# * the challenge inventory (the targets' challenge fields) equals challenges/*/config.json;
#   each workspace is complete and trusted-only by default. Its trusted statement surface is
#   Challenge.lean plus either vocabulary files Challenge/*.lean or a single Statement.lean (the
#   two layouts used in this family of repositories), all importing only Mathlib and the
#   workspace's own trusted modules; Solution.lean imports only PerronVariational, Mathlib and the
#   workspace's trusted modules. Config theorem names equal the target's challenge_theorems, and
#   config permitted axioms equal axioms.expected;
# * the pinned Comparator tool revisions agree with scripts/release-comparator.sh.
#
# Lean checks (after `lake build`): every declaration and related declaration resolves, and each
# depends on exactly axioms.expected.
#
# Usage: ruby scripts/check-formalization-manifest.rb [--metadata-only]
require 'yaml'
require 'json'
require 'open3'
require 'tempfile'
require 'pathname'

ROOT = Pathname.new(__dir__).parent
LEAN_NAME = /\A[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\z/
DECL_PREFIX = /^(?:@\[[^\]]*\]\s*)?(?:public |protected |private )?(?:theorem|lemma) /
metadata_only = ARGV == ['--metadata-only']
abort 'usage: check-formalization-manifest.rb [--metadata-only]' unless ARGV.empty? || metadata_only
Dir.chdir(ROOT)
failures = []

manifest = YAML.safe_load_file('formalization.yaml')
abort 'formalization.yaml must be a mapping' unless manifest.is_a?(Hash)
expected_axioms = manifest.fetch('axioms').fetch('expected')
abort 'axioms.expected must be a nonempty list' unless expected_axioms.is_a?(Array) && !expected_axioms.empty?
targets = manifest.fetch('targets')
abort 'targets must be a nonempty list' unless targets.is_a?(Array) && !targets.empty?
abort 'duplicate target id' unless targets.map { |t| t.fetch('id') }.uniq.length == targets.length
root_toolchain = File.read('lean-toolchain').strip
failures << 'project.lean_toolchain differs from lean-toolchain' \
  unless manifest.fetch('project').fetch('lean_toolchain') == root_toolchain

# Dependencies agree with lake-manifest.json.
locked = JSON.parse(File.read('lake-manifest.json')).fetch('packages').to_h { |p| [p['name'], p['rev']] }
manifest.fetch('dependencies').each do |dep|
  failures << "dependency #{dep['name']}: rev #{dep['rev']} differs from lake-manifest.json (#{locked[dep['name']].inspect})" \
    unless locked[dep['name']] == dep['rev']
end

library_sources = (Dir.glob('PerronVariational/**/*.lean') + ['PerronVariational.lean']).to_h { |f| [f, File.read(f)] }
# A declaration `PerronVariational.A.b` may be written `theorem b` inside `namespace A`, or
# `theorem A.b`; accept either spelling (the Lean check below is authoritative).
declared = lambda do |source, name|
  short = name.sub(/\APerronVariational\./, '')
  [short, short.split('.').last].uniq.any? do |n|
    source.match?(/#{DECL_PREFIX}#{Regexp.escape(n)}(?=[\s:({\[]|\z)/)
  end
end

# Targets.
SANITY_CHECK = 'sanity-check'
library_targets = targets.reject { |t| t['kind'] == SANITY_CHECK }
targets.each do |t|
  id = t.fetch('id')
  sanity = t['kind'] == SANITY_CHECK
  required = sanity ? %w[title kind challenge source informal] : %w[title kind module declaration challenge source informal]
  required.each do |k|
    failures << "#{id}: missing #{k}" unless t[k].is_a?(String) && !t[k].strip.empty?
  end
  failures << "#{id}: expected_axioms differ from axioms.expected" \
    unless t['expected_axioms'].is_a?(Array) && t['expected_axioms'].sort == expected_axioms.sort
  theorems = t['challenge_theorems']
  failures << "#{id}: challenge_theorems must be a nonempty list" \
    unless theorems.is_a?(Array) && !theorems.empty? && theorems.all? { |n| n.is_a?(String) && n.match?(LEAN_NAME) }
  if sanity
    %w[module declaration related_declarations].each do |k|
      failures << "#{id}: a sanity-check target has no #{k}" if t.key?(k)
    end
    next
  end
  names = [t['declaration'], *Array(t['related_declarations'])].compact
  names.each do |name|
    failures << "#{id}: invalid Lean name #{name.inspect}" unless name.match?(LEAN_NAME)
    failures << "#{id}: #{name} must be in the PerronVariational namespace" \
      unless name.start_with?('PerronVariational.')
  end
  file = "#{t['module'].to_s.tr('.', '/')}.lean"
  if !File.file?(file)
    failures << "#{id}: module #{t['module']} has no file #{file}"
  elsif !declared.call(File.read(file), t['declaration'].to_s)
    failures << "#{id}: #{file} does not declare #{t['declaration']}"
  end
  Array(t['related_declarations']).each do |name|
    failures << "#{id}: no library file declares #{name}" \
      unless library_sources.values.any? { |src| declared.call(src, name) }
  end
end

# External challenge inventory.
external = manifest.fetch('comparator').fetch('external_challenges')
allowed = external.fetch('permitted_axioms')
failures << 'comparator permitted_axioms differ from axioms.expected' unless allowed.sort == expected_axioms.sort
failures << 'external_challenges.toolchain differs from lean-toolchain' unless external['toolchain'] == root_toolchain
directory = external.fetch('directory')

listed = targets.map { |t| t['challenge'] }
failures << 'two targets share a challenge workspace' unless listed.uniq.length == listed.length
on_disk = Dir.glob("#{directory}/*/config.json").map { |c| File.dirname(c) }.sort
unless listed.sort == on_disk
  failures << "challenge inventory differs from formalization.yaml: " \
              "#{(on_disk - listed).inspect} unlisted, #{(listed - on_disk).inspect} missing"
end

imports = lambda do |f|
  # Accepts plain, `public`, `meta` and `public meta` imports (Lean module system).
  File.file?(f) ? File.read(f).scan(/^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)/).flatten : []
end

targets.each do |t|
  path = t['challenge'].to_s
  next unless File.directory?(path)
  %w[Challenge.lean Solution.lean config.json lakefile.toml lake-manifest.json lean-toolchain].each do |f|
    failures << "#{path}: missing #{f}" unless File.file?(File.join(path, f))
  end
  vocabulary = Dir.glob(File.join(path, 'Challenge', '*.lean')).sort
  statement = File.join(path, 'Statement.lean')
  vocabulary << statement if File.file?(statement)
  failures << "#{path}: no trusted vocabulary (Challenge/*.lean or Statement.lean)" if vocabulary.empty?
  vocabulary_modules = vocabulary.map do |f|
    f == statement ? 'Statement' : "Challenge.#{File.basename(f, '.lean')}"
  end
  toolchain = File.join(path, 'lean-toolchain')
  failures << "#{path}: lean-toolchain differs from the root" \
    if File.file?(toolchain) && File.read(toolchain).strip != root_toolchain
  [File.join(path, 'Challenge.lean'), *vocabulary].each do |f|
    bad = imports.call(f).reject { |m| m == 'Mathlib' || m.start_with?('Mathlib.') || vocabulary_modules.include?(m) }
    failures << "#{f}: imports outside Mathlib and the workspace vocabulary: #{bad.inspect}" unless bad.empty?
  end
  solution_imports = imports.call(File.join(path, 'Solution.lean'))
  bad = solution_imports.reject do |m|
    m == 'PerronVariational' || m.start_with?('PerronVariational.') ||
      m == 'Mathlib' || m.start_with?('Mathlib.') || vocabulary_modules.include?(m)
  end
  failures << "#{path}/Solution.lean: imports outside PerronVariational, Mathlib and the workspace vocabulary: #{bad.inspect}" \
    unless bad.empty?
  lakefile = File.join(path, 'lakefile.toml')
  if File.file?(lakefile)
    defaults = File.read(lakefile)[/^defaultTargets\s*=\s*\[([^\]]*)\]/, 1].to_s
    failures << "#{path}: Solution must not be a default target" if defaults.include?('Solution')
  end
  config_path = File.join(path, 'config.json')
  next unless File.file?(config_path)
  config = JSON.parse(File.read(config_path))
  failures << "#{path}: theorem_names differ from the target's challenge_theorems" \
    unless config.fetch('theorem_names') == t['challenge_theorems']
  failures << "#{path}: permitted_axioms differ from formalization.yaml" \
    unless config.fetch('permitted_axioms').sort == allowed.sort
  failures << "#{path}: unexpected challenge module" unless config.fetch('challenge_module') == 'Challenge'
  failures << "#{path}: unexpected solution module" unless config.fetch('solution_module') == 'Solution'
end

driver = File.read('scripts/release-comparator.sh')
{ 'comparator_revision' => 'COMPARATOR_REV',
  'lean4export_revision' => 'LEAN4EXPORT_REV',
  'landrun_revision' => 'LANDRUN_REV' }.each do |key, var|
  pinned = driver[/^#{var}=(\h+)$/, 1]
  failures << "#{key} #{external[key].inspect} differs from #{var} in scripts/release-comparator.sh" \
    unless pinned && external[key] == pinned
end

abort failures.join("\n") unless failures.empty?
if metadata_only
  puts "Validated #{targets.length} targets and #{on_disk.length} challenge workspaces (metadata only)"
  exit 0
end

# Lean: one invocation resolves every name and prints the axioms of every declaration.
names = library_targets.flat_map { |t| [t.fetch('declaration'), *Array(t['related_declarations'])] }.uniq
Tempfile.create(['manifest-check-', '.lean']) do |file|
  file.puts 'import PerronVariational'
  names.each { |n| file.puts "#check @#{n}" }
  names.each_with_index do |n, i|
    file.puts %Q(#eval IO.println "AXIOMS_BEGIN_#{i}")
    file.puts "#print axioms #{n}"
    file.puts %Q(#eval IO.println "AXIOMS_END_#{i}")
  end
  file.flush
  output, status = Open3.capture2e('lake', 'env', 'lean', file.path)
  output.force_encoding(Encoding::UTF_8)
  unless status.success?
    warn output
    abort 'Lean name resolution or axiom check failed'
  end
  names.each_with_index do |name, i|
    section = output[/AXIOMS_BEGIN_#{i}(.*?)AXIOMS_END_#{i}/m, 1]
    abort "missing #print axioms output for #{name}" unless section
    actual = if section.include?('does not depend on any axioms')
               []
             else
               block = section[/depends on axioms: \[([^\]]*)\]/, 1]
               abort "unrecognized #print axioms output for #{name}: #{section}" unless block
               block.split(',').map(&:strip).uniq
             end
    failures << "#{name}: axioms #{actual.sort.inspect}, expected #{expected_axioms.sort.inspect}" \
      unless actual.sort == expected_axioms.sort
  end
end
abort failures.join("\n") unless failures.empty?
puts "Validated #{targets.length} targets (#{library_targets.length} with library declarations; #{names.length} declarations resolve; axioms exactly " \
     "#{expected_axioms.sort.inspect}) and #{on_disk.length} challenge workspaces"
