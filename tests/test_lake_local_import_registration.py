"""Check Lake ownership of reachable local modules, independently of cached oleans."""
from pathlib import Path
import re
import subprocess


def _code_only(text):
    """Blank nested Lean comments and strings while preserving line boundaries."""
    out = []
    depth = 0
    string = False
    i = 0
    while i < len(text):
        pair = text[i:i + 2]
        char = text[i]
        if depth:
            if pair == '/-':
                depth += 1
                out.extend('  ')
                i += 2
                continue
            if pair == '-/':
                depth -= 1
                out.extend('  ')
                i += 2
                continue
            out.append('\n' if char == '\n' else ' ')
        elif string:
            if char == '\\' and i + 1 < len(text):
                out.extend('  ')
                i += 2
                continue
            if char == '"':
                string = False
            out.append('\n' if char == '\n' else ' ')
        elif pair == '--':
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            out.extend(' ' * (end - i))
            i = end
            continue
        elif pair == '/-':
            depth = 1
            out.extend('  ')
            i += 2
            continue
        elif char == '"':
            string = True
            out.append(' ')
        else:
            out.append(char)
        i += 1
    if depth or string:
        raise ValueError('unclosed comment/string in Lean input')
    return ''.join(out)


def _imports(text):
    result = []
    for match in re.finditer(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([^\n]+)',
                             _code_only(text), re.M):
        result.extend(re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", match.group(1)))
    return result


def _unregistered_dependencies(roots, sources):
    reachable = set()
    pending = list(roots)
    while pending:
        module = pending.pop()
        if module in reachable or module not in sources:
            continue
        reachable.add(module)
        pending.extend(_imports(sources[module]))
    return sorted(module for module in reachable
                  if not any(module == root or module.startswith(root + '.') for root in roots))


def test_import_parser_ignores_nested_comments_and_strings():
    text = ('/- import Wrong\n /- import AlsoWrong -/ -/\n'
            'import Mathlib.Real\npublic import Local.One Local.Two\n'
            'def example := "\nimport NotAModule\n"\n-- import WrongAgain\n')
    assert _imports(text) == ['Mathlib.Real', 'Local.One', 'Local.Two']


def test_missing_production_root_is_not_hidden_by_a_contract_root():
    sources = {'Test.Contract': 'import MathlibAux.Hidden',
               'MathlibAux.Hidden': 'import Mathlib.Real'}
    assert _unregistered_dependencies({'Test.Contract'}, sources) == ['MathlibAux.Hidden']
    assert not _unregistered_dependencies({'Test.Contract', 'MathlibAux.Hidden'}, sources)


def test_lake_root_prefix_covers_its_submodules():
    sources = {'Root': 'import Root.Child', 'Root.Child': 'import Mathlib.Real'}
    assert not _unregistered_dependencies({'Root'}, sources)
    sources = {'MathlibAux.Gamma': 'import MathlibAux.GammaVerticalStripBound',
               'MathlibAux.GammaVerticalStripBound': 'import Mathlib.Real'}
    assert _unregistered_dependencies({'MathlibAux.Gamma'}, sources) == ['MathlibAux.GammaVerticalStripBound']


def test_all_reachable_local_imports_are_owned_by_lake():
    root = Path(__file__).resolve().parents[1]
    lake = _code_only((root / 'lakefile.lean').read_text())
    assert len(re.findall(r'\blean_lib\b', lake)) == 1, 'update audit for multiple Lean libraries'
    assert not re.search(r'\bsrcDir\s*:=', lake), 'update audit for a custom source directory'
    assert len(re.findall(r'\broots\s*:=\s*#\[', lake)) == 1, 'update audit for multiple root arrays'
    assert not re.search(r'\bglobs\s*:=', lake), 'update this ownership audit for explicit Lake globs'
    block = re.search(r'\broots\s*:=\s*#\[(.*?)\]', lake, re.S)
    assert block, 'explicit Lake roots required'
    roots = set(re.findall(r"`([A-Za-z_][A-Za-z0-9_'.]*)", block.group(1)))
    files = subprocess.check_output(['git', 'ls-files', '-z', '--', '*.lean'], cwd=root).decode().split('\0')
    sources = {name[:-5].replace('/', '.'): (root / name).read_text() for name in files if name}
    assert roots and all(module in sources for module in roots), 'root source is missing'
    missing = _unregistered_dependencies(roots, sources)
    assert not missing, 'reachable local modules lack a Lake root/prefix: ' + ', '.join(missing)
