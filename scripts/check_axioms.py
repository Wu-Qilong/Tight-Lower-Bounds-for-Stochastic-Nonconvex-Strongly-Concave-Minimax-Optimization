"""Check the complete Lean axiom-audit output using only Python's standard library."""
import re
import sys
from pathlib import Path

ALLOWED = {
    'propext', 'Classical.choice', 'Quot.sound',
    'NCSCPureStochasticLB.PaperExact.importedLemmaB1Certificate',
}
REQUIRED = {
    'NCSCPureStochasticLB.PaperExact.' + name for name in (
        'theorem41_paper', 'theorem51_paper',
        'corollary52_bv_paper', 'corollary52_as_paper',
    )
}


def check(text):
    if 'sorryAx' in text or re.search(r'(^|\n).*\berror:', text):
        raise ValueError('Lean errors or sorryAx found in the audit')
    records = [
        (name, {a.strip() for a in axioms.split(',') if a.strip()})
        for name, axioms in re.findall(
            r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S)
    ]
    records += [(name, set()) for name in re.findall(
        r"'([^']+)' does not depend on any axioms", text)]
    missing = REQUIRED - {name for name, _ in records}
    if missing:
        raise ValueError('Missing paper endpoints: ' + ', '.join(sorted(missing)))
    for name, axioms in records:
        if axioms - ALLOWED:
            raise ValueError(name + ': unexpected axioms ' + str(sorted(axioms - ALLOWED)))
    return len(records)


if __name__ == '__main__':
    try:
        path = Path(sys.argv[1] if len(sys.argv) > 1 else 'axiom_audit.log')
        count = check(path.read_text(encoding='utf-8-sig'))
    except (OSError, ValueError) as exc:
        print('Axiom audit FAILED:', exc, file=sys.stderr)
        sys.exit(1)
    print(f'Axiom audit passed: {count} records; only approved dependencies.')
