"""Regression tests for truthful, fail-closed frontier classification."""
import copy
import json
from pathlib import Path
import sys
import unittest

TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS))
import wnear_blueprint as blueprint


class FrontierPolicyTests(unittest.TestCase):
    def setUp(self):
        self.manifest = json.loads(blueprint.MANIFEST.read_text())
        self.nodes = {n['id']: n for n in self.manifest['nodes']}
        self.rows = []
        for n in self.manifest['nodes']:
            admission = n['kind'] == 'admission'
            self.rows.append({'declaration': n['declaration'], 'is_theorem': n['kind'] != 'verification_contract',
                              'direct_sorry': admission, 'shape_hash': n['reviewed_shape_hash'], 'blueprint_label': n['label'],
                              'not_ready': n['kind'] in ['verification_contract', 'admission'] or n['id'] in ['global', 'exported', 'dispatch', 'object-parser', 'array-parser', 'ignored-opening', 'storage', 'lookup-raw-absent', 'lookup-absent', 'balance-lookup-absent', 'balance-caller-absent', 'balance-export-call-absent', 'method-ft_balance_of'], 'axioms': ['sorryAx'] if admission else ['propext'],
                              'type_dependencies': [], 'proof_dependencies': [], 'statement': 'test', 'type_hash': 1})
        self.by_id = {n['id']: row for n, row in zip(self.manifest['nodes'], self.rows)}
        self.by_id['storage']['type_dependencies'] = [self.nodes['owned-room']['declaration']]
        self.by_id['lookup-raw-absent']['proof_dependencies'] = [self.nodes['storage-read-absent']['declaration']]
        self.by_id['lookup-absent']['proof_dependencies'] = [self.nodes['lookup-raw-absent']['declaration']]
        self.by_id['balance-lookup-absent']['proof_dependencies'] = [self.nodes['lookup-absent']['declaration']]
        self.by_id['balance-caller-absent']['proof_dependencies'] = [self.nodes['balance-lookup-absent']['declaration']]
        self.by_id['balance-export-call-absent']['proof_dependencies'] = [self.nodes['balance-caller-absent']['declaration']]
        self.by_id['method-ft_balance_of']['axioms'].append('sorryAx')
        self.by_id['method-ft_balance_of']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['balance-no-issue', 'balance-accepted', 'balance-rejected']]
        self.by_id['global']['axioms'].append('sorryAx')
        self.by_id['global']['proof_dependencies'] = [self.nodes['exported']['declaration']]
        self.by_id['exported']['axioms'].append('sorryAx')
        self.by_id['exported']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['dispatch', 'binary-size']] + [
            n['declaration'] for n in self.manifest['nodes'] if n['kind'] == 'admission' and not n.get('indirect_admission')] + [self.nodes['method-ft_balance_of']['declaration']]
        self.by_id['dispatch']['type_dependencies'] = [self.nodes['remaining']['declaration']]
        self.by_id['dispatch']['proof_dependencies'] = [n['declaration'] for n in self.manifest['nodes']
                                                        if n.get('method') and n['kind'] != 'admission' and not n.get('exported_direct')]
        for n in self.manifest['nodes']:
            self.by_id[n['id']]['type_dependencies'] += [self.nodes[x]['declaration'] for x in n.get('required_type_dependencies', [])]
        self.audit = {'violations': [{'declaration': n, 'axioms': ['sorryAx']}
                                     for n in self.manifest['expected_incomplete']]}

    def test_conditional_composition_and_unresolved_hypotheses_are_visible(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        self.assertEqual(result['global']['status'], 'Conditional')
        self.assertEqual(result['dispatch']['status'], 'Conditional')
        self.assertEqual(result['object-parser']['status'], 'Conditional')
        self.assertEqual(result['ignored-opening']['status'], 'Conditional')
        self.assertEqual(result['array-parser']['status'], 'Conditional')
        self.assertEqual(result['storage']['status'], 'Conditional')
        self.assertEqual(result['ignore-hyp']['status'], 'Open')
        self.assertEqual(result['method-ft_total_supply']['status'], 'Proven')
        self.assertIn({'id': 'dispatch', 'status': 'Conditional'}, result['method-ft_total_supply']['integrated_into'])
        self.assertEqual(result['method-ft_balance_of']['status'], 'Conditional')
        self.assertEqual(sum(n['status'] == 'Open' for n in result.values() if n.get('method')), 8)

    def test_unlisted_admission_or_axiom_fails_closed(self):
        audit = copy.deepcopy(self.audit)
        audit['violations'].append({'declaration': 'WNear.untracked', 'axioms': ['sorryAx']})
        with self.assertRaisesRegex(ValueError, 'Untracked or stale audit frontier'):
            blueprint.classify(self.manifest, self.rows, audit)
        self.by_id['method-new']['axioms'].append('Lean.ofReduceBool')
        with self.assertRaisesRegex(ValueError, 'Nonstandard axioms'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_statement_weakening_and_stale_book_status_fail_closed(self):
        self.by_id['method-new']['shape_hash'] += 1
        with self.assertRaisesRegex(ValueError, 'Unreviewed statement or contract change'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['global']['not_ready'] = False
        with self.assertRaisesRegex(ValueError, 'readiness does not match'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_lost_composition_and_admission_changes_require_manifest_update(self):
        self.by_id['balance-export-call-absent']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['balance-caller-absent']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['balance-lookup-absent']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['lookup-absent']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['lookup-raw-absent']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['dispatch']['proof_dependencies'].remove(self.nodes['method-new']['declaration'])
        with self.assertRaisesRegex(ValueError, 'lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['method-near_withdraw']['direct_sorry'] = False
        with self.assertRaisesRegex(ValueError, 'Admission frontier changed'):
            blueprint.classify(self.manifest, self.rows, self.audit)


if __name__ == '__main__':
    unittest.main()
