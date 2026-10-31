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
                              'not_ready': n['kind'] in ['verification_contract', 'admission'] or any(self.nodes[d]['kind'] == 'verification_contract' for d in n.get('required_type_dependencies', [])) or n['id'] in ['global', 'balance-outside-array-object-accepted', 'balance-outside-array-object-no-issue', 'balance-outside-array-accepted', 'balance-outside-array-no-issue', 'balance-other-accepted', 'balance-other-no-issue', 'balance-no-issue', 'balance-accepted', 'exported', 'dispatch', 'exported-clauses-assembly', 'global-composition', 'global-with-obligations', 'short-string-room', 'model-short-string-room', 'initial-memory-parser-room', 'initial-combined-parser-room', 'object-parser', 'array-parser', 'ignored-opening', 'storage', 'lookup-raw-absent', 'lookup-absent', 'balance-lookup-absent', 'balance-caller-absent', 'balance-export-call-absent', 'balance-export-call-and-copy', 'balance-export-format-zero', 'balance-export-call-copy-format', 'balance-export-through-expect', 'balance-export-through-return', 'balance-export-through-cleanup', 'balance-export-parsed-suffix', 'balance-export-state-read', 'balance-export-state-through-cleanup', 'balance-second-read-from-budget', 'balance-export-state-budget', 'balance-export-state-exact-gas', 'balance-room-after-state', 'balance-export-state-six-grows', 'borsh-vec-free-bound', 'borsh-bytes-reader-free-bound', 'borsh-bytes-free-bound', 'borsh-ft-free-bound', 'borsh-contract-reader-free-bound', 'borsh-contract-free-bound', 'state-read-free-bound', 'state-read-model-free-bound', 'balance-state-read-free-bound', 'balance-state-cleanup-free-bound', 'balance-next-budget-free-bound', 'balance-state-budget-free-bound', 'balance-state-exact-gas-free-bound', 'balance-state-six-grows-free-bound', 'parser-owned-resources', 'balance-parser-through-cleanup', 'parser-expose-heap', 'parser-fixed-resources', 'parser-fixed-through-cleanup', 'parser-public-through-cleanup', 'array-parser-copied-core', 'copied-parser-room', 'copied-parser-with-room', 'balance-copied-parser-through-cleanup', 'balance-input-deref-through-cleanup', 'balance-input-expect-through-cleanup', 'balance-input-through-cleanup', 'balance-input-setup-through-cleanup', 'balance-copied-absent-body', 'initial-input-copy-room', 'balance-copied-body-initial-room', 'balance-copied-absent-model-composition', 'balance-argument-length', 'balance-copied-body-gas-bound', 'receipt-input-register-bound', 'receipt-input-register-returns', 'no-input-mismatch-witness', 'input-read', 'method-ft_balance_of'], 'axioms': ['sorryAx'] if admission else ['propext'],
                              'type_dependencies': [], 'proof_dependencies': [], 'statement': 'test', 'type_hash': 1})
        self.by_id = {n['id']: row for n, row in zip(self.manifest['nodes'], self.rows)}
        for n in self.manifest['nodes']:
            self.by_id[n['id']]['proof_dependencies'] += [self.nodes[x]['declaration'] for x in n.get('required_proof_dependencies', [])]
        self.by_id['storage']['type_dependencies'] = [self.nodes['owned-room']['declaration']]
        self.by_id['lookup-raw-absent']['proof_dependencies'] = [self.nodes['storage-read-absent']['declaration']]
        self.by_id['lookup-absent']['proof_dependencies'] = [self.nodes['lookup-raw-absent']['declaration']]
        self.by_id['balance-lookup-absent']['proof_dependencies'] = [self.nodes['lookup-absent']['declaration']]
        self.by_id['balance-caller-absent']['proof_dependencies'] = [self.nodes['balance-lookup-absent']['declaration']]
        self.by_id['balance-export-call-absent']['proof_dependencies'] = [self.nodes['balance-caller-absent']['declaration']]
        self.by_id['balance-export-call-and-copy']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['balance-export-call-absent', 'balance-export-copy-zero']]
        self.by_id['balance-export-call-copy-format']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['balance-export-call-and-copy', 'balance-export-format-zero']]
        self.by_id['balance-export-through-expect']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['balance-export-call-copy-format', 'balance-export-expect-ok']]
        self.by_id['balance-export-through-return']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['balance-export-through-expect', 'balance-export-return-vec']]
        self.by_id['balance-export-through-cleanup']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['balance-export-through-return', 'balance-export-cleanup']]
        self.by_id['balance-export-parsed-suffix']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['balance-export-through-cleanup', 'balance-export-argument-copy']]
        self.by_id['balance-export-state-through-cleanup']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['balance-export-state-read', 'balance-export-parsed-suffix']]
        self.by_id['balance-export-state-budget']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['balance-export-state-through-cleanup', 'balance-second-read-from-budget']]
        self.by_id['balance-second-read-exact-gas']['proof_dependencies'] = [self.nodes['balance-next-read-cost-preserved']['declaration']]
        self.by_id['balance-export-state-exact-gas']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['balance-export-state-budget', 'balance-second-read-exact-gas']]
        self.by_id['balance-export-state-six-grows']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['balance-export-state-exact-gas', 'balance-room-after-state']]
        self.by_id['balance-absent-parser-plan']['axioms'].append('sorryAx')
        self.by_id['balance-outside-array-object-accepted']['axioms'].append('sorryAx')
        self.by_id['balance-outside-array-object-no-issue']['axioms'].append('sorryAx')
        self.by_id['balance-outside-array-accepted']['axioms'].append('sorryAx')
        self.by_id['balance-outside-array-no-issue']['axioms'].append('sorryAx')
        self.by_id['balance-other-accepted']['axioms'].append('sorryAx')
        self.by_id['balance-other-no-issue']['axioms'].append('sorryAx')
        self.by_id['balance-no-issue']['axioms'].append('sorryAx')
        self.by_id['balance-accepted']['axioms'].append('sorryAx')
        self.by_id['method-ft_balance_of']['axioms'].append('sorryAx')
        self.by_id['method-ft_balance_of']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['balance-no-issue', 'balance-accepted', 'balance-rejected']]
        self.by_id['global']['axioms'].append('sorryAx')
        self.by_id['global']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['exported', 'global-composition']]
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

    def test_key_reuse_and_input_domain_proofs_keep_remaining_frontier_visible(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        for node in ['balance-input-nonempty', 'scratch-reuse-budget', 'key-series-valid',
                     'key-series-input-budget', 'key-series-growth-count', 'string-work-sharp',
                     'key-argument-slice-gas', 'key-growth-count-v86']:
            self.assertEqual(result[node]['status'], 'Proven')
        for node in ['key-traced-reader', 'key-growth-reader', 'balance-accepted-input-bounds',
                     'absent-plan-input-composition', 'balance-absent-parser-plan']:
            self.assertEqual(result[node]['status'], 'Conditional')
            self.assertFalse(result[node]['direct_sorry'])
        for node in ['argument-limit-v86', 'pinned-arguments-limit', 'balance-absent-parser-cost',
                     'key-conditions', 'value-conditions', 'ignore-hyp']:
            self.assertEqual(result[node]['status'], 'Open')
        for source, caller, status in [('string-work-sharp', 'key-series-growth', 'Proven'),
                                       ('key-traced-reader', 'key-growth-reader', 'Conditional'),
                                       ('balance-input-nonempty', 'balance-accepted-input-bounds', 'Conditional'),
                                       ('absent-plan-input-composition', 'balance-absent-parser-plan', 'Conditional')]:
            self.assertIn({'id': caller, 'status': status}, result[source]['integrated_into'])
        self.assertEqual(result['global']['status'], 'Conditional')

    def test_key_argument_slice_cannot_drop_its_global_growth_ceiling(self):
        self.by_id['key-argument-slice-gas']['proof_dependencies'].remove(
            self.nodes['key-growth-count-v86']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_retained_key_charge_cannot_drop_sharper_string_work(self):
        self.by_id['key-series-growth']['proof_dependencies'].remove(
            self.nodes['string-work-sharp']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_key_series_budget_cannot_assume_its_trace_validity(self):
        self.by_id['key-series-input-budget']['proof_dependencies'].remove(
            self.nodes['key-series-valid']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_parser_plan_cannot_hide_pinned_argument_ceiling(self):
        self.by_id['balance-absent-parser-plan']['proof_dependencies'].remove(
            self.nodes['pinned-arguments-limit']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_scratch_budget_cannot_drop_evolving_allocator_walks(self):
        self.by_id['scratch-mixed-budget']['proof_dependencies'].remove(
            self.nodes['scratch-mixed-walks']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_mixed_scratch_composition_keeps_both_specializations_and_open_parser(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        for node in ['scratch-mixed-budget', 'scratch-append-mixed-valid',
                     'ignore-machine-trace-valid', 'ignore-machine-mixed-budget',
                     'ignore-machine-trace-budget']:
            self.assertEqual(result[node]['status'], 'Proven')
        for source, caller in [('scratch-mixed-budget', 'scratch-reuse-budget'),
                               ('scratch-mixed-budget', 'scratch-mixed-frame-budget'),
                               ('ignore-machine-trace-valid', 'ignore-machine-mixed-budget'),
                               ('ignore-machine-mixed-budget', 'ignore-machine-trace-budget')]:
            self.assertIn({'id': caller, 'status': 'Proven'}, result[source]['integrated_into'])
        for node in ['ignore-hyp', 'key-conditions', 'value-conditions', 'balance-absent-parser-cost']:
            self.assertEqual(result[node]['status'], 'Open')
        self.assertEqual(result['global']['status'], 'Conditional')

    def test_string_specialization_cannot_drop_mixed_validity(self):
        self.by_id['scratch-reuse-budget']['proof_dependencies'].remove(
            self.nodes['scratch-append-mixed-valid']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_mixed_value_budget_cannot_drop_actual_model_trace_validity(self):
        self.by_id['ignore-machine-mixed-budget']['proof_dependencies'].remove(
            self.nodes['ignore-machine-trace-valid']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_container_loop_composes_actual_phases_without_closing_ignore_hyp(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        for node in ['ignored-container-iteration', 'ignored-container-loop',
                     'ignored-container-phase', 'ignored-container-suffix', 'ignored-decoded-suffix']:
            self.assertEqual(result[node]['status'], 'Proven')
        for source, caller in [('ignored-closing', 'ignored-container-iteration'),
                               ('ignored-container-iteration', 'ignored-container-loop'),
                               ('ignored-container-loop', 'ignored-container-phase'),
                               ('ignored-container-phase', 'ignored-container-suffix'),
                               ('ignored-member', 'ignored-container-suffix'),
                               ('ignored-container-suffix', 'ignored-decoded-suffix'),
                               ('ignored-suffix-code', 'ignored-decoded-suffix')]:
            self.assertIn({'id': caller, 'status': 'Proven'}, result[source]['integrated_into'])
        for node in ['ignore-hyp', 'key-conditions', 'value-conditions', 'balance-absent-parser-cost']:
            self.assertEqual(result[node]['status'], 'Open')
        self.assertEqual(result['global']['status'], 'Conditional')

    def test_container_iteration_cannot_drop_nested_close_composition(self):
        self.by_id['ignored-container-iteration']['proof_dependencies'].remove(
            self.nodes['ignored-closing']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_decoded_suffix_cannot_drop_its_checked_bytecode_equality(self):
        self.by_id['ignored-decoded-suffix']['proof_dependencies'].remove(
            self.nodes['ignored-suffix-code']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_full_ignored_reader_stays_conditional_on_trace_room(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        for node in ['ignored-full-reader', 'ignored-traced-reader', 'ignored-colon-reader',
                     'ignored-value-loop', 'ignored-hyp-instance', 'ignored-object-composition']:
            self.assertEqual(result[node]['status'], 'Conditional')
            self.assertFalse(result[node]['direct_sorry'])
        for node in ['ignored-trace-room', 'ignored-member-conditions', 'ignore-hyp',
                     'key-conditions', 'value-conditions']:
            self.assertEqual(result[node]['status'], 'Open')
        for source, caller in [('ignored-full-reader', 'ignored-traced-reader'),
                               ('ignored-colon-reader', 'ignored-hyp-instance'),
                               ('ignored-hyp-instance', 'ignored-object-composition'),
                               ('object-parser', 'ignored-object-composition')]:
            self.assertIn({'id': caller, 'status': 'Conditional'}, result[source]['integrated_into'])
        self.assertEqual(result['global']['status'], 'Conditional')

    def test_full_reader_cannot_drop_actual_main_composition(self):
        self.by_id['ignored-full-reader']['proof_dependencies'].remove(
            self.nodes['ignored-main']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_object_reader_cannot_hide_reachable_member_conditions(self):
        self.by_id['ignored-object-composition']['type_dependencies'].remove(
            self.nodes['ignored-member-conditions']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Expected verification hypotheses missing'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_concrete_reader_room_keeps_whole_object_obligations_open(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        for node in ['ignored-reader-pages', 'ignored-reader-v86', 'ignored-colon-v86',
                     'ignored-capacity-v86', 'ignored-pages-v86', 'ignored-heap-pages']:
            self.assertEqual(result[node]['status'], 'Proven')
            self.assertFalse(result[node]['direct_sorry'])
        for node in ['ignored-reachable-hyp', 'ignored-reachable-object', 'global', 'method-ft_balance_of']:
            self.assertEqual(result[node]['status'], 'Conditional')
        for node in ['ignored-reachable-conditions', 'ignore-hyp', 'key-conditions', 'value-conditions']:
            self.assertEqual(result[node]['status'], 'Open')
        for source, caller, status in [('ignored-reader-pages', 'ignored-reader-v86', 'Proven'),
                                       ('ignored-reader-v86', 'ignored-colon-v86', 'Proven'),
                                       ('ignored-colon-v86', 'ignored-reachable-hyp', 'Conditional'),
                                       ('ignored-reachable-hyp', 'ignored-reachable-object', 'Conditional')]:
            self.assertIn({'id': caller, 'status': status}, result[source]['integrated_into'])

    def test_page_budget_reader_cannot_drop_its_room_constructor(self):
        self.by_id['ignored-reader-pages']['proof_dependencies'].remove(
            self.nodes['ignored-room-pages']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_physical_object_caller_cannot_hide_reachable_conditions(self):
        self.by_id['ignored-reachable-object']['type_dependencies'].remove(
            self.nodes['ignored-reachable-conditions']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Expected verification hypotheses missing'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_actual_object_key_coverage_keeps_full_parser_open(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        for node in ['object-key-path', 'object-key-cover', 'object-key-models', 'object-key-gas', 'object-key-opening']:
            self.assertEqual(result[node]['status'], 'Proven')
        for node in ['object-key-path', 'object-key-cover', 'object-key-models', 'key-argument-slice-gas']:
            self.assertIn({'id': 'object-key-gas', 'status': 'Proven'}, result[node]['integrated_into'])
        self.assertEqual(result['ignored-reachable-conditions']['status'], 'Open')
        self.assertEqual(result['global']['status'], 'Conditional')

    def test_key_gas_cannot_drop_actual_input_coverage(self):
        self.by_id['object-key-gas']['proof_dependencies'].remove(
            self.nodes['object-key-cover']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_precise_closing_and_exact_cost_keep_reader_obligations_visible(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        for node in ['object-key-hyp', 'object-value-hyp', 'object-close-hyp', 'object-closing-conditions',
                     'ignore-hyp', 'key-conditions', 'value-conditions', 'ignored-reachable-conditions']:
            self.assertEqual(result[node]['status'], 'Open')
        for node in ['object-loop-closing', 'object-loop-monotone', 'object-model-closing',
                     'ignored-object-closing', 'ignored-object-key-cost', 'object-parser', 'global']:
            self.assertEqual(result[node]['status'], 'Conditional')
            self.assertFalse(result[node]['direct_sorry'])
        for node in ['object-key-fuel', 'object-key-component', 'object-key-cost-path', 'object-cost-key-component']:
            self.assertEqual(result[node]['status'], 'Proven')
        self.assertIn({'id': 'ignored-object-key-cost', 'status': 'Conditional'},
                      result['object-cost-key-component']['integrated_into'])
        self.assertIn({'id': 'object-parser', 'status': 'Conditional'},
                      result['object-model-closing']['integrated_into'])

    def test_legacy_model_api_cannot_drop_closing_composition(self):
        self.by_id['object-parser']['proof_dependencies'].remove(
            self.nodes['object-model-closing']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_physical_object_cannot_hide_precise_closing_condition(self):
        self.by_id['ignored-object-closing']['type_dependencies'].remove(
            self.nodes['object-closing-conditions']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Expected verification hypotheses missing'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_wasm_key_split_cannot_drop_exact_cost_equation(self):
        self.by_id['ignored-object-key-cost']['proof_dependencies'].remove(
            self.nodes['object-cost-key-component']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_concrete_ledger_closes_state_but_keeps_room_gas_setup_open(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        for node in ['mixed-growth-v86', 'mixed-pages-v86', 'mixed-loop-pages', 'mixed-account-page',
                     'object-ledger-ceiling', 'object-ledger-segment', 'object-ledger-ignored-state', 'object-ledger-member']:
            self.assertEqual(result[node]['status'], 'Proven')
        for node in ['object-ledger-key', 'object-ledger-value', 'object-ledger-ignore',
                     'object-ledger-reader', 'object-ledger-initial-reader', 'global']:
            self.assertEqual(result[node]['status'], 'Conditional')
            self.assertFalse(result[node]['direct_sorry'])
        for node in ['object-ledger-setup', 'object-key-room-charges', 'object-value-room-charges',
                     'object-ignore-charges', 'key-conditions', 'value-conditions', 'ignore-hyp']:
            self.assertEqual(result[node]['status'], 'Open')
        for source in ['object-ledger-key', 'object-ledger-value', 'object-ledger-ignore', 'object-ledger-closing']:
            self.assertIn({'id': 'object-ledger-reader', 'status': 'Conditional'}, result[source]['integrated_into'])
        self.assertIn({'id': 'object-ledger-initial-reader', 'status': 'Conditional'},
                      result['object-ledger-member']['integrated_into'])

    def test_ignored_ledger_cannot_drop_actual_heap_ceiling(self):
        self.by_id['object-ledger-ignore']['proof_dependencies'].remove(
            self.nodes['object-ledger-ceiling']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_initial_ledger_reader_cannot_assume_member_initialization(self):
        self.by_id['object-ledger-initial-reader']['proof_dependencies'].remove(
            self.nodes['object-ledger-member']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_object_ledger_cannot_drop_value_state_composition(self):
        self.by_id['object-ledger-reader']['proof_dependencies'].remove(
            self.nodes['object-ledger-value']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_ledger_cannot_hide_remaining_ignored_gas_obligation(self):
        self.by_id['object-ledger-reader']['type_dependencies'].remove(
            self.nodes['object-ignore-charges']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Expected verification hypotheses missing'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_general_ledger_reaches_actual_receipt_but_keeps_budget_open(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        for node in ['ledger-wrapper-generic', 'ledger-scratch-cleanup', 'ledger-final-bounds',
                     'ledger-container-code', 'ledger-parser-code', 'ledger-input-bounds']:
            self.assertEqual(result[node]['status'], 'Proven')
        for node in ['ledger-key-wrapper', 'ledger-cost-wrapper', 'ledger-from-trait',
                     'ledger-from-slice', 'ledger-result-room', 'ledger-from-slice-room',
                     'ledger-parser-call', 'ledger-parser-family', 'ledger-deployed-provider',
                     'ledger-provider-plan', 'ledger-receipt']:
            self.assertEqual(result[node]['status'], 'Conditional')
            self.assertFalse(result[node]['direct_sorry'])
        for node in ['object-key-room-charges', 'object-value-room-charges', 'object-ignore-charges',
                     'provider-model-budget', 'ignore-hyp', 'key-conditions', 'value-conditions']:
            self.assertEqual(result[node]['status'], 'Open')
        for source in ['ledger-provider-plan', 'provider-plan-receipt-initial']:
            self.assertIn({'id': 'ledger-receipt', 'status': 'Conditional'}, result[source]['integrated_into'])

    def test_general_ledger_receipt_cannot_hide_original_model_budget(self):
        self.by_id['ledger-receipt']['type_dependencies'].remove(self.nodes['provider-model-budget']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Expected verification hypotheses missing'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_general_ledger_caller_cannot_skip_actual_scratch_cleanup(self):
        self.by_id['ledger-from-trait']['proof_dependencies'].remove(self.nodes['ledger-scratch-cleanup']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_general_ledger_family_cannot_assume_initial_setup(self):
        self.by_id['ledger-parser-family']['proof_dependencies'].remove(self.nodes['ledger-input-bounds']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_general_ledger_provider_cannot_assume_function_code(self):
        self.by_id['ledger-deployed-provider']['proof_dependencies'].remove(self.nodes['ledger-parser-code']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_reader_room_is_constructed_and_only_gas_remains_in_receipt(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        for node in ['string-room-trace', 'ledger-reader-pages']:
            self.assertEqual(result[node]['status'], 'Proven')
        for node in ['string-page-reserve', 'string-page-run', 'string-any-short', 'ledger-account-room',
                     'ledger-value-gas-charges', 'ledger-key-gas-charges', 'ledger-key-room', 'ledger-gas-family',
                     'ledger-gas-provider', 'ledger-gas-plan', 'ledger-gas-receipt']:
            self.assertEqual(result[node]['status'], 'Conditional')
            self.assertFalse(result[node]['direct_sorry'])
        for node in ['object-key-gas-obligation', 'object-value-gas', 'object-ignore-charges', 'provider-model-budget',
                     'ignore-hyp', 'key-conditions', 'value-conditions']:
            self.assertEqual(result[node]['status'], 'Open')
        for node in ['ledger-gas-family', 'ledger-gas-provider', 'ledger-gas-plan', 'ledger-gas-receipt']:
            self.assertFalse({'object-key-room-charges', 'object-value-room-charges', 'string-room',
                              'owned-room', 'object-ledger-setup'} & set(result[node]['type_edges']))
        for source in ['ledger-value-gas-charges', 'ledger-key-gas-charges']:
            self.assertIn({'id': 'ledger-gas-family', 'status': 'Conditional'}, result[source]['integrated_into'])

    def test_concrete_key_room_cannot_drop_copied_trace_identity(self):
        self.by_id['ledger-key-room']['proof_dependencies'].remove(self.nodes['string-room-trace']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_gas_family_cannot_assume_account_reader_room(self):
        self.by_id['ledger-gas-family']['proof_dependencies'].remove(self.nodes['ledger-value-gas-charges']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_gas_receipt_cannot_hide_remaining_key_gas(self):
        self.by_id['ledger-gas-receipt']['type_dependencies'].remove(self.nodes['object-key-gas-obligation']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Expected verification hypotheses missing'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_account_room_cannot_skip_retained_page_bound(self):
        self.by_id['ledger-account-room']['proof_dependencies'].remove(self.nodes['ledger-reader-pages']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_duplicate_node_id_is_rejected_before_status_collapse(self):
        self.manifest['nodes'][-1]['id'] = self.manifest['nodes'][0]['id']
        with self.assertRaisesRegex(ValueError, 'Duplicate frontier id'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_duplicate_blueprint_label_is_rejected(self):
        self.manifest['nodes'][-1]['label'] = self.manifest['nodes'][0]['label']
        self.rows[-1]['blueprint_label'] = self.rows[0]['blueprint_label']
        with self.assertRaisesRegex(ValueError, 'Duplicate frontier label'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_duplicate_frontier_declaration_is_rejected(self):
        self.manifest['nodes'].append(copy.deepcopy(self.manifest['nodes'][-1]))
        self.manifest['nodes'][-1]['id'] += '-duplicate'
        self.manifest['nodes'][-1]['label'] += '-duplicate'
        with self.assertRaisesRegex(ValueError, 'Duplicate frontier declaration'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_duplicate_lean_export_row_is_rejected(self):
        self.rows.append(copy.deepcopy(self.rows[-1]))
        with self.assertRaisesRegex(ValueError, 'Duplicate Lean declaration'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_precise_key_cost_reaches_receipt_without_claiming_gas_complete(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        for node in ['precise-key-cost-compat', 'precise-key-work']:
            self.assertEqual(result[node]['status'], 'Proven')
        for node in ['precise-key-conditions', 'precise-key-gas', 'object-value-gas',
                     'object-ignore-charges', 'provider-model-budget', 'ignore-hyp',
                     'key-conditions', 'value-conditions']:
            self.assertEqual(result[node]['status'], 'Open')
        for node in ['precise-key-reader', 'precise-next-key-reader', 'precise-key-hyp',
                     'precise-object-closing', 'precise-ignored-object', 'precise-ledger-keys',
                     'precise-ledger-wrapper', 'precise-from-trait', 'precise-from-slice',
                     'precise-from-slice-room', 'precise-parser-call', 'precise-parser-family',
                     'precise-deployed-provider', 'precise-provider-plan', 'precise-receipt',
                     'precise-key-conditions-compat', 'precise-key-gas-compat']:
            self.assertEqual(result[node]['status'], 'Conditional')
            self.assertFalse(result[node]['direct_sorry'])
        for node in ['precise-parser-family', 'precise-deployed-provider', 'precise-provider-plan', 'precise-receipt']:
            self.assertNotIn('object-key-gas-obligation', result[node]['type_edges'])
            self.assertNotIn('key-conditions', result[node]['type_edges'])
            self.assertNotIn('object-key-room-charges', result[node]['type_edges'])
        self.assertIn({'id': 'precise-receipt', 'status': 'Conditional'}, result['precise-provider-plan']['integrated_into'])

    def test_precise_key_hyp_cannot_skip_actual_next_key_code(self):
        self.by_id['precise-key-hyp']['proof_dependencies'].remove(self.nodes['precise-next-key-reader']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_precise_object_model_cannot_restore_legacy_key_cost(self):
        self.by_id['precise-object-closing']['proof_dependencies'].remove(self.nodes['precise-key-hyp']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_precise_receipt_cannot_hide_original_model_budget(self):
        self.by_id['precise-receipt']['type_dependencies'].remove(self.nodes['provider-model-budget']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Expected verification hypotheses missing'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_precise_compatibility_cannot_skip_cost_domination(self):
        self.by_id['precise-key-cost-compat']['proof_dependencies'].remove(self.nodes['key-traced-cost-domination']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_phase_loop_is_integrated_without_closing_reader_obligations(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        for node in ['phase-key-hyp', 'phase-value-hyp', 'phase-ignore-hyp', 'phase-close-hyp',
                     'key-conditions', 'value-conditions', 'ignore-hyp', 'precise-key-gas',
                     'object-value-gas', 'object-ignore-charges', 'provider-model-budget']:
            self.assertEqual(result[node]['status'], 'Open')
        for node in ['phase-object-loop', 'phase-key-compat', 'phase-value-compat',
                     'phase-ignore-compat', 'phase-close-compat', 'object-loop-closing',
                     'precise-object-closing', 'precise-receipt']:
            self.assertEqual(result[node]['status'], 'Conditional')
            self.assertFalse(result[node]['direct_sorry'])
        for node in ['prefix-value-model', 'prefix-models', 'prefix-ledger', 'prefix-initial',
                     'prefix-first-exact', 'prefix-pending-key']:
            self.assertEqual(result[node]['status'], 'Proven')
        for node in ['phase-object-loop', 'phase-key-compat', 'phase-value-compat',
                     'phase-ignore-compat', 'phase-close-compat']:
            self.assertIn({'id': 'object-loop-closing', 'status': 'Conditional'}, result[node]['integrated_into'])
        self.assertIn({'id': 'precise-object-closing', 'status': 'Conditional'}, result['object-loop-closing']['integrated_into'])

    def test_old_loop_cannot_skip_actual_phase_composition(self):
        self.by_id['object-loop-closing']['proof_dependencies'].remove(self.nodes['phase-object-loop']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_old_loop_cannot_skip_phase_ignore_instantiation(self):
        self.by_id['object-loop-closing']['proof_dependencies'].remove(self.nodes['phase-ignore-compat']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_prefix_ledger_cannot_skip_actual_segment_models(self):
        self.by_id['prefix-ledger']['proof_dependencies'].remove(self.nodes['prefix-models']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_actual_code_provider_reaches_global_assemblies_without_closing_the_plan(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        for node in ['deployed-parser-provider', 'provider-model-budget', 'absent-parser-plan',
                     'pinned-arguments-limit', 'balance-absent-parser-cost', 'balance-other-state-accepted',
                     'balance-other-input-state-safety', 'ignore-hyp', 'key-conditions', 'value-conditions']:
            self.assertEqual(result[node]['status'], 'Open')
        for node in ['provider-runs', 'provider-plan-receipt-initial',
                     'balance-outside-array-object-accepted', 'balance-outside-array-object-no-issue',
                     'method-ft_balance_of', 'global']:
            self.assertEqual(result[node]['status'], 'Conditional')
        for node in ['balance-outside-array-object-accepted', 'balance-outside-array-object-no-issue']:
            self.assertFalse(result[node]['direct_sorry'])
            self.assertIn({'id': node, 'status': 'Conditional'},
                          result['provider-plan-receipt-initial']['integrated_into'])
        self.assertEqual(result['balance-object-case-refinement']['status'], 'Proven')
        self.assertIn({'id': 'balance-object-case-refinement', 'status': 'Proven'},
                      result['object-provider-plan']['integrated_into'])

    def test_provider_entry_cannot_lose_actual_instantiated_store(self):
        self.by_id['provider-entry-adequacy']['proof_dependencies'].remove(
            self.nodes['provider-initial-store']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_top_accepted_split_cannot_hide_the_unproved_parser_plan(self):
        self.by_id['balance-outside-array-object-accepted']['proof_dependencies'].remove(
            self.nodes['balance-absent-parser-plan']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_provider_receipt_cannot_hide_the_original_model_budget(self):
        self.by_id['provider-receipt-initial']['type_dependencies'].remove(
            self.nodes['provider-model-budget']['declaration'])
        with self.assertRaisesRegex(ValueError, 'readiness|verification hypotheses'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_closed_object_receipt_cannot_drop_its_concrete_parser_plan(self):
        self.by_id['balance-object-case-refinement']['proof_dependencies'].remove(
            self.nodes['object-provider-plan']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_uniform_parser_family_is_instantiated_without_closing_the_general_contract(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        self.assertEqual(result['parser-family']['status'], 'Open')
        self.assertEqual(result['object-parser-family-instance']['status'], 'Conditional')
        self.assertEqual(result['provider-absent-body']['status'], 'Conditional')
        self.assertEqual(result['balance-object-case-refinement']['status'], 'Proven')
        for source in ['provider-absent-body', 'object-parser-family-instance']:
            self.assertIn({'id': 'object-absent-body', 'status': 'Conditional'},
                          result[source]['integrated_into'])
        for node in ['ignore-hyp', 'key-conditions', 'value-conditions']:
            self.assertEqual(result[node]['status'], 'Open')
        self.assertEqual(result['global']['status'], 'Conditional')

    def test_object_body_cannot_lose_uniform_provider_instantiation(self):
        self.by_id['object-absent-body']['proof_dependencies'].remove(
            self.nodes['object-parser-family-instance']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_provider_body_cannot_hide_its_parser_family(self):
        self.by_id['provider-absent-body']['type_dependencies'].remove(
            self.nodes['parser-family']['declaration'])
        with self.assertRaisesRegex(ValueError, 'readiness|verification hypotheses'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_object_receipt_case_is_integrated_without_hiding_general_obligations(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        self.assertEqual(result['balance-object-case-refinement']['status'], 'Proven')
        for source, caller in [('balance-object-case-accepted', 'balance-outside-array-accepted'),
                               ('balance-object-case-safety', 'balance-outside-array-no-issue')]:
            self.assertIn({'id': caller, 'status': 'Conditional'}, result[source]['integrated_into'])
        for node in ['pinned-arguments-limit', 'balance-absent-parser-cost', 'balance-other-state-accepted', 'balance-other-input-state-safety',
                     'ignore-hyp', 'key-conditions', 'value-conditions', 'parser-call-contract']:
            self.assertEqual(result[node]['status'], 'Open')
        for node in ['balance-outside-array-accepted', 'balance-outside-array-no-issue',
                     'method-ft_balance_of', 'global']:
            self.assertEqual(result[node]['status'], 'Conditional')

    def test_object_receipt_cannot_lose_full_model_gas_instantiation(self):
        self.by_id['object-provider-plan']['proof_dependencies'].remove(
            self.nodes['object-total-model-gas']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_object_adequacy_cannot_lose_actual_store_resources(self):
        self.by_id['object-entry-adequacy']['proof_dependencies'].remove(
            self.nodes['object-initial-store']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_outside_array_assembly_cannot_hide_object_case_integration(self):
        self.by_id['balance-outside-array-accepted']['proof_dependencies'].remove(
            self.nodes['balance-object-case-accepted']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_object_instances_do_not_discharge_general_frontier(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        self.assertEqual(result['object-noesc-loop-initial']['status'], 'Proven')
        for node in ['object-noesc-keys-before', 'object-noesc-keys-saved', 'object-noesc-values',
                     'object-shallow-ignore', 'object-noesc-initial-room', 'object-noesc-loop']:
            self.assertEqual(result[node]['status'], 'Conditional')
        for node in ['ignore-hyp', 'key-conditions', 'value-conditions']:
            self.assertEqual(result[node]['status'], 'Open')
        self.assertIn({'id': 'object-noesc-loop-initial', 'status': 'Proven'},
                      result['object-noesc-loop']['integrated_into'])
        self.assertEqual(result['method-ft_balance_of']['status'], 'Conditional')
        self.assertEqual(result['global']['status'], 'Conditional')
        self.assertIn({'id': 'object-wrapper-reader', 'status': 'Proven'},
                      result['object-noesc-loop-initial']['integrated_into'])

    def test_object_loop_cannot_lose_concrete_reader_composition(self):
        self.by_id['object-noesc-loop']['proof_dependencies'].remove(
            self.nodes['object-noesc-values']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_object_loop_cannot_lose_numerical_room_instantiation(self):
        self.by_id['object-noesc-loop-initial']['proof_dependencies'].remove(
            self.nodes['object-noesc-initial-room']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_broader_array_case_is_integrated_and_legacy_statements_specialize_it(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        self.assertEqual(result['balance-array-case-refinement']['status'], 'Proven')
        self.assertIn({'id': 'balance-other-accepted', 'status': 'Conditional'},
                      result['balance-array-case-accepted']['integrated_into'])
        self.assertIn({'id': 'balance-other-no-issue', 'status': 'Conditional'},
                      result['balance-array-case-safety']['integrated_into'])
        self.assertIn('balance-array-case-refinement',
                      result['balance-copied-case-refinement']['proof_edges'])
        for node in ['pinned-arguments-limit', 'balance-absent-parser-cost', 'balance-other-state-accepted', 'balance-other-input-state-safety',
                     'ignore-hyp', 'key-conditions', 'value-conditions']:
            self.assertEqual(result[node]['status'], 'Open')
        for node in ['balance-other-accepted', 'balance-other-no-issue', 'balance-accepted',
                     'balance-no-issue', 'method-ft_balance_of', 'global']:
            self.assertEqual(result[node]['status'], 'Conditional')

    def test_array_case_cannot_lose_resource_or_gas_instantiation(self):
        self.by_id['balance-array-case-refinement']['proof_dependencies'].remove(
            self.nodes['balance-total-model-gas']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_remaining_case_cannot_hide_borrowed_string_integration(self):
        self.by_id['balance-other-accepted']['proof_dependencies'].remove(
            self.nodes['balance-array-case-accepted']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_completed_case_is_integrated_without_hiding_other_cases(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        self.assertEqual(result['balance-copied-case-refinement']['status'], 'Proven')
        self.assertEqual(result['balance-copied-case-accepted']['status'], 'Proven')
        self.assertIn({'id': 'balance-accepted', 'status': 'Conditional'},
                      result['balance-copied-case-accepted']['integrated_into'])
        self.assertEqual(result['balance-other-accepted']['status'], 'Conditional')
        for node in ['balance-no-issue', 'balance-accepted', 'method-ft_balance_of', 'global']:
            self.assertEqual(result[node]['status'], 'Conditional')
        for node in ['ignore-hyp', 'key-conditions', 'value-conditions']:
            self.assertEqual(result[node]['status'], 'Open')

    def test_safety_assembly_integrates_the_completed_case(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        self.assertEqual(result['balance-copied-case-safety']['status'], 'Proven')
        self.assertEqual(result['balance-other-no-issue']['status'], 'Conditional')
        self.assertIn({'id': 'balance-no-issue', 'status': 'Conditional'},
                      result['balance-copied-case-safety']['integrated_into'])
        self.by_id['balance-no-issue']['proof_dependencies'].remove(
            self.nodes['balance-copied-case-safety']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_accepted_assembly_cannot_lose_completed_case(self):
        self.by_id['balance-accepted']['proof_dependencies'].remove(
            self.nodes['balance-copied-case-accepted']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_completed_case_cannot_lose_model_gas(self):
        self.by_id['balance-copied-case-refinement']['proof_dependencies'].remove(
            self.nodes['balance-array-case-refinement']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_initial_entry_composition_keeps_ending_run_scope(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        self.assertEqual(result['balance-entry-host']['status'], 'Proven')
        self.assertIn({'id': 'balance-array-entry-adequacy', 'status': 'Proven'},
                      result['balance-initial-start']['integrated_into'])
        self.assertIn({'id': 'balance-entry-host', 'status': 'Proven'},
                      result['balance-end-observations']['integrated_into'])
        self.assertNotIn('balance-accepted',
                         [n['id'] for n in result['balance-entry-host']['integrated_into']])
        for node in ['pinned-arguments-limit', 'balance-absent-parser-cost', 'balance-other-state-accepted', 'balance-other-input-state-safety', 'balance-rejected']:
            self.assertEqual(result[node]['status'], 'Open')
        self.assertEqual(result['method-ft_balance_of']['status'], 'Conditional')
        self.assertEqual(result['global']['status'], 'Conditional')

    def test_initial_entry_cannot_lose_linear_resource_composition(self):
        self.by_id['balance-initial-start-split']['proof_dependencies'].remove(
            self.nodes['balance-initial-table']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_initial_entry_cannot_hide_parser_verification_hypotheses(self):
        self.by_id['balance-entry-host']['type_dependencies'].append(
            self.nodes['ignore-hyp']['declaration'])
        with self.assertRaisesRegex(ValueError, 'readiness does not match'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_store_code_composition_preserves_external_frontier(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        self.assertEqual(result['balance-copied-body-store-code']['status'], 'Proven')
        self.assertIn({'id': 'balance-copied-body-store-code', 'status': 'Proven'},
                      result['balance-code-assembled']['integrated_into'])
        self.assertEqual(result['balance-code-start']['status'], 'Proven')
        self.assertNotIn('balance-accepted',
                         [n['id'] for n in result['balance-code-start']['integrated_into']])
        self.assertEqual(result['balance-accepted']['status'], 'Conditional')
        self.assertEqual(result['method-ft_balance_of']['status'], 'Conditional')
        self.assertEqual(result['global']['status'], 'Conditional')

    def test_store_code_cannot_claim_integration_without_checked_composition(self):
        self.by_id['balance-copied-body-store-code']['proof_dependencies'].remove(
            self.nodes['balance-code-assembled']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_initial_memory_discharges_this_parser_room_instance(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        self.assertEqual(result['balance-copied-body-initial-memory']['status'], 'Proven')
        self.assertNotIn('string-room', result['balance-copied-body-initial-memory']['type_edges'])
        self.assertNotIn('lookup-heap-room', result['balance-copied-body-initial-memory']['type_edges'])
        self.assertIn({'id': 'balance-array-body-initial-memory', 'status': 'Proven'},
                      result['initial-memory-parser-room']['integrated_into'])
        self.assertEqual(result['string-room']['status'], 'Open')
        self.assertEqual(result['accept-parser']['status'], 'Open')
        self.assertEqual(result['method-ft_balance_of']['status'], 'Conditional')
        self.assertEqual(result['global']['status'], 'Conditional')

    def test_initial_memory_cannot_hide_a_remaining_room_hypothesis(self):
        self.by_id['balance-copied-body-initial-memory']['type_dependencies'].append(
            self.nodes['string-room']['declaration'])
        with self.assertRaisesRegex(ValueError, 'readiness does not match'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['balance-array-body-initial-memory']['proof_dependencies'].remove(
            self.nodes['initial-memory-parser-room']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_admission_free_global_composition_keeps_contracts_open(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        self.assertEqual(result['exported-clauses']['status'], 'Open')
        for node in ['exported-clauses-assembly', 'global-composition', 'global-with-obligations']:
            self.assertEqual(result[node]['status'], 'Conditional')
            self.assertNotIn('sorryAx', result[node]['axioms'])
        self.assertIn({'id': 'global', 'status': 'Conditional'}, result['global-composition']['integrated_into'])

    def test_conditional_composition_and_unresolved_hypotheses_are_visible(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        self.assertEqual(result['global']['status'], 'Conditional')
        self.assertEqual(result['context-wf-with-args']['status'], 'Proven')
        self.assertEqual(result['context-wf-bounded-args']['status'], 'Proven')
        self.assertEqual(result['input-register-trap']['status'], 'Proven')
        self.assertEqual(result['input-panic-obstruction']['status'], 'Proven')
        self.assertEqual(result['validated-actions-arguments']['status'], 'Proven')
        self.assertEqual(result['protocol-input-limit-order']['status'], 'Open')
        self.assertEqual(result['receipt-input-register-returns']['status'], 'Conditional')
        self.assertEqual(result['receipt-input-register-bound']['status'], 'Conditional')
        self.assertEqual(result['no-input-mismatch-witness']['status'], 'Conditional')
        self.assertEqual(result['dispatch']['status'], 'Conditional')
        self.assertEqual(result['object-parser']['status'], 'Conditional')
        self.assertEqual(result['ignored-opening']['status'], 'Conditional')
        self.assertEqual(result['array-parser']['status'], 'Conditional')
        self.assertEqual(result['storage']['status'], 'Conditional')
        self.assertEqual(result['input-register-room']['status'], 'Open')
        self.assertEqual(result['input-read']['status'], 'Conditional')
        self.assertEqual(result['balance-method-prologue']['status'], 'Proven')
        self.assertEqual(result['balance-input-expect']['status'], 'Proven')
        self.assertEqual(result['balance-input-deref-setup']['status'], 'Proven')
        self.assertEqual(result['balance-copied-absent-body']['status'], 'Conditional')
        self.assertEqual(result['initial-input-copy-room']['status'], 'Conditional')
        self.assertEqual(result['balance-copied-body-initial-room']['status'], 'Conditional')
        self.assertEqual(result['ft-balance-absent-model']['status'], 'Proven')
        self.assertEqual(result['balance-copied-absent-model-composition']['status'], 'Conditional')
        self.assertEqual(result['protocol-burn-limit']['status'], 'Open')
        self.assertEqual(result['balance-argument-charge']['status'], 'Proven')
        self.assertEqual(result['balance-argument-length']['status'], 'Conditional')
        self.assertEqual(result['balance-copied-body-gas-bound']['status'], 'Conditional')
        self.assertNotIn('input-register-room', self.nodes['balance-copied-body-initial-room']['required_type_dependencies'])
        self.assertNotIn('owned-room', self.nodes['balance-copied-body-initial-room']['required_type_dependencies'])
        self.assertEqual(result['balance-copied-parser-through-cleanup']['status'], 'Conditional')
        self.assertEqual(result['copied-parser-with-room']['status'], 'Conditional')
        self.assertEqual(result['parser-post-budget']['status'], 'Open')
        self.assertEqual(result['parser-fixed-result']['status'], 'Open')
        self.assertEqual(result['parser-public-through-cleanup']['status'], 'Conditional')
        self.assertEqual(result['parser-owned-result']['status'], 'Open')
        self.assertEqual(result['parser-owned-resources']['status'], 'Conditional')
        self.assertEqual(result['balance-parser-handoff']['status'], 'Proven')
        self.assertEqual(result['balance-parser-through-cleanup']['status'], 'Conditional')
        self.assertEqual(result['balance-next-read-free-bound']['status'], 'Open')
        self.assertEqual(result['balance-next-gas-free-bound']['status'], 'Open')
        self.assertEqual(result['balance-next-exact-gas-free-bound']['status'], 'Proven')
        self.assertEqual(result['balance-state-six-grows-free-bound']['status'], 'Conditional')
        self.assertEqual(result['state-entry-free-bound']['status'], 'Open')
        self.assertEqual(result['state-read-free-bound']['status'], 'Conditional')
        self.assertEqual(result['state-read-model-free-bound']['status'], 'Conditional')
        self.assertEqual(result['balance-state-entry']['status'], 'Open')
        self.assertEqual(result['balance-second-read']['status'], 'Open')
        self.assertEqual(result['balance-second-read-gas']['status'], 'Open')
        self.assertEqual(result['balance-second-read-from-budget']['status'], 'Conditional')
        self.assertEqual(result['balance-export-state-budget']['status'], 'Conditional')
        self.assertEqual(result['balance-second-read-exact-gas']['status'], 'Proven')
        self.assertEqual(result['balance-export-state-exact-gas']['status'], 'Conditional')
        self.assertEqual(result['balance-room-after-state']['status'], 'Conditional')
        self.assertEqual(result['balance-export-state-six-grows']['status'], 'Conditional')
        self.assertNotIn('owned-room', result['balance-export-state-six-grows']['type_edges'])
        self.assertNotIn('balance-second-read-gas', result['balance-export-state-exact-gas']['type_edges'])
        self.assertEqual(result['balance-export-state-read']['status'], 'Conditional')
        self.assertEqual(result['balance-export-state-through-cleanup']['status'], 'Conditional')
        self.assertIn({'id': 'balance-export-state-through-cleanup', 'status': 'Conditional'}, result['balance-export-parsed-suffix']['integrated_into'])
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
        self.by_id['balance-export-state-six-grows']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['balance-export-state-exact-gas']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['balance-export-state-budget']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['balance-export-state-through-cleanup']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['balance-export-parsed-suffix']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['balance-export-through-cleanup']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['balance-export-through-return']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['balance-export-through-expect']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['balance-export-call-copy-format']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['balance-export-call-and-copy']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
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




class PublishConfigurationTests(unittest.TestCase):
    def test_publishing_requires_an_explicit_endpoint(self):
        import contextlib
        import io
        from unittest.mock import patch
        with patch.object(blueprint, 'DEFAULT_URL', None), \
                patch.object(sys, 'argv', ['wnear_blueprint', '--publish']), \
                contextlib.redirect_stderr(io.StringIO()) as error:
            with self.assertRaises(SystemExit) as exit:
                blueprint.main()
        self.assertEqual(exit.exception.code, 2)
        self.assertIn('BLUEPRINT_BASE_URL', error.getvalue())

    def test_watcher_persists_the_configured_endpoint_and_destination(self):
        import plistlib
        import subprocess
        import tempfile
        from unittest.mock import patch
        with tempfile.TemporaryDirectory() as directory:
            home = Path(directory)
            destination = home / 'publish'
            url = 'https://example.com/w-near/'
            with patch.object(Path, 'home', return_value=home), \
                    patch.object(blueprint.subprocess, 'run', return_value=subprocess.CompletedProcess([], 0)):
                blueprint.install_watch(destination, url)
            config = plistlib.loads((home / 'Library/LaunchAgents/com.safe-near.wnear-blueprint-watch.plist').read_bytes())
            arguments = config['ProgramArguments']
            self.assertEqual(arguments[arguments.index('--url') + 1], url)
            self.assertEqual(arguments[arguments.index('--destination') + 1], str(destination))


if __name__ == '__main__':
    unittest.main()
