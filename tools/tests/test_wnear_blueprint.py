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

    def test_actual_code_provider_reaches_global_assemblies_without_closing_the_plan(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        for node in ['deployed-parser-provider', 'provider-model-budget', 'absent-parser-plan',
                     'balance-absent-parser-plan', 'balance-other-state-accepted',
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
        for node in ['balance-absent-parser-plan', 'balance-other-state-accepted', 'balance-other-input-state-safety',
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
        for node in ['balance-absent-parser-plan', 'balance-other-state-accepted', 'balance-other-input-state-safety',
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
        for node in ['balance-absent-parser-plan', 'balance-other-state-accepted', 'balance-other-input-state-safety', 'balance-rejected']:
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
