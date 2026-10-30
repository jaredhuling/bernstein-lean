"""Failure-path tests for the evidence parser and reviewed-statement gate."""
import copy
import json
import unittest

from verify import check_review, declarations, parse_records, signature_hash


class VerificationFailures(unittest.TestCase):
    def setUp(self):
        self.record = {"declaration": "T", "elaborated_type": "True", "binders": [],
                       "axioms": ["propext"], "canonical_type": "True", "conclusion": "True",
                       "direct_proof_dependencies": []}
        self.log = "AUDIT_DECLARATION " + json.dumps(self.record)
        self.review = {"declarations": {"T": {
            "signature_sha256": signature_hash(self.record), "proposition_binders": {}}},
            "definition_context_sha256": {}}

    def test_clean_record(self):
        self.assertEqual(parse_records(self.log, ["T"]), [self.record])
        check_review([self.record], self.review)

    def test_missing_or_duplicate_record_rejected(self):
        for log in ["", self.log + "\n" + self.log]:
            with self.assertRaises(ValueError):
                parse_records(log, ["T"])

    def test_unexpected_axiom_rejected(self):
        for name in ["sorryAx", "Extra.axiom"]:
            record = dict(self.record, axioms=[name])
            with self.assertRaises(ValueError):
                parse_records("AUDIT_DECLARATION " + json.dumps(record), ["T"])

    def test_error_after_success_rejected(self):
        with self.assertRaises(ValueError):
            parse_records(self.log + "\nfile: error: later failure", ["T"])

    def test_changed_statement_rejected(self):
        with self.assertRaises(ValueError):
            check_review([dict(self.record, canonical_type="False")], self.review)

    def test_unreviewed_premise_rejected(self):
        record = dict(self.record, binders=[{"index": 0, "is_proposition": True}])
        with self.assertRaises(ValueError):
            check_review([record], self.review)
        review = copy.deepcopy(self.review)
        review["declarations"]["T"]["proposition_binders"]["0"] = {"provenance": "unclassified"}
        with self.assertRaises(ValueError):
            check_review([record], review)

    def test_categorized_error_rejected(self):
        with self.assertRaises(ValueError):
            parse_records(self.log + "\nf.lean: error(lean.unknownIdentifier): failed", ["T"])

    def test_malformed_record_rejected(self):
        for r in [{"declaration": "T"}, dict(self.record, axioms="propext"),
                  dict(self.record, binders=[{"index": 2}])]:
            with self.assertRaises(ValueError):
                parse_records("AUDIT_DECLARATION " + json.dumps(r), ["T"])

    def test_private_and_exposed_declarations_indexed(self):
        source = "namespace N\nprivate lemma p : True := trivial\n@[expose] def D := True\nend N"
        self.assertEqual(declarations(source), ["N.p", "N.D"])

    def test_unreferenced_axiom_rejected(self):
        with self.assertRaises(ValueError):
            declarations("namespace N\naxiom hidden : True\nend N")

    def test_missing_provenance_evidence_rejected(self):
        record = dict(self.record, binders=[{"index": 0, "is_proposition": True}])
        review = copy.deepcopy(self.review)
        review["declarations"]["T"]["proposition_binders"]["0"] = {"provenance": "reference-assumes"}
        with self.assertRaises(ValueError):
            check_review([record], review)

    def test_changed_context_rejected(self):
        review = copy.deepcopy(self.review)
        review["definition_context_sha256"] = {"lean-toolchain": "wrong hash"}
        with self.assertRaises(ValueError):
            check_review([self.record], review)

    def test_unsupported_declarations_fail_closed(self):
        for line in ["opaque hidden : True := trivial", "noncomputable def hidden := True",
                     "structure Unreviewed where"]:
            with self.assertRaises(ValueError):
                declarations(line)


if __name__ == "__main__":
    unittest.main()
