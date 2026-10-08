import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk142

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk146_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 756901908443096622712841930611) chunk146 = true := by
  decide +kernel

theorem chunk146_last : lastKey (some 756901908443096622712841930611) chunk146 = some 760255864443076467583122191224 := by
  decide +kernel

theorem chunk146_length : chunk146.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
