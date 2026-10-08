import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk097

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk101_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 321105044804697069114566886407) chunk101 = true := by
  decide +kernel

theorem chunk101_last : lastKey (some 321105044804697069114566886407) chunk101 = some 327478252689425365188283428631 := by
  decide +kernel

theorem chunk101_length : chunk101.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
