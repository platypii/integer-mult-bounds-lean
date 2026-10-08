import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk136

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk140_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 680255864375196916343005182037) chunk140 = true := by
  decide +kernel

theorem chunk140_last : lastKey (some 680255864375196916343005182037) chunk140 = some 684326665228070529413142858316 := by
  decide +kernel

theorem chunk140_length : chunk140.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
