import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk149

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk153_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 847136175160411006227956907543) chunk153 = true := by
  decide +kernel

theorem chunk153_last : lastKey (some 847136175160411006227956907543) chunk153 = some 852069321820488381068046783378 := by
  decide +kernel

theorem chunk153_length : chunk153.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
