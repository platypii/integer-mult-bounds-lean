import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk150

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk154_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 852069321820488381068046783378) chunk154 = true := by
  decide +kernel

theorem chunk154_last : lastKey (some 852069321820488381068046783378) chunk154 = some 875851578550102753895348701650 := by
  decide +kernel

theorem chunk154_length : chunk154.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
