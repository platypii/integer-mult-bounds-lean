import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk154

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk158_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 934511467424971496765501473698) chunk158 = true := by
  decide +kernel

theorem chunk158_last : lastKey (some 934511467424971496765501473698) chunk158 = some 939887994324815362214547926826 := by
  decide +kernel

theorem chunk158_length : chunk158.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
