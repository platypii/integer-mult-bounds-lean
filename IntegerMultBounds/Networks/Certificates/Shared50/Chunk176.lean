import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk172

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk176_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1278871275885861859125106673707) chunk176 = true := by
  decide +kernel

theorem chunk176_last : lastKey (some 1278871275885861859125106673707) chunk176 = some 1285945997866583813157494736739 := by
  decide +kernel

theorem chunk176_length : chunk176.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
