import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk069

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk073_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 165775188491222894341049200897) chunk073 = true := by
  decide +kernel

theorem chunk073_last : lastKey (some 165775188491222894341049200897) chunk073 = some 167554775753837709173513522501 := by
  decide +kernel

theorem chunk073_length : chunk073.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
