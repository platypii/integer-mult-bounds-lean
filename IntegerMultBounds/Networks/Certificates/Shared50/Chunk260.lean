import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk256

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk260_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 5627910620632067761604511588804) chunk260 = true := by
  decide +kernel

theorem chunk260_last : lastKey (some 5627910620632067761604511588804) chunk260 = some 5686235501424018197026774165091 := by
  decide +kernel

theorem chunk260_length : chunk260.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
