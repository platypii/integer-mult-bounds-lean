import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk045

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk049_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 54408803117332570662144855) chunk049 = true := by
  decide +kernel

theorem chunk049_last : lastKey (some 54408803117332570662144855) chunk049 = some 59921076844485584238325841 := by
  decide +kernel

theorem chunk049_length : chunk049.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
