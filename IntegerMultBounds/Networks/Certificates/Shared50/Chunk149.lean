import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk145

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk149_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 787534823824473070236744597984) chunk149 = true := by
  decide +kernel

theorem chunk149_last : lastKey (some 787534823824473070236744597984) chunk149 = some 794487018573459719875671091240 := by
  decide +kernel

theorem chunk149_length : chunk149.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
