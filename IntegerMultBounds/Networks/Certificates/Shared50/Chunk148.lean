import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk144

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk148_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 764743819494583709426695904115) chunk148 = true := by
  decide +kernel

theorem chunk148_last : lastKey (some 764743819494583709426695904115) chunk148 = some 787534823824473070236744597984 := by
  decide +kernel

theorem chunk148_length : chunk148.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
