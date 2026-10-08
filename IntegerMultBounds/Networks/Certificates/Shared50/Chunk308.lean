import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk304

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk308_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 70120310187665451902745009356331) chunk308 = true := by
  decide +kernel

theorem chunk308_last : lastKey (some 70120310187665451902745009356331) chunk308 = some 83902879113757938137303015920727 := by
  decide +kernel

theorem chunk308_length : chunk308.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
