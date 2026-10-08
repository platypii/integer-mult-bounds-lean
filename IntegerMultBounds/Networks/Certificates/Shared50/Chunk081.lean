import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk077

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk081_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 206839958814961192904277024103) chunk081 = true := by
  decide +kernel

theorem chunk081_last : lastKey (some 206839958814961192904277024103) chunk081 = some 208276963220246861376225900103 := by
  decide +kernel

theorem chunk081_length : chunk081.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
