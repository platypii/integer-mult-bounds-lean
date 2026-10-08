import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk100

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk104_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 333960977906147290062027763271) chunk104 = true := by
  decide +kernel

theorem chunk104_last : lastKey (some 333960977906147290062027763271) chunk104 = some 350664539468439864219491227030 := by
  decide +kernel

theorem chunk104_length : chunk104.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
