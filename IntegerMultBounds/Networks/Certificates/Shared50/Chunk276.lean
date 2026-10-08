import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk272

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk276_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 7777549105871228493746218195261) chunk276 = true := by
  decide +kernel

theorem chunk276_last : lastKey (some 7777549105871228493746218195261) chunk276 = some 8180240677759056303526940066955 := by
  decide +kernel

theorem chunk276_length : chunk276.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
