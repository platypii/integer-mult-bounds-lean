import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk273

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk277_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 8180240677759056303526940066955) chunk277 = true := by
  decide +kernel

theorem chunk277_last : lastKey (some 8180240677759056303526940066955) chunk277 = some 8297298966981457164629951764663 := by
  decide +kernel

theorem chunk277_length : chunk277.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
