import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk083

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk087_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 234090914467212006831114978363) chunk087 = true := by
  decide +kernel

theorem chunk087_last : lastKey (some 234090914467212006831114978363) chunk087 = some 236094803250718607574966307451 := by
  decide +kernel

theorem chunk087_length : chunk087.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
