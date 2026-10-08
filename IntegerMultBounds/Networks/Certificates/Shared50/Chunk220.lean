import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk216

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk220_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 2636917556382442973360195060011) chunk220 = true := by
  decide +kernel

theorem chunk220_last : lastKey (some 2636917556382442973360195060011) chunk220 = some 2656922512788418764969436716127 := by
  decide +kernel

theorem chunk220_length : chunk220.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
