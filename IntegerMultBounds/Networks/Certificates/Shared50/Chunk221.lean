import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk217

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk221_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 2656922512788418764969436716127) chunk221 = true := by
  decide +kernel

theorem chunk221_last : lastKey (some 2656922512788418764969436716127) chunk221 = some 2707520992574138075754849960027 := by
  decide +kernel

theorem chunk221_length : chunk221.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
