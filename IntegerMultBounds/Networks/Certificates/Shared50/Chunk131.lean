import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk127

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk131_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 571005531239357681357321237051) chunk131 = true := by
  decide +kernel

theorem chunk131_last : lastKey (some 571005531239357681357321237051) chunk131 = some 576253268627372484836614404931 := by
  decide +kernel

theorem chunk131_length : chunk131.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
