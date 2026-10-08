import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk128

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk132_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 576253268627372484836614404931) chunk132 = true := by
  decide +kernel

theorem chunk132_last : lastKey (some 576253268627372484836614404931) chunk132 = some 606800606027662204440250308497 := by
  decide +kernel

theorem chunk132_length : chunk132.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
