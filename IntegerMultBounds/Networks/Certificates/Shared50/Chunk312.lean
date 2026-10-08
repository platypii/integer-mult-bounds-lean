import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk308

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk312_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 140369957936036530488284116303907) chunk312 = true := by
  decide +kernel

theorem chunk312_last : lastKey (some 140369957936036530488284116303907) chunk312 = some 165375522385355544551288770130022 := by
  decide +kernel

theorem chunk312_length : chunk312.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
