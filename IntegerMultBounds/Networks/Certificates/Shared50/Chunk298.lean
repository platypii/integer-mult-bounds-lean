import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk294

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk298_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 15908417110574467401901502685500) chunk298 = true := by
  decide +kernel

theorem chunk298_last : lastKey (some 15908417110574467401901502685500) chunk298 = some 16777263186035302515488100500669 := by
  decide +kernel

theorem chunk298_length : chunk298.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
