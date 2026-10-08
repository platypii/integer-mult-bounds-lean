import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk096

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk100_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 313807942343505292642201040107) chunk100 = true := by
  decide +kernel

theorem chunk100_last : lastKey (some 313807942343505292642201040107) chunk100 = some 321105044804697069114566886407 := by
  decide +kernel

theorem chunk100_length : chunk100.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
