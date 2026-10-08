import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk074

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk078_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 186620311808951598169990132900) chunk078 = true := by
  decide +kernel

theorem chunk078_last : lastKey (some 186620311808951598169990132900) chunk078 = some 189255391033198496670234654724 := by
  decide +kernel

theorem chunk078_length : chunk078.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
