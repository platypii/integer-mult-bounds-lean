import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk073

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk077_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 185314282513563840285619533924) chunk077 = true := by
  decide +kernel

theorem chunk077_last : lastKey (some 185314282513563840285619533924) chunk077 = some 186620311808951598169990132900 := by
  decide +kernel

theorem chunk077_length : chunk077.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
