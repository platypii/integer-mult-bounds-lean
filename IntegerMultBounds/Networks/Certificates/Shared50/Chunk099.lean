import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk095

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk099_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 303634153964284865783848605029) chunk099 = true := by
  decide +kernel

theorem chunk099_last : lastKey (some 303634153964284865783848605029) chunk099 = some 313807942343505292642201040107 := by
  decide +kernel

theorem chunk099_length : chunk099.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
