import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk080

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk084_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 219717546725505867185710349287) chunk084 = true := by
  decide +kernel

theorem chunk084_last : lastKey (some 219717546725505867185710349287) chunk084 = some 231310781707180357910797139891 := by
  decide +kernel

theorem chunk084_length : chunk084.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
