import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk022

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk026_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 15981703866206165008177223) chunk026 = true := by
  decide +kernel

theorem chunk026_last : lastKey (some 15981703866206165008177223) chunk026 = some 16719140734199822317685770 := by
  decide +kernel

theorem chunk026_length : chunk026.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
