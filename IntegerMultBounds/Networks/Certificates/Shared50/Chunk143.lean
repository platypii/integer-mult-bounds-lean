import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk139

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk143_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 708162439879917704357181319981) chunk143 = true := by
  decide +kernel

theorem chunk143_last : lastKey (some 708162439879917704357181319981) chunk143 = some 714497250666713693422523850373 := by
  decide +kernel

theorem chunk143_length : chunk143.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
