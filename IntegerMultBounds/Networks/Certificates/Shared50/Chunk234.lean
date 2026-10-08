import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk230

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk234_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 3475788538938547764572714416412) chunk234 = true := by
  decide +kernel

theorem chunk234_last : lastKey (some 3475788538938547764572714416412) chunk234 = some 3501260478466436854764711019612 := by
  decide +kernel

theorem chunk234_length : chunk234.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
