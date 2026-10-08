import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk009

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk013_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 7910099978179452955186612) chunk013 = true := by
  decide +kernel

theorem chunk013_last : lastKey (some 7910099978179452955186612) chunk013 = some 8207815960926610532097892 := by
  decide +kernel

theorem chunk013_length : chunk013.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
