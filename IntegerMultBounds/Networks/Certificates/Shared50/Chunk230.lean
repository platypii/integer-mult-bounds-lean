import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk226

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk230_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 3178626857527823087954237991585) chunk230 = true := by
  decide +kernel

theorem chunk230_last : lastKey (some 3178626857527823087954237991585) chunk230 = some 3206120219427664792327671696129 := by
  decide +kernel

theorem chunk230_length : chunk230.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
