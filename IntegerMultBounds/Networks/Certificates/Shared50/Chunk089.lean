import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk085

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk089_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 247177022083257511988601838283) chunk089 = true := by
  decide +kernel

theorem chunk089_last : lastKey (some 247177022083257511988601838283) chunk089 = some 250125119187417850561594929534 := by
  decide +kernel

theorem chunk089_length : chunk089.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
