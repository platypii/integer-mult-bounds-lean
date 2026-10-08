import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk148

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk152_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 842228372545341473059025400639) chunk152 = true := by
  decide +kernel

theorem chunk152_last : lastKey (some 842228372545341473059025400639) chunk152 = some 847136175160411006227956907543 := by
  decide +kernel

theorem chunk152_length : chunk152.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
