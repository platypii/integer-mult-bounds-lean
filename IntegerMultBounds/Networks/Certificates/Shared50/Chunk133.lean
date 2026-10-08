import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk129

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk133_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 606800606027662204440250308497) chunk133 = true := by
  decide +kernel

theorem chunk133_last : lastKey (some 606800606027662204440250308497) chunk133 = some 609564452819740467050655652817 := by
  decide +kernel

theorem chunk133_length : chunk133.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
