import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk130

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk134_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 609564452819740467050655652817) chunk134 = true := by
  decide +kernel

theorem chunk134_last : lastKey (some 609564452819740467050655652817) chunk134 = some 613262970066536553682322298769 := by
  decide +kernel

theorem chunk134_length : chunk134.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
