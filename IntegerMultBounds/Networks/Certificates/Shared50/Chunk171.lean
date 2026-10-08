import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk167

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk171_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1158845689961990093248237162028) chunk171 = true := by
  decide +kernel

theorem chunk171_last : lastKey (some 1158845689961990093248237162028) chunk171 = some 1165336804774671612947356822868 := by
  decide +kernel

theorem chunk171_length : chunk171.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
