import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk059

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk063_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 134857146079349038475191321) chunk063 = true := by
  decide +kernel

theorem chunk063_last : lastKey (some 134857146079349038475191321) chunk063 = some 149536345272997718319293051 := by
  decide +kernel

theorem chunk063_length : chunk063.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
