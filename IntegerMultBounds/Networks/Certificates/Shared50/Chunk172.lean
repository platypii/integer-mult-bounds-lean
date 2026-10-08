import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk168

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk172_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1165336804774671612947356822868) chunk172 = true := by
  decide +kernel

theorem chunk172_last : lastKey (some 1165336804774671612947356822868) chunk172 = some 1171859994678759067132930590755 := by
  decide +kernel

theorem chunk172_length : chunk172.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
