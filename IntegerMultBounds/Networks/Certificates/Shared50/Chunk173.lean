import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk169

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk173_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1171859994678759067132930590755) chunk173 = true := by
  decide +kernel

theorem chunk173_last : lastKey (some 1171859994678759067132930590755) chunk173 = some 1203272925317996353178732664695 := by
  decide +kernel

theorem chunk173_length : chunk173.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
