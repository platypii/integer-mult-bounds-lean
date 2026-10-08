import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk012

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk016_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 8673465110282357329718247) chunk016 = true := by
  decide +kernel

theorem chunk016_last : lastKey (some 8673465110282357329718247) chunk016 = some 9909448043932043258748854 := by
  decide +kernel

theorem chunk016_length : chunk016.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
