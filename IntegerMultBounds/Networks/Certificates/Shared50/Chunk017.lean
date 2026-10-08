import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk013

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk017_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 9909448043932043258748854) chunk017 = true := by
  decide +kernel

theorem chunk017_last : lastKey (some 9909448043932043258748854) chunk017 = some 10583569847563619101208840 := by
  decide +kernel

theorem chunk017_length : chunk017.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
