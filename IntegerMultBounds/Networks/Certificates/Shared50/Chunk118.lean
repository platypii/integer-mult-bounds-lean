import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk114

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk118_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 455531211330716179313676438569) chunk118 = true := by
  decide +kernel

theorem chunk118_last : lastKey (some 455531211330716179313676438569) chunk118 = some 457681979584210984604802739233 := by
  decide +kernel

theorem chunk118_length : chunk118.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
