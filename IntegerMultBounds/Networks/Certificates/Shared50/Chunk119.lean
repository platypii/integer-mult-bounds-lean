import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk115

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk119_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 457681979584210984604802739233) chunk119 = true := by
  decide +kernel

theorem chunk119_last : lastKey (some 457681979584210984604802739233) chunk119 = some 461283129213590269095933196233 := by
  decide +kernel

theorem chunk119_length : chunk119.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
