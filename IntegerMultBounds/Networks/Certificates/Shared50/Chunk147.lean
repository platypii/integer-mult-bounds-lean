import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk143

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk147_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 760255864443076467583122191224) chunk147 = true := by
  decide +kernel

theorem chunk147_last : lastKey (some 760255864443076467583122191224) chunk147 = some 764743819494583709426695904115 := by
  decide +kernel

theorem chunk147_length : chunk147.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
