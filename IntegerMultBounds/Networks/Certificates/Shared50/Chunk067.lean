import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk063

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk067_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 191722563537045459749792359) chunk067 = true := by
  decide +kernel

theorem chunk067_last : lastKey (some 191722563537045459749792359) chunk067 = some 210792828529961700077420434 := by
  decide +kernel

theorem chunk067_length : chunk067.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
