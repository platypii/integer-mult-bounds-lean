import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk197

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk201_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1934751015969035984433634564922) chunk201 = true := by
  decide +kernel

theorem chunk201_last : lastKey (some 1934751015969035984433634564922) chunk201 = some 1947458266463466056318219136346 := by
  decide +kernel

theorem chunk201_length : chunk201.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
