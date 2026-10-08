import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk196

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk200_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1922116378053433907965016224903) chunk200 = true := by
  decide +kernel

theorem chunk200_last : lastKey (some 1922116378053433907965016224903) chunk200 = some 1934751015969035984433634564922 := by
  decide +kernel

theorem chunk200_length : chunk200.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
