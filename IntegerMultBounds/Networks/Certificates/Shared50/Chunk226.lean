import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk222

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk226_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 2918430957756080657681595026427) chunk226 = true := by
  decide +kernel

theorem chunk226_last : lastKey (some 2918430957756080657681595026427) chunk226 = some 2940290317990495952244609924051 := by
  decide +kernel

theorem chunk226_length : chunk226.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
