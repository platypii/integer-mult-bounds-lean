import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk223

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk227_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 2940290317990495952244609924051) chunk227 = true := by
  decide +kernel

theorem chunk227_last : lastKey (some 2940290317990495952244609924051) chunk227 = some 3003004593192616709056392152195 := by
  decide +kernel

theorem chunk227_length : chunk227.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
