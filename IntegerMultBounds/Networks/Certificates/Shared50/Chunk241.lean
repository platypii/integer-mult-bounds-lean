import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk237

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk241_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 3870752473239448467585518286431) chunk241 = true := by
  decide +kernel

theorem chunk241_last : lastKey (some 3870752473239448467585518286431) chunk241 = some 3903419995358166057830168369200 := by
  decide +kernel

theorem chunk241_length : chunk241.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
