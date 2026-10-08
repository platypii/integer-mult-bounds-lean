import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk099

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk103_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 329627403215543010677200823303) chunk103 = true := by
  decide +kernel

theorem chunk103_last : lastKey (some 329627403215543010677200823303) chunk103 = some 333960977906147290062027763271 := by
  decide +kernel

theorem chunk103_length : chunk103.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
