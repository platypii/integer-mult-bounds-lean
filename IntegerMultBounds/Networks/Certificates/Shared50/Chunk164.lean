import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk160

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk164_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1039929830020921808349176475641) chunk164 = true := by
  decide +kernel

theorem chunk164_last : lastKey (some 1039929830020921808349176475641) chunk164 = some 1045832737053009707318549460305 := by
  decide +kernel

theorem chunk164_length : chunk164.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
