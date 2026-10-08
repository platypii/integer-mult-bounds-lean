import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk265

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk269_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 6799948002191032646559840809573) chunk269 = true := by
  decide +kernel

theorem chunk269_last : lastKey (some 6799948002191032646559840809573) chunk269 = some 6884136837111078849362296618153 := by
  decide +kernel

theorem chunk269_length : chunk269.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
