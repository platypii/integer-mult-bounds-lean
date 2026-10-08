import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk266

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk270_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 6884136837111078849362296618153) chunk270 = true := by
  decide +kernel

theorem chunk270_last : lastKey (some 6884136837111078849362296618153) chunk270 = some 6969238476314250831146984323126 := by
  decide +kernel

theorem chunk270_length : chunk270.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
