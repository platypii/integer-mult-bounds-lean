import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk082

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk086_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 232498975220138795566861995171) chunk086 = true := by
  decide +kernel

theorem chunk086_last : lastKey (some 232498975220138795566861995171) chunk086 = some 234090914467212006831114978363 := by
  decide +kernel

theorem chunk086_length : chunk086.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
