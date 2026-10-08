import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk213

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk217_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 2500534593337327818117759198808) chunk217 = true := by
  decide +kernel

theorem chunk217_last : lastKey (some 2500534593337327818117759198808) chunk217 = some 2597304471497664398289283327003 := by
  decide +kernel

theorem chunk217_length : chunk217.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
