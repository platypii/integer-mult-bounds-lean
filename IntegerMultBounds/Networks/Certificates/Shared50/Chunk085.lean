import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk081

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk085_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 231310781707180357910797139891) chunk085 = true := by
  decide +kernel

theorem chunk085_last : lastKey (some 231310781707180357910797139891) chunk085 = some 232498975220138795566861995171 := by
  decide +kernel

theorem chunk085_length : chunk085.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
