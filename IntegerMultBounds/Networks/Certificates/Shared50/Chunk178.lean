import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk174

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk178_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1293055093958293075049886519307) chunk178 = true := by
  decide +kernel

theorem chunk178_last : lastKey (some 1293055093958293075049886519307) chunk178 = some 1301985140985520118680247215267 := by
  decide +kernel

theorem chunk178_length : chunk178.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
