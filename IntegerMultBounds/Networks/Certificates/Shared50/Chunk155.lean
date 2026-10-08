import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk151

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk155_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 875851578550102753895348701650) chunk155 = true := by
  decide +kernel

theorem chunk155_last : lastKey (some 875851578550102753895348701650) chunk155 = some 882206700686172123911285376114 := by
  decide +kernel

theorem chunk155_length : chunk155.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
