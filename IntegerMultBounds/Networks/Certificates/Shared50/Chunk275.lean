import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk271

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk275_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 7650044279261847497191954367205) chunk275 = true := by
  decide +kernel

theorem chunk275_last : lastKey (some 7650044279261847497191954367205) chunk275 = some 7777549105871228493746218195261 := by
  decide +kernel

theorem chunk275_length : chunk275.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
