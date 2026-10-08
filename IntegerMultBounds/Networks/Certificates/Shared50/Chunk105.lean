import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk101

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk105_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 350664539468439864219491227030) chunk105 = true := by
  decide +kernel

theorem chunk105_last : lastKey (some 350664539468439864219491227030) chunk105 = some 352374165389481295916586265935 := by
  decide +kernel

theorem chunk105_length : chunk105.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
