import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk277

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk281_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 9050471677590580585206882450063) chunk281 = true := by
  decide +kernel

theorem chunk281_last : lastKey (some 9050471677590580585206882450063) chunk281 = some 9168453446155737218796227125542 := by
  decide +kernel

theorem chunk281_length : chunk281.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
