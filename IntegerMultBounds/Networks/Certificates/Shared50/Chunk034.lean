import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk030

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk034_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 23778104052499033745052809) chunk034 = true := by
  decide +kernel

theorem chunk034_last : lastKey (some 23778104052499033745052809) chunk034 = some 24556660973713019208942489 := by
  decide +kernel

theorem chunk034_length : chunk034.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
