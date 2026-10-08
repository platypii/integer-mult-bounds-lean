import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk187

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk191_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1598526868585032400529880530964) chunk191 = true := by
  decide +kernel

theorem chunk191_last : lastKey (some 1598526868585032400529880530964) chunk191 = some 1635349159419443721278474574861 := by
  decide +kernel

theorem chunk191_length : chunk191.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
