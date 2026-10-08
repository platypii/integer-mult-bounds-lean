import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk186

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk190_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1587837649471700411576128974141) chunk190 = true := by
  decide +kernel

theorem chunk190_last : lastKey (some 1587837649471700411576128974141) chunk190 = some 1598526868585032400529880530964 := by
  decide +kernel

theorem chunk190_length : chunk190.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
