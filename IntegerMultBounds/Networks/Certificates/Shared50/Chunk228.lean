import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk224

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk228_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 3003004593192616709056392152195) chunk228 = true := by
  decide +kernel

theorem chunk228_last : lastKey (some 3003004593192616709056392152195) chunk228 = some 3155220068208421236397127196333 := by
  decide +kernel

theorem chunk228_length : chunk228.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
