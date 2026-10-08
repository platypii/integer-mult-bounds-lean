import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk199

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk203_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1960239325161877848531464369591) chunk203 = true := by
  decide +kernel

theorem chunk203_last : lastKey (some 1960239325161877848531464369591) chunk203 = some 2001635147232900227232374494118 := by
  decide +kernel

theorem chunk203_length : chunk203.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
