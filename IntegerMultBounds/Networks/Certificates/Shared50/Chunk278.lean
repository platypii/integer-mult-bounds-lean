import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk274

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk278_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 8297298966981457164629951764663) chunk278 = true := by
  decide +kernel

theorem chunk278_last : lastKey (some 8297298966981457164629951764663) chunk278 = some 8415824101415684145535275984055 := by
  decide +kernel

theorem chunk278_length : chunk278.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
