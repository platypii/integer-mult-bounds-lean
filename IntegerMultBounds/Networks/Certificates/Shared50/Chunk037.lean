import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk033

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk037_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 29099913865769169180807932) chunk037 = true := by
  decide +kernel

theorem chunk037_last : lastKey (some 29099913865769169180807932) chunk037 = some 30345569194572378253348426 := by
  decide +kernel

theorem chunk037_length : chunk037.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
