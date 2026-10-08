import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk198

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk202_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1947458266463466056318219136346) chunk202 = true := by
  decide +kernel

theorem chunk202_last : lastKey (some 1947458266463466056318219136346) chunk202 = some 1960239325161877848531464369591 := by
  decide +kernel

theorem chunk202_length : chunk202.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
