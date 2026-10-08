import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk090

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk094_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 279453852406549818254260827668) chunk094 = true := by
  decide +kernel

theorem chunk094_last : lastKey (some 279453852406549818254260827668) chunk094 = some 281793048907544987823383280629 := by
  decide +kernel

theorem chunk094_length : chunk094.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
