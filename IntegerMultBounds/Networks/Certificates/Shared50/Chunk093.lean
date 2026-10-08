import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk089

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk093_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 264433334236780192374842969801) chunk093 = true := by
  decide +kernel

theorem chunk093_last : lastKey (some 264433334236780192374842969801) chunk093 = some 279453852406549818254260827668 := by
  decide +kernel

theorem chunk093_length : chunk093.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
