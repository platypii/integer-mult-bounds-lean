import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk258

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk262_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 5751654863439702544370409184935) chunk262 = true := by
  decide +kernel

theorem chunk262_last : lastKey (some 5751654863439702544370409184935) chunk262 = some 5811103396784137377319102222371 := by
  decide +kernel

theorem chunk262_length : chunk262.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
