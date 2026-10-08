import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk146

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk150_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 794487018573459719875671091240) chunk150 = true := by
  decide +kernel

theorem chunk150_last : lastKey (some 794487018573459719875671091240) chunk150 = some 838560319314381510694805594583 := by
  decide +kernel

theorem chunk150_length : chunk150.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
