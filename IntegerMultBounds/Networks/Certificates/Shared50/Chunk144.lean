import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk140

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk144_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 714497250666713693422523850373) chunk144 = true := by
  decide +kernel

theorem chunk144_last : lastKey (some 714497250666713693422523850373) chunk144 = some 752454465957024876689916215539 := by
  decide +kernel

theorem chunk144_length : chunk144.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
