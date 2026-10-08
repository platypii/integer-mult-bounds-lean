import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk043

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk047_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 50570884830631279469173239) chunk047 = true := by
  decide +kernel

theorem chunk047_last : lastKey (some 50570884830631279469173239) chunk047 = some 52332340819342680486362416 := by
  decide +kernel

theorem chunk047_length : chunk047.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
