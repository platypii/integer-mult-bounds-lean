import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk044

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk048_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 52332340819342680486362416) chunk048 = true := by
  decide +kernel

theorem chunk048_last : lastKey (some 52332340819342680486362416) chunk048 = some 54408803117332570662144855 := by
  decide +kernel

theorem chunk048_length : chunk048.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
