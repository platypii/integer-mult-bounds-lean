import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk292

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk296_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 14449194985091733545112251153406) chunk296 = true := by
  decide +kernel

theorem chunk296_last : lastKey (some 14449194985091733545112251153406) chunk296 = some 15481132463203297716842390367548 := by
  decide +kernel

theorem chunk296_length : chunk296.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
