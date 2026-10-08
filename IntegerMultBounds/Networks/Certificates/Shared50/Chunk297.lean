import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk293

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk297_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 15481132463203297716842390367548) chunk297 = true := by
  decide +kernel

theorem chunk297_last : lastKey (some 15481132463203297716842390367548) chunk297 = some 15908417110574467401901502685500 := by
  decide +kernel

theorem chunk297_length : chunk297.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
