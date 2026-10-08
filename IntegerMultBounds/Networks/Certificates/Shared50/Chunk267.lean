import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk263

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk267_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 6363569277015983820557796384434) chunk267 = true := by
  decide +kernel

theorem chunk267_last : lastKey (some 6363569277015983820557796384434) chunk267 = some 6472121877532960506758910912755 := by
  decide +kernel

theorem chunk267_length : chunk267.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
