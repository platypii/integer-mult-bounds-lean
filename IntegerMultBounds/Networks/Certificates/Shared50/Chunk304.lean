import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk300

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk304_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 32911852416382475429098715768182) chunk304 = true := by
  decide +kernel

theorem chunk304_last : lastKey (some 32911852416382475429098715768182) chunk304 = some 40079227035157884806780530774823 := by
  decide +kernel

theorem chunk304_length : chunk304.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
