import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk056

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk060_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 111680969002208610419601687) chunk060 = true := by
  decide +kernel

theorem chunk060_last : lastKey (some 111680969002208610419601687) chunk060 = some 116221845787160002612524059 := by
  decide +kernel

theorem chunk060_length : chunk060.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
