import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk123

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk127_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 544549102894270254944970491699) chunk127 = true := by
  decide +kernel

theorem chunk127_last : lastKey (some 544549102894270254944970491699) chunk127 = some 547062559768330712056582359035 := by
  decide +kernel

theorem chunk127_length : chunk127.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
