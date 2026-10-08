import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk124

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk128_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 547062559768330712056582359035) chunk128 = true := by
  decide +kernel

theorem chunk128_last : lastKey (some 547062559768330712056582359035) chunk128 = some 550426253577176829143120131139 := by
  decide +kernel

theorem chunk128_length : chunk128.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
