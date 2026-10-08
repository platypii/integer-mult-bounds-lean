import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk310

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk314_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 194911311484817956081226537279087) chunk314 = true := by
  decide +kernel

theorem chunk314_last : lastKey (some 194911311484817956081226537279087) chunk314 = some 211723253989835733933586157102546 := by
  decide +kernel

theorem chunk314_length : chunk314.length = 64 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
