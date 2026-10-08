import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk061

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk065_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 156057419155307656731016363) chunk065 = true := by
  decide +kernel

theorem chunk065_last : lastKey (some 156057419155307656731016363) chunk065 = some 173450532275597296001569254 := by
  decide +kernel

theorem chunk065_length : chunk065.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
