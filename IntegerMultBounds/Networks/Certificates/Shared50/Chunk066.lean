import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk062

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk066_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 173450532275597296001569254) chunk066 = true := by
  decide +kernel

theorem chunk066_last : lastKey (some 173450532275597296001569254) chunk066 = some 191722563537045459749792359 := by
  decide +kernel

theorem chunk066_length : chunk066.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
