import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk107

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk111_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 393132702024809059760913411145) chunk111 = true := by
  decide +kernel

theorem chunk111_last : lastKey (some 393132702024809059760913411145) chunk111 = some 395022758175693791751534863058 := by
  decide +kernel

theorem chunk111_length : chunk111.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
