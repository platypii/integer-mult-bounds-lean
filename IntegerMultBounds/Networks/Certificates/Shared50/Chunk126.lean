import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk122

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk126_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 515176473233021995749668889611) chunk126 = true := by
  decide +kernel

theorem chunk126_last : lastKey (some 515176473233021995749668889611) chunk126 = some 544549102894270254944970491699 := by
  decide +kernel

theorem chunk126_length : chunk126.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
