import IntegerMultBounds.Networks.Certificates.Shared50.Data

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk001_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 4242913991422880964759557) chunk001 = true := by
  decide +kernel

theorem chunk001_last : lastKey (some 4242913991422880964759557) chunk001 = some 4564718210909734999905424 := by
  decide +kernel

theorem chunk001_length : chunk001.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
