import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk284

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk288_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 10944302151177800755696624166041) chunk288 = true := by
  decide +kernel

theorem chunk288_last : lastKey (some 10944302151177800755696624166041) chunk288 = some 11130381019026358676901103162169 := by
  decide +kernel

theorem chunk288_length : chunk288.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
