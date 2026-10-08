import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk147

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk151_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 838560319314381510694805594583) chunk151 = true := by
  decide +kernel

theorem chunk151_last : lastKey (some 838560319314381510694805594583) chunk151 = some 842228372545341473059025400639 := by
  decide +kernel

theorem chunk151_length : chunk151.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
