import IntegerMultBounds.Machine.AllAxisAddressHeaders
import IntegerMultBounds.Machine.UnitPhaseAddressInitAt

/-! Complete live counter initialization from the original node/global
headers. The address width is derived physically, used to fill the counter
and readout, then its generated header is erased. Streams are spectators. -/
namespace IntegerMultBounds.Machine.AllAxisPhaseStreamInit
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open ActiveRepairRankHeadersCommands (bank)
open SharedPlacementAlphabet (setTape)
open DelimitedRadixRecord (Context)
open BinaryAddressTableData (row)
open CountedLoopReuseAlphabet (binary)
variable {s : Shape}

def privateEmpty := SharedBank.empty 13 2
def input (order : Order) (v : Stage s) (rows : ℕ) (tail : Tapes 4 2) :=
  (bank (AllAxisAddressHeaders.initial order v rows)).append (privateEmpty.append tail)
def prepared (order : Order) (v : Stage s) (rows : ℕ) (tail : Tapes 4 2) :=
  (bank (AllAxisAddressHeaders.finished order v rows)).append (privateEmpty.append tail)

end
end IntegerMultBounds.Machine.AllAxisPhaseStreamInit
