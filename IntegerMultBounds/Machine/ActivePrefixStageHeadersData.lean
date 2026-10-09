import IntegerMultBounds.Machine.ActivePrefixStageHeadersOps
import IntegerMultBounds.Machine.ActivePrefixStageGeometry
import IntegerMultBounds.Machine.ActivePrefixLayoutHeadersGeometry

/-! Thirteen original shape/node/slot numbers are the complete numeric input.
Every layout width and source offset is generated rather than supplied. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageHeadersData
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters ActivePrefixStageGeometry
open ActiveRepairRankHeadersCommands (State put)
open ActivePrefixStageHeadersOps

inductive Order | early | late deriving DecidableEq

def originalValues {s : Shape} (v : Stage s) (rows : ℕ) : Fin 13 → ℕ :=
  ![s.chunk,s.axes,s.guard,s.active,rows,s.payload,v.slots,v.f,v.left,v.right,v.rho,v.source.val,v.target.val]
def initial {s : Shape} (v : Stage s) (rows : ℕ) : State := fun i =>
  if h : i.val<13 then some (originalValues v rows ⟨i.val,h⟩) else none

def offset {s : Shape} (order : Order) (v : Stage s) :=
  match order with | .early => earlyOffset v | .late => lateOffset v

def outputs {s : Shape} (order : Order) (v : Stage s) : Fin 9 → ℕ :=
  ![s.H,s.B,s.F,before v,after v,(v.f-1)*s.chunk,(v.f-1)*s.guard,v.f-1,offset order v]
def finished {s : Shape} (order : Order) (v : Stage s) (rows : ℕ) : State := fun i =>
  if h : i.val<13 then some (originalValues v rows ⟨i.val,h⟩)
  else if h : i.val<22 then some (outputs order v ⟨i.val-13,by omega⟩) else none

def layoutFocus : Fin 14 → Fin 28 := ![13,14,15,16,17,18,19,0,2,20,10,21,4,5]
def reservationFocus : Fin 7 → Fin 28 := ![0,1,2,20,3,4,5]
theorem layoutFocus_injective : Function.Injective layoutFocus := by decide
theorem reservationFocus_injective : Function.Injective reservationFocus := by decide

def seed : List Op := [.one 22,.command (.difference 7 22 20 (by decide)),.product ![2,1,13] (by decide)]
def back : List Op := [.round ![13,0,24] (by decide),
  .command (.difference 24 13 14 (by decide)),.command (.erase 24)]
def front : List Op := [.command (.copy 13 24 (by decide)),.command (.add 24 13 (by decide)),
  .round ![24,0,25] (by decide),.command (.difference 25 24 15 (by decide)),
  .command (.erase 24),.command (.erase 25)]
def widths : List Op := [.product ![0,20,18] (by decide),.product ![2,20,19] (by decide)]
def highTarget : List Op := [.product ![7,12,24] (by decide),.command (.add 24 8 (by decide)),
  .product ![0,24,25] (by decide),.command (.difference 0 10 26 (by decide)),
  .command (.add 25 26 (by decide)),.command (.copy 25 16 (by decide)),
  .command (.erase 24),.command (.erase 25),.command (.erase 26)]
def lowTarget : List Op := [.command (.difference 6 12 24 (by decide)),
  .command (.difference 24 22 25 (by decide)),.command (.erase 24),
  .product ![7,25,24] (by decide),.command (.erase 25),.command (.add 24 9 (by decide)),
  .product ![0,24,25] (by decide),.command (.erase 24),.command (.add 25 10 (by decide)),
  .command (.copy 25 17 (by decide)),.command (.erase 25)]
def source : Order → List Op
  | .early => [.command (.difference 12 11 24 (by decide)),
      .command (.difference 24 22 25 (by decide)),.command (.erase 24),
      .product ![7,25,24] (by decide),.command (.erase 25),
      .product ![0,24,25] (by decide),.command (.erase 24),
      .command (.difference 0 10 24 (by decide)),.command (.add 25 24 (by decide)),
      .command (.copy 25 21 (by decide)),.command (.erase 24),.command (.erase 25)]
  | .late => [.command (.difference 6 11 24 (by decide)),
      .command (.difference 24 22 25 (by decide)),.command (.erase 24),
      .product ![7,25,24] (by decide),.command (.erase 25),.command (.add 24 9 (by decide)),
      .product ![0,24,25] (by decide),.command (.erase 24),
      .command (.copy 25 21 (by decide)),.command (.erase 25)]
def schedule (order : Order) := seed++back++front++widths++highTarget++lowTarget++source order++[.command (.erase 22)]

theorem original_retained {s : Shape} (order : Order) (v : Stage s) (rows : ℕ) (i : Fin 13) :
    finished order v rows (Fin.castAdd 15 i)=some (originalValues v rows i) := by
  simp [finished,i.isLt]

theorem layout_values {s : Shape} (order : Order) (v : Stage s) (rows : ℕ)
    (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (i : Fin 14) :
    finished order v rows (layoutFocus i)=some (ActivePrefixLayoutHeadersData.originalValues
      (ActivePrefixLayoutHeadersGeometry.inputs s (parameters v hG hGK) (offset order v) rows) i) := by
  fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.ActivePrefixStageHeadersData
