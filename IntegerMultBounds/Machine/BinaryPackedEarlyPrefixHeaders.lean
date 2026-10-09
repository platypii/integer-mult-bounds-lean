import IntegerMultBounds.Machine.BinaryAddressOffsetHeaders
import IntegerMultBounds.Machine.BinaryParityXorOffsetPlaced

/-! Paid width/range setup for source-prefix repetition. The child-stage ports
are original q/b/n and physical L/K descriptors; original controls are retained.
No source field is moved: L is the exact trailing rotation-row multiplicity. -/
namespace IntegerMultBounds.Machine.BinaryPackedEarlyPrefixHeaders
open SharedPlacementAlphabet (setTape)
open BinaryAddressOffsetHeaders (binary widthBits rangeBits countBits)
noncomputable section

def originals (hs : Fin 5 → List Bool) : Fin 3 → List Bool := ![hs 0,hs 1,hs 2]
def extra (hs : Fin 5 → List Bool) (Z : List Bool) : Tapes 3 0 :=
  ⟨![1,1,0],![binary (hs 3),binary (hs 4),BinaryParityXorOffsetRow.word Z]⟩
def input (hs : Fin 5 → List Bool) (Z : List Bool) :=
  (BinaryAddressOffsetHeaders.bank (originals hs)).append (extra hs Z)
def ready (hs : Fin 5 → List Bool) (Z : List Bool) (q n : ℕ) :=
  (BinaryAddressOffsetHeaders.output (originals hs) q n).append (extra hs Z)
def output (hs : Fin 5 → List Bool) (Z : List Bool) (q b n : ℕ) :=
  setTape (ready hs Z q n) 6 (binary (widthBits b n)) 1

def widthPlace : Fin (6+13) ≃ Fin 19 where
  toFun := ![9,6,10,1,11,2,0,3,4,5,7,8,12,13,14,15,16,17,18]
  invFun := ![6,3,5,7,8,9,1,10,11,0,2,4,12,13,14,15,16,17,18]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def prepare := extend BinaryAddressOffsetHeaders.program 3
def widthProgram := Placement.placed (DimensionProductDescriptor.program (q := 0)) widthPlace
def program := seq prepare widthProgram

theorem width_hoare (hs : Fin 5 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 0<b)
    (hvb : Counter.value (hs 1)=b) (hvn : Counter.value (hs 2)=n)
    (cb : GrowingCounterData.Canonical (hs 1)) (cn : GrowingCounterData.Canonical (hs 2)) :
    HoareTime widthProgram (fun z => z=ready hs Z q n) (fun z => z=output hs Z q b n) (53*(n*b)+28) := by
  have ha : Placement.active widthPlace (ready hs Z q n)=DimensionProductDescriptor.input (hs 1) (hs 2) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have h := Placement.hoare_at (DimensionProductDescriptor.construct_hoare (hs 1) (hs 2) n b hb hvb hvn cb cn)
    widthPlace _ ha
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def cost (q b n : ℕ) := BinaryAddressOffsetHeaders.cost q n+53*(n*b)+29

theorem constructs (hs : Fin 5 → List Bool) (Z : List Bool) (q b n : ℕ) (hq : 0<q) (hb : 0<b)
    (hvq : Counter.value (hs 0)=q) (hvb : Counter.value (hs 1)=b) (hvn : Counter.value (hs 2)=n)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime program (fun z => z=input hs Z) (fun z => z=output hs Z q b n) (cost q b n) := by
  have h0 := hoare_extend_eq (BinaryAddressOffsetHeaders.constructs (originals hs) q n hq hvq hvn (hc 0) (hc 2)) (extra hs Z)
  have h1 := width_hoare hs Z q b n hb hvb hvn (hc 1) (hc 2)
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.BinaryPackedEarlyPrefixHeaders
