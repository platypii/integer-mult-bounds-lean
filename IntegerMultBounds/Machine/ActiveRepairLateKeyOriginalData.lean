import IntegerMultBounds.Machine.ActiveRepairLateKey
import IntegerMultBounds.Machine.ActiveRepairRankHeadersPlaced

/-! Original geometric descriptors and a genuine rank supply all inputs of
the later key machine. Parser and patch headers start physically blank. -/
namespace IntegerMultBounds.Machine.ActiveRepairLateKeyOriginalData
noncomputable section
open ActiveRepairRankHeadersData
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)

structure Data where
  side : SourceSide
  geom : Widths
  originals : Fin 10 → List Bool
  cs : List Bool
  ss : Fin 4 → List Bool
  bs : List Bool
  q : ℕ
  b : ℕ
  rho : ℕ
  n : ℕ
  f : ℕ
  hb : 1≤b
  hbq : b+1≤q

namespace Data
def key (d : Data) : ActiveRepairLateKeyData.Data where
  cs := d.cs
  starts := fun i => parserValues d.side d.geom (ActiveRepairRankFieldsBank.offsetSlot i)
  widths := fun i => parserValues d.side d.geom (ActiveRepairRankFieldsBank.widthSlot i)
  hs := fun i => bits (parserValues d.side d.geom i)
  ss := d.ss
  bs := d.bs
  ph := fun i => bits (patchValues d.geom i)
  q := d.q
  b := d.b
  rho := d.rho
  n := d.n
  f := d.f
  A := d.geom.addressBits
  sv := targetStart d.geom
  st := tStart d.geom
  su := uStart d.geom
  hb := d.hb
  hbq := d.hbq

def originalBank (d : Data) : Tapes 10 1 :=
  ⟨fun _ => 1,fun i => RadixZeroFill.encodedBinary (d.originals i)⟩
def generated (d : Data) := d.key.input.append d.originalBank
end Data

def generatedSlots : Fin 15 → Fin 43 := ![6,7,8,9,10,11,12,13,23,24,25,26,27,28,29]
def headerFocus : Fin 25 → Fin 43 :=
  ![33,34,35,36,37,38,39,40,41,42,6,7,8,9,10,11,12,13,23,24,25,26,27,28,29]
def keyFocus : Fin 33 → Fin 43 := Fin.castAdd 10
theorem header_injective : Function.Injective headerFocus := by decide
theorem key_injective : Function.Injective keyFocus := Fin.castAdd_injective _ _

private theorem strip_subset {c e k : ℕ} (v : Tapes k 1)
    (small : Fin c → Fin k) (large : Fin e → Fin k)
    (hsub : ∀ j, ∃ i, large i=small j) :
    SharedBank.strip (SharedBank.strip v small) large=SharedBank.strip v large := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    by_cases hl : ∃ j, large j=i
    · simp only [SharedBank.strip,hl,ite_true]
    · have hs : ¬∃ j, small j=i := by
        rintro ⟨j,rfl⟩
        exact hl (hsub j)
      simp only [SharedBank.strip,hl,hs,ite_false]

private theorem strip_set_congr {c k : ℕ} (v w : Tapes k 1) (focus : Fin c → Fin k)
    (hv : SharedBank.strip v focus=SharedBank.strip w focus)
    (i : Fin k) (f : ℤ → Fin 5) (p : ℤ) :
    SharedBank.strip (setTape v i f p) focus=SharedBank.strip (setTape w i f p) focus := by
  apply congrArg₂ Tapes.mk <;> funext j
  · by_cases hj : j=i
    · subst j; simp [setTape]
    · simpa only [SharedBank.strip,setTape,Function.update_of_ne hj] using
        congrFun (congrArg Tapes.head hv) j
  · by_cases hj : j=i
    · subst j; simp [setTape]
    · simpa only [SharedBank.strip,setTape,Function.update_of_ne hj] using
        congrFun (congrArg Tapes.tape hv) j

namespace Data
def input (d : Data) := SharedBank.strip d.generated generatedSlots
def written (d : Data) := setTape d.generated 31
  (FlagCopy.keyTape (FlagCopy.keyWord d.key.flag d.key.destination)) 0
def output (d : Data) := setTape d.input 31
  (FlagCopy.keyTape (FlagCopy.keyWord d.key.flag d.key.destination)) 0
end Data

theorem input_payload (d : Data) : SharedBank.payload d.input headerFocus=
    ActiveRepairRankHeadersPlaced.sources (a := 1) d.originals := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [Data.input,SharedBank.strip,generatedSlots,headerFocus,Fin.exists_fin_succ]
  all_goals rfl

theorem generated_payload (d : Data)
    (hv : ∀ i, Counter.value (d.originals i)=originalValues d.geom i)
    (hc : ∀ i, GrowingCounterData.Canonical (d.originals i)) :
    SharedBank.payload d.generated headerFocus=
      ActiveRepairRankHeadersPlaced.outputs (a := 1) d.side d.geom := by
  have he : d.originals=fun i => bits (originalValues d.geom i) := by
    funext i
    exact CompactGadgetReservationHeadersCore.canonical_bits _ _ (hc i) (hv i)
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact congrArg RadixZeroFill.encodedBinary (congrFun he _)

theorem input_frame (d : Data) : SharedBank.strip d.input headerFocus=
    SharedBank.strip d.generated headerFocus := by
  apply strip_subset
  intro j
  refine ⟨⟨j.val+10,by omega⟩,?_⟩
  fin_cases j <;> rfl

theorem produced_eq (d : Data)
    (hv : ∀ i, Counter.value (d.originals i)=originalValues d.geom i)
    (hc : ∀ i, GrowingCounterData.Canonical (d.originals i)) :
    ActiveRepairRankHeadersPlaced.result d.input headerFocus d.side d.geom=d.generated := by
  apply ActiveRepairEarlyKeyPlacement.install_eq
    d.input d.generated headerFocus _ (generated_payload d hv hc) (input_frame d)

theorem key_payload (d : Data) : SharedBank.payload d.generated keyFocus=d.key.input :=
  SharedBankFrames.payload_append_left _ _ id

theorem key_result (d : Data) :
    ActiveRepairLateKeyPlaced.result d.generated keyFocus d.key=d.written := rfl

theorem written_payload (d : Data)
    (hv : ∀ i, Counter.value (d.originals i)=originalValues d.geom i)
    (hc : ∀ i, GrowingCounterData.Canonical (d.originals i)) :
    SharedBank.payload d.written headerFocus=ActiveRepairRankHeadersPlaced.outputs d.side d.geom := by
  have he := generated_payload d hv hc
  rw [←he]
  apply congrArg₂ Tapes.mk <;> funext i
  · have hi : headerFocus i≠31 := by fin_cases i <;> decide
    simp only [Data.written,setTape,Function.update_of_ne hi]
  · have hi : headerFocus i≠31 := by fin_cases i <;> decide
    simp only [Data.written,setTape,Function.update_of_ne hi]

theorem output_payload (d : Data) : SharedBank.payload d.output headerFocus=
    ActiveRepairRankHeadersPlaced.sources (a := 1) d.originals := by
  have he := input_payload d
  rw [←he]
  apply congrArg₂ Tapes.mk <;> funext i
  · have hi : headerFocus i≠31 := by fin_cases i <;> decide
    simp only [Data.output,setTape,Function.update_of_ne hi]
  · have hi : headerFocus i≠31 := by fin_cases i <;> decide
    simp only [Data.output,setTape,Function.update_of_ne hi]

theorem restored_eq (d : Data) :
    ActiveRepairRankHeadersPlaced.restored d.written headerFocus d.originals=d.output := by
  apply ActiveRepairEarlyKeyPlacement.install_eq _ _ _ _ (output_payload d)
  exact strip_set_congr _ _ headerFocus (input_frame d).symm 31 _ 0

end
end IntegerMultBounds.Machine.ActiveRepairLateKeyOriginalData
