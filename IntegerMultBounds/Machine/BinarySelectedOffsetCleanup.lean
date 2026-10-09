import IntegerMultBounds.Machine.BinarySelectedOffsetGather

/-! Paid cleanup of both generated input streams and all three derived
headers. The packed output is physically rewound to its origin, and the only
remaining tapes are the original b/q/n descriptors, original control and actual offset word. -/
namespace IntegerMultBounds.Machine.BinarySelectedOffsetCleanup
open SharedPlacementAlphabet (setTape)
open BinarySelectedOffsetData
open BinaryAddressOffsetHeaders (widthBits rangeBits countBits)
noncomputable section

def states (hs : Fin 3 → List Bool) (q b n : ℕ) (Z : List Bool) (hb : 1 ≤ b) (hbq : b+1 ≤ q) : Fin 7 → Tapes 17 0 :=
  let v0 := BinarySelectedOffsetGather.after hs q b n Z hb hbq
  let v1 := setTape v0 6 (fun _ => blank) 0
  let v2 := setTape v1 7 (fun _ => blank) 0
  let v3 := setTape v2 8 (BinarySelectedOffsetGather.outputTape q b n Z hb hbq) 0
  let v4 := setTape v3 3 (fun _ => blank) 0
  let v5 := setTape v4 4 (fun _ => blank) 0
  let v6 := setTape v5 5 (fun _ => blank) 0
  ![v0,v1,v2,v3,v4,v5,v6]

def sourceProgram := Placement.placed (EraseBack.program (a := 0)) (FiniteReturnStackAt.placement (6 : Fin 17))
def dummyProgram := Placement.placed (EraseBack.program (a := 0)) (FiniteReturnStackAt.placement (7 : Fin 17))
def rewindProgram := Placement.placed (ReturnOrigin.program (a := 0)) (FiniteReturnStackAt.placement (8 : Fin 17))
def widthProgram := BinaryDescriptorCleanupList.oneProgram (a := 0) (3 : Fin 17)
def rangeProgram := BinaryDescriptorCleanupList.oneProgram (a := 0) (4 : Fin 17)
def countProgram := BinaryDescriptorCleanupList.oneProgram (a := 0) (5 : Fin 17)
def program := seq (seq (seq (seq (seq sourceProgram dummyProgram) rewindProgram) widthProgram) rangeProgram) countProgram

theorem source_hoare (hs : Fin 3 → List Bool) (q b n : ℕ) (Z : List Bool) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :
    HoareTime sourceProgram (fun z => z=states hs q b n Z hb hbq 0)
      (fun z => z=states hs q b n Z hb hbq 1) ((n*2^(n*b))*b+2) := by
  have hr := EraseBack.erase_hoare (fun _ => (blank : Fin 4)) 0 ((source b n).map bitSymbol)
    (ReturnOrigin.bits_nonblank _) rfl (by intros; rfl)
  simp only [List.length_map,source_length,zero_add] at hr
  have ha : Placement.active (FiniteReturnStackAt.placement (6 : Fin 17)) (states hs q b n Z hb hbq 0)=
      (EraseBack.cfg (putWord (fun _ => blank) 0 ((source b n).map bitSymbol)) ((n*2^(n*b))*b) 0).tapes := by
    rw [FiniteReturnStackAt.active_bank]; rfl
  have hh := Placement.hoare_at hr (FiniteReturnStackAt.placement (6 : Fin 17)) (states hs q b n Z hb hbq 0) ha
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank (fun _ => blank) 0)=_
  exact FiniteReturnStackAt.replace_bank _ _ _ _

theorem controls_hoare (hs : Fin 3 → List Bool) (q b n : ℕ) (Z : List Bool)
    (hb : 1 ≤ b) (hbq : b+1 ≤ q) (hZ : Z.length=n) :
    HoareTime dummyProgram (fun z => z=states hs q b n Z hb hbq 1)
      (fun z => z=states hs q b n Z hb hbq 2) (n*2^(n*b)+2) := by
  have hr := EraseBack.erase_hoare (fun _ => (blank : Fin 4)) 0
    ((controls b n Z).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl (by intros; rfl)
  simp only [List.length_map,controls_length b n Z hZ,zero_add] at hr
  have ha : Placement.active (FiniteReturnStackAt.placement (7 : Fin 17)) (states hs q b n Z hb hbq 1)=
      (EraseBack.cfg (putWord (fun _ => blank) 0 ((controls b n Z).map bitSymbol)) (n*2^(n*b)) 0).tapes := by
    rw [FiniteReturnStackAt.active_bank]; rfl
  have hh := Placement.hoare_at hr (FiniteReturnStackAt.placement (7 : Fin 17)) (states hs q b n Z hb hbq 1) ha
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank (fun _ => blank) 0)=_
  exact FiniteReturnStackAt.replace_bank _ _ _ _

theorem rewind_hoare (hs : Fin 3 → List Bool) (q b n : ℕ) (Z : List Bool) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :
    HoareTime rewindProgram (fun z => z=states hs q b n Z hb hbq 2)
      (fun z => z=states hs q b n Z hb hbq 3) ((n*2^(n*b))*q+2) := by
  have hr := ReturnOrigin.return_hoare_at (fun _ => (blank : Fin 4)) 0
    ((word q b n hb hbq Z).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl
  simp only [List.length_map,word_length,zero_add] at hr
  have ha : Placement.active (FiniteReturnStackAt.placement (8 : Fin 17)) (states hs q b n Z hb hbq 2)=
      (ReturnOrigin.cfg (BinarySelectedOffsetGather.outputTape q b n Z hb hbq) ((n*2^(n*b))*q) 0).tapes := by
    rw [FiniteReturnStackAt.active_bank]; rfl
  have hh := Placement.hoare_at hr (FiniteReturnStackAt.placement (8 : Fin 17)) (states hs q b n Z hb hbq 2) ha
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank (BinarySelectedOffsetGather.outputTape q b n Z hb hbq) 0)=_
  exact FiniteReturnStackAt.replace_bank _ _ _ _

theorem width_hoare (hs : Fin 3 → List Bool) (q b n : ℕ) (Z : List Bool) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :
    HoareTime widthProgram (fun z => z=states hs q b n Z hb hbq 3)
      (fun z => z=states hs q b n Z hb hbq 4) (2*(widthBits b n).length+4) := by
  exact BinaryDescriptorCleanupList.one_hoare 3 (states hs q b n Z hb hbq 3) (widthBits b n)
    (BinaryAddressTableStep.bits_word _ _ _) rfl

theorem range_hoare (hs : Fin 3 → List Bool) (q b n : ℕ) (Z : List Bool) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :
    HoareTime rangeProgram (fun z => z=states hs q b n Z hb hbq 4)
      (fun z => z=states hs q b n Z hb hbq 5) (2*(rangeBits b n).length+4) := by
  exact BinaryDescriptorCleanupList.one_hoare 4 (states hs q b n Z hb hbq 4) (rangeBits b n)
    (BinaryAddressTableStep.bits_word _ _ _) rfl

theorem count_hoare (hs : Fin 3 → List Bool) (q b n : ℕ) (Z : List Bool) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :
    HoareTime countProgram (fun z => z=states hs q b n Z hb hbq 5)
      (fun z => z=states hs q b n Z hb hbq 6) (2*(countBits b n).length+4) := by
  exact BinaryDescriptorCleanupList.one_hoare 5 (states hs q b n Z hb hbq 5) (countBits b n)
    (BinaryAddressTableStep.bits_word _ _ _) rfl

def cost (q b n : ℕ) := (n*2^(n*b))*q+n*2^(n*b)+(n*2^(n*b))*b+
  2*((widthBits b n).length+(rangeBits b n).length+(countBits b n).length)+23

def output (hs : Fin 3 → List Bool) (q b n : ℕ) (Z : List Bool) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :=
  setTape (BinarySelectedOffsetPrepare.input hs Z) 8 (BinarySelectedOffsetGather.outputTape q b n Z hb hbq) 0

theorem final_eq (hs : Fin 3 → List Bool) (q b n : ℕ) (Z : List Bool) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :
    states hs q b n Z hb hbq 6=output hs q b n Z hb hbq := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem cleans (hs : Fin 3 → List Bool) (q b n : ℕ) (Z : List Bool) (hb : 1 ≤ b) (hbq : b+1 ≤ q) (hZ : Z.length=n) :
    HoareTime program (fun z => z=BinarySelectedOffsetGather.after hs q b n Z hb hbq)
      (fun z => z=output hs q b n Z hb hbq) (cost q b n) := by
  have h0 := (source_hoare hs q b n Z hb hbq).seq (controls_hoare hs q b n Z hb hbq hZ)
  have h1 := h0.seq (rewind_hoare hs q b n Z hb hbq)
  have h2 := h1.seq (width_hoare hs q b n Z hb hbq)
  have h3 := h2.seq (range_hoare hs q b n Z hb hbq)
  have h4 := h3.seq (count_hoare hs q b n Z hb hbq)
  rw [final_eq] at h4
  exact h4.consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.BinarySelectedOffsetCleanup
