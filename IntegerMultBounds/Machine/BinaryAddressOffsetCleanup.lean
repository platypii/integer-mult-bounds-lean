import IntegerMultBounds.Machine.BinaryAddressOffsetGather

/-! Paid cleanup of both generated input streams and all three derived
headers. The packed output is physically rewound to its origin, and the only
remaining tapes are the original q/b/n descriptors and the actual offset word. -/
namespace IntegerMultBounds.Machine.BinaryAddressOffsetCleanup
open SharedPlacementAlphabet (setTape)
open BinaryAddressOffsetData
open BinaryAddressOffsetHeaders (widthBits rangeBits countBits)
noncomputable section

def states (hs : Fin 3 → List Bool) (q b n : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) : Fin 7 → Tapes 16 0 :=
  let v0 := BinaryAddressOffsetGather.after hs q b n hb hbq
  let v1 := setTape v0 6 (fun _ => blank) 0
  let v2 := setTape v1 7 (fun _ => blank) 0
  let v3 := setTape v2 8 (BinaryAddressOffsetGather.outputTape q b n hb hbq) 0
  let v4 := setTape v3 3 (fun _ => blank) 0
  let v5 := setTape v4 4 (fun _ => blank) 0
  let v6 := setTape v5 5 (fun _ => blank) 0
  ![v0,v1,v2,v3,v4,v5,v6]

def sourceProgram := Placement.placed (EraseBack.program (a := 0)) (FiniteReturnStackAt.placement (6 : Fin 16))
def dummyProgram := Placement.placed (MarkedControlStreamReset.program (a := 0)) (FiniteReturnStackAt.placement (7 : Fin 16))
def rewindProgram := Placement.placed (ReturnOrigin.program (a := 0)) (FiniteReturnStackAt.placement (8 : Fin 16))
def widthProgram := BinaryDescriptorCleanupList.oneProgram (a := 0) (3 : Fin 16)
def rangeProgram := BinaryDescriptorCleanupList.oneProgram (a := 0) (4 : Fin 16)
def countProgram := BinaryDescriptorCleanupList.oneProgram (a := 0) (5 : Fin 16)
def program := seq (seq (seq (seq (seq sourceProgram dummyProgram) rewindProgram) widthProgram) rangeProgram) countProgram

theorem source_hoare (hs : Fin 3 → List Bool) (q b n : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :
    HoareTime sourceProgram (fun z => z=states hs q b n hb hbq 0)
      (fun z => z=states hs q b n hb hbq 1) ((n*2^(n*q))*q+2) := by
  have hr := EraseBack.erase_hoare (fun _ => (blank : Fin 4)) 0 ((source q n).map bitSymbol)
    (ReturnOrigin.bits_nonblank _) rfl (by intros; rfl)
  simp only [List.length_map,source_length,zero_add] at hr
  have ha : Placement.active (FiniteReturnStackAt.placement (6 : Fin 16)) (states hs q b n hb hbq 0)=
      (EraseBack.cfg (putWord (fun _ => blank) 0 ((source q n).map bitSymbol)) ((n*2^(n*q))*q) 0).tapes := by
    rw [FiniteReturnStackAt.active_bank]; rfl
  have hh := Placement.hoare_at hr (FiniteReturnStackAt.placement (6 : Fin 16)) (states hs q b n hb hbq 0) ha
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank (fun _ => blank) 0)=_
  exact FiniteReturnStackAt.replace_bank _ _ _ _

theorem dummy_hoare (hs : Fin 3 → List Bool) (q b n : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :
    HoareTime dummyProgram (fun z => z=states hs q b n hb hbq 1)
      (fun z => z=states hs q b n hb hbq 2) (n*2^(n*q)+2) := by
  have hr := MarkedControlStreamReset.resets ((dummy q n).map (bitSymbol (a := 0)))
    (by intro x hx; obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx; cases b <;> decide)
  simp only [List.length_map,dummy_length,←BinaryAddressTableStep.binary_word] at hr
  have ha : Placement.active (FiniteReturnStackAt.placement (7 : Fin 16)) (states hs q b n hb hbq 1)=
      MarkedWordCleanup.one (CountedCopyReuse.binary (dummy q n)) (1+n*2^(n*q)) := by
    rw [FiniteReturnStackAt.active_bank]; rfl
  have hh := Placement.hoare_at hr (FiniteReturnStackAt.placement (7 : Fin 16)) (states hs q b n hb hbq 1) ha
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank (fun _ => blank) 0)=_
  exact FiniteReturnStackAt.replace_bank _ _ _ _

theorem rewind_hoare (hs : Fin 3 → List Bool) (q b n : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :
    HoareTime rewindProgram (fun z => z=states hs q b n hb hbq 2)
      (fun z => z=states hs q b n hb hbq 3) ((n*2^(n*q))*b+2) := by
  have hr := ReturnOrigin.return_hoare_at (fun _ => (blank : Fin 4)) 0
    ((word q b n hb hbq).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl
  simp only [List.length_map,word_length,zero_add] at hr
  have ha : Placement.active (FiniteReturnStackAt.placement (8 : Fin 16)) (states hs q b n hb hbq 2)=
      (ReturnOrigin.cfg (BinaryAddressOffsetGather.outputTape q b n hb hbq) ((n*2^(n*q))*b) 0).tapes := by
    rw [FiniteReturnStackAt.active_bank]; rfl
  have hh := Placement.hoare_at hr (FiniteReturnStackAt.placement (8 : Fin 16)) (states hs q b n hb hbq 2) ha
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank (BinaryAddressOffsetGather.outputTape q b n hb hbq) 0)=_
  exact FiniteReturnStackAt.replace_bank _ _ _ _

theorem width_hoare (hs : Fin 3 → List Bool) (q b n : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :
    HoareTime widthProgram (fun z => z=states hs q b n hb hbq 3)
      (fun z => z=states hs q b n hb hbq 4) (2*(widthBits q n).length+4) := by
  exact BinaryDescriptorCleanupList.one_hoare 3 (states hs q b n hb hbq 3) (widthBits q n)
    (BinaryAddressTableStep.bits_word _ _ _) rfl

theorem range_hoare (hs : Fin 3 → List Bool) (q b n : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :
    HoareTime rangeProgram (fun z => z=states hs q b n hb hbq 4)
      (fun z => z=states hs q b n hb hbq 5) (2*(rangeBits q n).length+4) := by
  exact BinaryDescriptorCleanupList.one_hoare 4 (states hs q b n hb hbq 4) (rangeBits q n)
    (BinaryAddressTableStep.bits_word _ _ _) rfl

theorem count_hoare (hs : Fin 3 → List Bool) (q b n : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :
    HoareTime countProgram (fun z => z=states hs q b n hb hbq 5)
      (fun z => z=states hs q b n hb hbq 6) (2*(countBits q n).length+4) := by
  exact BinaryDescriptorCleanupList.one_hoare 5 (states hs q b n hb hbq 5) (countBits q n)
    (BinaryAddressTableStep.bits_word _ _ _) rfl

def cost (q b n : ℕ) := (n*2^(n*q))*q+n*2^(n*q)+(n*2^(n*q))*b+
  2*((widthBits q n).length+(rangeBits q n).length+(countBits q n).length)+23

def output (hs : Fin 3 → List Bool) (q b n : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :=
  setTape (BinaryAddressOffsetHeaders.bank hs) 8 (BinaryAddressOffsetGather.outputTape q b n hb hbq) 0

theorem final_eq (hs : Fin 3 → List Bool) (q b n : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :
    states hs q b n hb hbq 6=output hs q b n hb hbq := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem cleans (hs : Fin 3 → List Bool) (q b n : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :
    HoareTime program (fun z => z=BinaryAddressOffsetGather.after hs q b n hb hbq)
      (fun z => z=output hs q b n hb hbq) (cost q b n) := by
  have h0 := (source_hoare hs q b n hb hbq).seq (dummy_hoare hs q b n hb hbq)
  have h1 := h0.seq (rewind_hoare hs q b n hb hbq)
  have h2 := h1.seq (width_hoare hs q b n hb hbq)
  have h3 := h2.seq (range_hoare hs q b n hb hbq)
  have h4 := h3.seq (count_hoare hs q b n hb hbq)
  rw [final_eq] at h4
  exact h4.consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.BinaryAddressOffsetCleanup
