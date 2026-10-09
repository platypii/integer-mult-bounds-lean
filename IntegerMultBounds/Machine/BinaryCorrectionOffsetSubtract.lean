import IntegerMultBounds.Machine.BinaryCorrectionOffsetLoop
import IntegerMultBounds.Machine.BinaryAddressOffsetRepeat

/-! Complete physical rowwise subtraction with blank initial workspace.
Both operand tables are consumed and erased; only the output table and the
original runtime width/count descriptors remain, all heads restored. -/
namespace IntegerMultBounds.Machine.BinaryCorrectionOffsetSubtract
open SharedPlacementAlphabet (setTape)
open CountedCopyReuse (empty binary)
open BinaryCorrectionOffsetLoop (left right result Uniform)
open BinaryCorrectionOffsetRow (word)
noncomputable section

def raw (f g out : ℤ → Fin 4) (p q r : ℤ) (ws ns : List Bool) : Tapes 9 0 :=
  ⟨![p,q,r,0,0,0,1,0,1],![f,g,out,(fun _ => blank),(fun _ => blank),(fun _ => blank),binary ws,(fun _ => blank),binary ns]⟩
def bank (f g out : ℤ → Fin 4) (p q r : ℤ) (ws ns : List Bool) := BinaryCorrectionOffsetLoop.bank f g out p q r ws ns

def oneInit (slot : Fin 9) := Placement.placed (RecursiveChildQuotientsConstant.program (a := 0) 0)
  (FiniteReturnStackAt.placement slot)
def setup := seq (oneInit 5) (oneInit 7)
def clocks : List (Fin 9) := [5,7]
def clearClocks := BinaryDescriptorCleanupList.program (a := 0) (by decide : 0<9) clocks
def eraseLeft := Placement.placed (EraseBack.program (a := 0)) (FiniteReturnStackAt.placement (0 : Fin 9))
def eraseRight := Placement.placed (EraseBack.program (a := 0)) (FiniteReturnStackAt.placement (1 : Fin 9))
def rewind := Placement.placed (ReturnOrigin.program (a := 0)) (FiniteReturnStackAt.placement (2 : Fin 9))
def program := seq (seq (seq (seq (seq setup BinaryCorrectionOffsetLoop.program) clearClocks) eraseLeft) eraseRight) rewind

theorem init_hoare (slot : Fin 9) (v : Tapes 9 0) (ht : v.tape slot=fun _ => blank) (hh : v.head slot=0) :
    HoareTime (oneInit slot) (fun z => z=v) (fun z => z=setTape v slot empty 1) 6 := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := 0) 0)
    (FiniteReturnStackAt.placement slot) v (by rw [FiniteReturnStackAt.active_bank,ht,hh])
  apply h.consequence (fun _ h => h) _ (by decide)
  rintro z ⟨small,rfl,rfl⟩
  exact FiniteReturnStackAt.replace_bank _ _ _ _

theorem setup_hoare (f g out : ℤ → Fin 4) (p q r : ℤ) (ws ns : List Bool) :
    HoareTime setup (fun z => z=raw f g out p q r ws ns) (fun z => z=bank f g out p q r ws ns) 13 := by
  have h0 := init_hoare 5 (raw f g out p q r ws ns) rfl rfl
  have h1 := init_hoare 7 (setTape (raw f g out p q r ws ns) 5 empty 1) rfl rfl
  have he : setTape (setTape (raw f g out p q r ws ns) 5 empty 1) 7 empty 1=bank f g out p q r ws ns := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h1
  exact h0.seq h1

theorem clear_clocks (f g out : ℤ → Fin 4) (p q r : ℤ) (ws ns : List Bool) :
    HoareTime clearClocks (fun z => z=bank f g out p q r ws ns) (fun z => z=raw f g out p q r ws ns) 10 := by
  have h := BinaryDescriptorCleanupList.cleanup_hoare (by decide : 0<9) clocks (by decide)
    (fun _ => []) (bank f g out p q r ws ns) (by
      intro i hi
      simp only [clocks,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl <;> exact ⟨rfl,rfl⟩)
  have he : BinaryDescriptorCleanupList.cleared clocks (bank f g out p q r ws ns)=raw f g out p q r ws ns := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  simpa only [he,clearClocks,show BinaryDescriptorCleanupList.cost clocks (fun _ => [])=10 by decide] using h

theorem erase_left (xs : List Bool) (g out : ℤ → Fin 4) (q r : ℤ) (ws ns : List Bool) :
    HoareTime eraseLeft (fun z => z=raw (word xs) g out xs.length q r ws ns)
      (fun z => z=raw (fun _ => blank) g out 0 q r ws ns) (xs.length+2) := by
  have h := EraseBack.erase_hoare (fun _ => (blank : Fin 4)) 0 (xs.map bitSymbol)
    (ReturnOrigin.bits_nonblank xs) rfl (by intros; rfl)
  simp only [List.length_map,zero_add] at h
  have ha : Placement.active (FiniteReturnStackAt.placement (0 : Fin 9)) (raw (word xs) g out xs.length q r ws ns)=
      (EraseBack.cfg (word xs) xs.length 0).tapes := by rw [FiniteReturnStackAt.active_bank]; rfl
  apply (Placement.hoare_at h _ _ ha).consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank (fun _ => blank) 0)=_
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem erase_right (ys : List Bool) (f out : ℤ → Fin 4) (p r : ℤ) (ws ns : List Bool) :
    HoareTime eraseRight (fun z => z=raw f (word ys) out p ys.length r ws ns)
      (fun z => z=raw f (fun _ => blank) out p 0 r ws ns) (ys.length+2) := by
  have h := EraseBack.erase_hoare (fun _ => (blank : Fin 4)) 0 (ys.map bitSymbol)
    (ReturnOrigin.bits_nonblank ys) rfl (by intros; rfl)
  simp only [List.length_map,zero_add] at h
  have ha : Placement.active (FiniteReturnStackAt.placement (1 : Fin 9)) (raw f (word ys) out p ys.length r ws ns)=
      (EraseBack.cfg (word ys) ys.length 0).tapes := by rw [FiniteReturnStackAt.active_bank]; rfl
  apply (Placement.hoare_at h _ _ ha).consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank (fun _ => blank) 0)=_
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem rewinds (xs : List Bool) (f g : ℤ → Fin 4) (p q : ℤ) (ws ns : List Bool) :
    HoareTime rewind (fun z => z=raw f g (word xs) p q xs.length ws ns)
      (fun z => z=raw f g (word xs) p q 0 ws ns) (xs.length+2) := by
  have h := ReturnOrigin.return_hoare_at (fun _ => (blank : Fin 4)) 0 (xs.map bitSymbol)
    (ReturnOrigin.bits_nonblank xs) rfl
  simp only [List.length_map,zero_add] at h
  have ha : Placement.active (FiniteReturnStackAt.placement (2 : Fin 9)) (raw f g (word xs) p q xs.length ws ns)=
      (ReturnOrigin.cfg (word xs) xs.length 0).tapes := by rw [FiniteReturnStackAt.active_bank]; rfl
  apply (Placement.hoare_at h _ _ ha).consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank (word xs) 0)=_
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def cost (W N : ℕ) (ws ns : List Bool) := BinaryCorrectionOffsetLoop.cost W N ws ns+3*(N*W)+34

theorem runs (rows : List (List Bool × List Bool)) (W : ℕ) (hu : Uniform W rows) (ws ns : List Bool)
    (hw : Counter.value ws=W) (hn : Counter.value ns=rows.length) :
    HoareTime program (fun z => z=raw (word (left rows)) (word (right rows)) (fun _ => blank) 0 0 0 ws ns)
      (fun z => z=raw (fun _ => blank) (fun _ => blank) (word (result rows)) 0 0 0 ws ns)
      (cost W rows.length ws ns) := by
  have hleft : (left rows).length=rows.length*W := by
    rw [left,BlockRotationData.uniform_volume W _ (BinaryCorrectionOffsetLoop.left_uniform W rows hu),List.length_map]
  have hright : (right rows).length=rows.length*W := by
    rw [right,BlockRotationData.uniform_volume W _ (BinaryCorrectionOffsetLoop.right_uniform W rows hu),List.length_map]
  have hout := BinaryCorrectionOffsetLoop.result_length W rows hu
  have h0 := setup_hoare (word (left rows)) (word (right rows)) (fun _ => blank) 0 0 0 ws ns
  have h1 := BinaryCorrectionOffsetLoop.runs rows W hu (fun _ => blank) (fun _ => blank) (fun _ => blank) 0 0 0 ws ns hw hn
  simp only [zero_add] at h1
  have h2 := clear_clocks (word (left rows)) (word (right rows)) (word (result rows)) (rows.length*W) (rows.length*W) (rows.length*W) ws ns
  have h3 := erase_left (left rows) (word (right rows)) (word (result rows)) (rows.length*W) (rows.length*W) ws ns
  have h4 := erase_right (right rows) (fun _ => blank) (word (result rows)) 0 (rows.length*W) ws ns
  have h5 := rewinds (result rows) (fun _ => blank) (fun _ => blank) 0 0 ws ns
  rw [hleft] at h3
  rw [hright] at h4
  rw [hout] at h5
  exact ((((h0.seq h1).seq h2).seq h3).seq h4 |>.seq h5).consequence
    (fun _ h => h) (fun _ h => h) (by unfold cost; omega)


theorem cost_linear (W N : ℕ) (ws ns : List Bool) (hN : 0<N)
    (hw : Counter.value ws=W) (hn : Counter.value ns=N)
    (cw : GrowingCounterData.Canonical ws) (cn : GrowingCounterData.Canonical ns) :
    cost W N ws ns≤160*(N*(W+1)) := by
  have hlw := GrowingCounterData.canonical_width ws cw
  have hln := GrowingCounterData.canonical_width ns cn
  rw [hw] at hlw
  rw [hn] at hln
  have hwlog := Nat.log2_le_self W
  have hnlog := Nat.log2_le_self N
  have hcost : 15*W+14*ws.length+52≤29*W+66 := by omega
  have hmul := Nat.mul_le_mul_left N hcost
  unfold cost BinaryCorrectionOffsetLoop.cost
  nlinarith

end
end IntegerMultBounds.Machine.BinaryCorrectionOffsetSubtract
