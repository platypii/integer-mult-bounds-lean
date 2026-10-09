import IntegerMultBounds.Machine.CountedLateRepairInverse
import IntegerMultBounds.Machine.CountedLateRepairFlag
import IntegerMultBounds.Machine.CountedRepairKeyPrefix

/-! A fixed later-address guard: the original-header early guard is run on
V/W and V/U, and its two literal flags are combined and cleaned physically. -/
namespace IntegerMultBounds.Machine.CountedLateRepairGuard
noncomputable section
variable {a : ℕ}
open CountedRankSplitBank (placed_exact)
open SharedPlacementAlphabet (setTape)

def bank (V W U X : List Bool) (hs : Fin 3 → List Bool)
    (F G : ℤ → Fin (a+4)) (pf pg : ℤ) : Tapes 30 a :=
  ⟨![0,0,0,0,0,0,0,0,0,0,0,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,pf,pg],
    ![CountedGuardGadgetRecord.word V,CountedGuardGadgetRecord.word W,CountedGuardGadgetRecord.word U,CountedGuardGadgetRecord.word X,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,CountedLoopReuseAlphabet.binary (hs 0),CountedLoopReuseAlphabet.binary (hs 1),CountedLoopReuseAlphabet.binary (hs 2),fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,F,G]⟩

def flag (q b : ℕ) (V W X : List Bool) := CountedRepairKeyBank.flag q b V W X
def before (V W U X : List Bool) (hs : Fin 3 → List Bool) : Tapes 30 a :=
  bank V W U X hs (fun _ => blank) (fun _ => blank) 0 0
def first (q b : ℕ) (V W U X : List Bool) (hs : Fin 3 → List Bool) : Tapes 30 a :=
  setTape (before V W U X hs) 28 (CountedLateRepairFlag.key (flag q b V W X)) 1
def second (q b : ℕ) (V W U X : List Bool) (hs : Fin 3 → List Bool) : Tapes 30 a :=
  setTape (first q b V W U X hs) 29 (CountedLateRepairFlag.key (flag q b V U X)) 1
def after (q b : ℕ) (V W U X : List Bool) (hs : Fin 3 → List Bool) : Tapes 30 a :=
  setTape (before V W U X hs) 28
    (CountedLateRepairFlag.key (flag q b V W X || flag q b V U X)) 1

def wPlace : Fin (15+15) ≃ Fin 30 where
  toFun := ![0,1,14,15,16,17,18,19,20,12,21,22,13,11,28,2,3,4,5,6,7,8,9,10,23,24,25,26,27,29]
  invFun := ![0,1,15,16,17,18,19,20,21,22,23,13,9,12,2,3,4,5,6,7,8,10,11,24,25,26,27,28,14,29]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def uPlace : Fin (15+15) ≃ Fin 30 where
  toFun := ![0,2,14,15,16,17,18,19,20,12,21,22,13,11,29,1,3,4,5,6,7,8,9,10,23,24,25,26,27,28]
  invFun := ![0,15,1,16,17,18,19,20,21,22,23,13,9,12,2,3,4,5,6,7,8,10,11,24,25,26,27,28,29,14]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def flagPlace : Fin (2+28) ≃ Fin 30 where
  toFun := ![28,29,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27]
  invFun := ![2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0,1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem wPlace_extra_index (i : Fin 15) :
    wPlace (Fin.natAdd 15 i) = ![2,3,4,5,6,7,8,9,10,23,24,25,26,27,29] i := by
  fin_cases i <;> decide

theorem uPlace_extra_index (i : Fin 15) :
    uPlace (Fin.natAdd 15 i) = ![1,3,4,5,6,7,8,9,10,23,24,25,26,27,28] i := by
  fin_cases i <;> decide

theorem flagPlace_extra_index (i : Fin 28) :
    flagPlace (Fin.natAdd 2 i) = ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] i := by
  fin_cases i <;> decide

theorem wPlace_ne28 (i : Fin 15) :
    wPlace (Fin.natAdd 15 i) ≠ (28 : Fin 30) := by
  rw [wPlace_extra_index]; fin_cases i <;> decide

theorem uPlace_ne29 (i : Fin 15) :
    uPlace (Fin.natAdd 15 i) ≠ (29 : Fin 30) := by
  rw [uPlace_extra_index]; fin_cases i <;> decide

theorem flagPlace_ne28 (i : Fin 28) :
    flagPlace (Fin.natAdd 2 i) ≠ (28 : Fin 30) := by
  rw [flagPlace_extra_index]; fin_cases i <;> decide

theorem flagPlace_ne29 (i : Fin 28) :
    flagPlace (Fin.natAdd 2 i) ≠ (29 : Fin 30) := by
  rw [flagPlace_extra_index]; fin_cases i <;> decide

def guardW := Placement.placed (CountedGuardOriginal.program (a := a)) wPlace
def guardU := Placement.placed (CountedGuardOriginal.program (a := a)) uPlace
def combine := Placement.placed (CountedLateRepairFlag.program (a := a)) flagPlace
def program := seq (seq (guardW (a := a)) guardU) combine

theorem w_input (V W U X : List Bool) (hs : Fin 3 → List Bool) :
    Placement.active wPlace (before (a := a) V W U X hs)=
      CountedGuardOriginal.input V W (hs 1) (hs 2) (hs 0) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem w_output (q b : ℕ) (V W U X : List Bool) (hs : Fin 3 → List Bool) :
    Placement.active wPlace (first (a := a) q b V W U X hs)=
      CountedGuardOriginal.output q b X.length V W (hs 1) (hs 2) (hs 0) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem w_extra (q b : ℕ) (V W U X : List Bool) (hs : Fin 3 → List Bool) :
    Placement.extra wPlace (before (a := a) V W U X hs)=
      Placement.extra wPlace (first q b V W U X hs) := by
  unfold Placement.extra first SharedPlacementAlphabet.setTape
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [Function.update_of_ne (wPlace_ne28 i)]

theorem w_runs (q b : ℕ) (hb : 1≤b) (hbq : b+3≤q)
    (V W U X : List Bool) (hs : Fin 3 → List Bool)
    (hV : V.length=X.length*q) (hW : W.length=X.length*b)
    (hv : ∀ i, Counter.value (hs i)=CountedPackedShapeHeaders.originalValues q b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (guardW (a := a)) (fun v => v=before V W U X hs)
      (fun v => v=first q b V W U X hs) (1000*((X.length+1)*(q+b+1))) := by
  have hcost : X.length*(45*q+16*b+174)+52*q+82*b+433 ≤
      1000*((X.length+1)*(q+b+1)) := by
    simpa only [Nat.mul_assoc] using CountedGuardOriginal.cost_volume q b X.length
  have h0 := CountedGuardOriginal.runs (a := a) q b X.length V W (hs 1) (hs 2) (hs 0)
    (hv 0) (hc 0) (hv 1) (hc 1) (hv 2) (hc 2) hb hbq hV hW
  have h1 := h0.consequence (fun _ h => h) (fun _ h => h) hcost
  exact placed_exact wPlace _ _ _ _ (w_input V W U X hs)
    (w_output q b V W U X hs) (w_extra q b V W U X hs) h1

theorem u_input (q b : ℕ) (V W U X : List Bool) (hs : Fin 3 → List Bool) :
    Placement.active uPlace (first (a := a) q b V W U X hs)=
      CountedGuardOriginal.input V U (hs 1) (hs 2) (hs 0) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem u_output (q b : ℕ) (V W U X : List Bool) (hs : Fin 3 → List Bool) :
    Placement.active uPlace (second (a := a) q b V W U X hs)=
      CountedGuardOriginal.output q b X.length V U (hs 1) (hs 2) (hs 0) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem u_extra (q b : ℕ) (V W U X : List Bool) (hs : Fin 3 → List Bool) :
    Placement.extra uPlace (first (a := a) q b V W U X hs)=
      Placement.extra uPlace (second q b V W U X hs) := by
  unfold Placement.extra second SharedPlacementAlphabet.setTape
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [Function.update_of_ne (uPlace_ne29 i)]

theorem u_runs (q b : ℕ) (hb : 1≤b) (hbq : b+3≤q)
    (V W U X : List Bool) (hs : Fin 3 → List Bool)
    (hV : V.length=X.length*q) (hU : U.length=X.length*b)
    (hv : ∀ i, Counter.value (hs i)=CountedPackedShapeHeaders.originalValues q b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (guardU (a := a)) (fun v => v=first q b V W U X hs)
      (fun v => v=second q b V W U X hs) (1000*((X.length+1)*(q+b+1))) := by
  have hcost : X.length*(45*q+16*b+174)+52*q+82*b+433 ≤
      1000*((X.length+1)*(q+b+1)) := by
    simpa only [Nat.mul_assoc] using CountedGuardOriginal.cost_volume q b X.length
  have h0 := CountedGuardOriginal.runs (a := a) q b X.length V U (hs 1) (hs 2) (hs 0)
    (hv 0) (hc 0) (hv 1) (hc 1) (hv 2) (hc 2) hb hbq hV hU
  have h1 := h0.consequence (fun _ h => h) (fun _ h => h) hcost
  exact placed_exact uPlace _ _ _ _ (u_input q b V W U X hs)
    (u_output q b V W U X hs) (u_extra q b V W U X hs) h1

theorem combine_input (q b : ℕ) (V W U X : List Bool) (hs : Fin 3 → List Bool) :
    Placement.active flagPlace (second (a := a) q b V W U X hs)=
      CountedLateRepairFlag.input (flag q b V W X) (flag q b V U X) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem combine_output (q b : ℕ) (V W U X : List Bool) (hs : Fin 3 → List Bool) :
    Placement.active flagPlace (after (a := a) q b V W U X hs)=
      CountedLateRepairFlag.output (flag q b V W X) (flag q b V U X) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem combine_extra (q b : ℕ) (V W U X : List Bool) (hs : Fin 3 → List Bool) :
    Placement.extra flagPlace (second (a := a) q b V W U X hs)=
      Placement.extra flagPlace (after q b V W U X hs) := by
  unfold Placement.extra second first after SharedPlacementAlphabet.setTape
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [Function.update_of_ne (flagPlace_ne28 i),Function.update_of_ne (flagPlace_ne29 i)]

theorem combine_runs (q b : ℕ) (V W U X : List Bool) (hs : Fin 3 → List Bool) :
    HoareTime (combine (a := a)) (fun v => v=second q b V W U X hs)
      (fun v => v=after q b V W U X hs) 2 := by
  exact placed_exact flagPlace _ _ _ _ (combine_input q b V W U X hs)
    (combine_output q b V W U X hs) (combine_extra q b V W U X hs)
    (CountedLateRepairFlag.runs (flag q b V W X) (flag q b V U X))

theorem runs (q b : ℕ) (hb : 1≤b) (hbq : b+3≤q)
    (V W U X : List Bool) (hs : Fin 3 → List Bool)
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b)
    (hv : ∀ i, Counter.value (hs i)=CountedPackedShapeHeaders.originalValues q b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a)) (fun v => v=before V W U X hs)
      (fun v => v=after q b V W U X hs) (2004*((X.length+1)*(q+b+1))) := by
  have h1 := w_runs (a := a) q b hb hbq V W U X hs hV hW hv hc
  have h2 := u_runs (a := a) q b hb hbq V W U X hs hV hU hv hc
  have h3 := combine_runs (a := a) q b V W U X hs
  refine ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h) ?_
  have hp : 1≤(X.length+1)*(q+b+1) :=
    Nat.mul_pos (by omega : 0<X.length+1) (by omega : 0<q+b+1)
  omega

/-- The two early-style predicates share the same original target word;
their conjunction is exactly the late guarded set. -/
def address (q b : ℕ) (V W U X : List Bool)
    (hV : V.length=X.length*q) (hW : W.length=X.length*b)
    (hU : U.length=X.length*b) (hq : 1≤q) :
    Compact.LateAddress ((2 : ℤ)^b) ((2 : ℤ)^(q-1)) X.length :=
  (⟨(Counter.value U : ℤ),by positivity,CountedGuardGadgetValue.word_bound U X.length b hU⟩,
    CountedGuardGadgetValue.address q b X.length V W hV hW hq)

theorem flag_iff_bad (q b : ℕ) (hb : 1≤b) (hbq : b+3≤q)
    (V W X : List Bool) (hV : V.length=X.length*q) (hW : W.length=X.length*b) :
    flag q b V W X=true ↔ ¬ Compact.earlyGood ((2 : ℤ)^b) ((2 : ℤ)^(q-1)) X.length
      (CountedGuardGadgetValue.address q b X.length V W hV hW (by omega)) := by
  have h := CountedGuardOriginal.result_iff_bad (a := 0) q b X.length V W [] [] [] hb hbq hV hW
  change bitSymbol (a := 0) (flag q b V W X)=bitSymbol true ↔ _ at h
  have he (x : Bool) : (bitSymbol (a := 0) x=bitSymbol true) ↔ x=true := by
    cases x <;> simp [bitSymbol]
  rwa [he] at h

theorem combined_iff_bad (q b : ℕ) (hb : 1≤b) (hbq : b+3≤q)
    (V W U X : List Bool) (hV : V.length=X.length*q) (hW : W.length=X.length*b)
    (hU : U.length=X.length*b) :
    (flag q b V W X || flag q b V U X)=true ↔
      ¬ Compact.lateGood ((2 : ℤ)^b) ((2 : ℤ)^(q-1)) X.length
        (address q b V W U X hV hW hU (by omega)) := by
  rw [Bool.or_eq_true,flag_iff_bad q b hb hbq V W X hV hW,
    flag_iff_bad q b hb hbq V U X hV hU]
  unfold Compact.lateGood Compact.earlyGood address CountedGuardGadgetValue.address
  simp only
  tauto


end
end IntegerMultBounds.Machine.CountedLateRepairGuard
