import IntegerMultBounds.Machine.NativePolynomialConjugationWorkspace
import IntegerMultBounds.Machine.CompactComplexSourceReadyDirection
import IntegerMultBounds.Machine.FiniteReturnGuard

/-! A fixed physical orientation selector reads the genuine saved call frame.
Empty root stacks select identity; saved inverse calls select native source65
conjugation. The guard and decoder restore the stack before either branch. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyOrientation
noncomputable section
open Networks
open CompactComplexSourceReadyWorkspace (tapes)
open CompactComplexSourceReadyDirection (width room directionTag addressDirection select)
open NativePolynomialConjugationData (array)
open SharedPlacementAlphabet (setTape)
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
variable {s c : ℕ}
attribute [local irreducible] CompactComplexSourceReadyDirection.width
  FiniteReturnStack.encode CompactComplexSourceReadyDirection.terminalFor
  ComplexRank25.program ComplexRecursiveCallSchema.sites
  CompactComplexCallReturn.addressCount

def source := NativePolynomialConjugationWorkspace.source (s:=s) (c:=c)
theorem positive : 0<tapes s c := Nat.zero_lt_of_lt (source (s:=s) (c:=c)).isLt

def branchPrograms : Fin 2 → Σ q,Program (tapes s c) q 2 :=
  ![⟨1,skip (tapes s c) 2 positive⟩,⟨_,NativePolynomialConjugationWorkspace.program s c⟩]
def branchStates := fun pc : Fin 2 => (branchPrograms (s:=s) (c:=c) pc).1
def branchFamily := fun pc : Fin 2 => (branchPrograms (s:=s) (c:=c) pc).2

def childProgram (stack : Fin (tapes s c)) :=
  FiniteDispatch.program (CompactComplexSourceReadyDirection.peekProgram stack)
    branchStates branchFamily select

def guardPrograms (stack : Fin (tapes s c)) : Fin 2 → Σ q,Program (tapes s c) q 2 :=
  ![⟨1,skip (tapes s c) 2 positive⟩,⟨_,childProgram stack⟩]
def guardStates (stack : Fin (tapes s c)) := fun pc : Fin 2 => (guardPrograms stack pc).1
def guardFamily (stack : Fin (tapes s c)) := fun pc : Fin 2 => (guardPrograms stack pc).2

def guardSelect (st : Fin 4) : Option (Fin 2) :=
  if st=2 then some 0 else if st=3 then some 1 else none

def program (stack : Fin (tapes s c)) :=
  FiniteDispatch.program (FiniteReturnGuard.program stack) (guardStates stack) (guardFamily stack) guardSelect

def output {N : ℕ} (call : ComplexRecursiveCallSchema.Call) (v : Tapes (tapes s c) 2)
    (f : Fin N → ButterflyStreamData.Coefficient) :=
  if call.inverse then setTape v source (NativeZeroPadding.word (NativeZeroPaddingArray.word (array f))) 0 else v

theorem child_runs (stack : Fin (tapes s c)) (call : ComplexRecursiveCallSchema.Call)
    (v : Tapes (tapes s c) 2) (older : ℤ → Fin 6) (p : ℤ)
    (hstack : Placement.active (FiniteReturnStackAt.placement stack) v=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart older p
        (FiniteReturnStack.address room (CompactComplexScheduledPCDecode.callAddress call)) width le_rfl) (p+width))
    (sh : Shape) (rows ell precision : ℕ) (hr : 0<rows) (f : Array sh rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh precision ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh precision)
    (hs : v.tape source=NativeZeroPadding.word (NativeZeroPaddingArray.word f)) (hh : v.head source=0) :
    HoareTime (childProgram stack) (fun w => w=v) (fun w => w=output call v f)
      (2*width+3+5*CompactNativeRoleTransferBudget.volume rows sh ell precision) := by
  obtain ⟨out,hrun,hhalt,htapes,hselect⟩ :=
    CompactComplexSourceReadyDirection.local_runsFor 2 room addressDirection
      (CompactComplexScheduledPCDecode.callAddress call) older p
  have hrun' : run (CompactComplexSourceReadyDirection.Peek.program 2 width) (2*width+2)
      ((Placement.active (FiniteReturnStackAt.placement stack) v).start
        (CompactComplexSourceReadyDirection.Peek.program 2 width))=some out := by
    rw [hstack]
    exact hrun
  have hp := Placement.placed_run _ (FiniteReturnStackAt.placement stack) v hrun'
  have hh' := Placement.placed_halt _ (FiniteReturnStackAt.placement stack) v hhalt
  have hv : (Placement.result (FiniteReturnStackAt.placement stack) v out).tapes=v := by
    rw [Placement.result_tapes,htapes,←hstack,Placement.replace_active]
  have hsel : select out.state=some (directionTag call) := hselect.trans
    (congrArg (Option.map directionTag) (CompactComplexScheduledPCDecode.decodeCall_actual call))
  have hb : HoareTime (branchFamily (s:=s) (c:=c) (directionTag call))
      (fun w => w=v) (fun w => w=output call v f)
      (5*CompactNativeRoleTransferBudget.volume rows sh ell precision) := by
    cases hi : call.inverse
    · have ht : directionTag call=0 := by unfold directionTag; rw [hi]; rfl
      rw [ht]
      simpa [hi,Bool.false_eq_true,↓reduceIte,branchFamily,branchPrograms,
        Matrix.cons_val_zero,output] using
        (skip_hoare positive v).consequence (fun _ h => h) (fun _ h => h) (by omega : 0≤5*CompactNativeRoleTransferBudget.volume rows sh ell precision)
    · have ht : directionTag call=1 := by unfold directionTag; rw [hi]; rfl
      rw [ht]
      simpa [hi,↓reduceIte,branchFamily,branchPrograms,Matrix.cons_val_one,
        Matrix.cons_val_zero,output,source,NativePolynomialConjugationWorkspace.program] using
        NativePolynomialConjugationRows.runs_linear source v sh rows ell precision hr f hw hs hh
  have hb' : HoareTime (branchFamily (s:=s) (c:=c) (directionTag call))
      (fun w => w=(Placement.result (FiniteReturnStackAt.placement stack) v out).tapes)
      (fun w => w=output call v f)
      (5*CompactNativeRoleTransferBudget.volume rows sh ell precision) := by
    simpa only [hv] using hb
  exact FiniteDispatch.hoare_selected _ branchStates branchFamily select v _ (directionTag call)
    (2*width+2) _ _ hp hh' hsel hb'

theorem root_runs (stack : Fin (tapes s c)) (v : Tapes (tapes s c) 2)
    (hb : v.tape stack (v.head stack-1)=blank) :
    HoareTime (program stack) (fun w => w=v) (fun w => w=v) 3 := by
  have hr := FiniteReturnGuard.exact_run stack v
  rw [hb] at hr
  simp only [decide_true] at hr
  exact FiniteDispatch.hoare_selected _ (guardStates stack) (guardFamily stack) guardSelect v
    (FiniteReturnGuard.terminal v true) 0 2 0 _ hr (FiniteReturnGuard.terminal_halt stack v true)
    (by rfl) (skip_hoare positive v)

private theorem width_pos_generic {N k : ℕ} (hr : N≤2^k) (hN : 2≤N) : 0<k := by
  by_contra h
  have hk : k=0 := by omega
  rw [hk] at hr
  simp only [pow_zero] at hr
  omega

private theorem originalCount_eq : CompactComplexScheduledPCLayout.originalCount=
    ComplexRecursiveCallSchema.sites.length*(25^3) := by
  exact congrFun (congrFun (show CompactComplexCallReturn.addressCount=(fun x y => x*y) from by
    unfold CompactComplexCallReturn.addressCount; rfl)
    ComplexRecursiveCallSchema.sites.length) (25^3)

private theorem mul_two_le (L A : ℕ) (hL : 1≤L) (hA : 2≤A) : 2≤L*A :=
  hA.trans (by simpa only [one_mul] using Nat.mul_le_mul_right A hL)

theorem width_positive (call : ComplexRecursiveCallSchema.Call) : 0<width := by
  have hs : 1≤ComplexRecursiveCallSchema.sites.length := Nat.succ_le_of_lt
    (Nat.zero_lt_of_lt call.site.isLt)
  have hn : 2≤CompactComplexScheduledPCLayout.originalCount := by
    rw [originalCount_eq]
    exact mul_two_le _ _ hs (by decide)
  exact width_pos_generic (N:=CompactComplexScheduledPCLayout.originalCount) (k:=width) room hn

theorem saved_occupied (stack : Fin (tapes s c)) (call : ComplexRecursiveCallSchema.Call)
    (v : Tapes (tapes s c) 2) (older : ℤ → Fin 6) (p : ℤ)
    (hstack : Placement.active (FiniteReturnStackAt.placement stack) v=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart older p
        (FiniteReturnStack.address room (CompactComplexScheduledPCDecode.callAddress call)) width le_rfl) (p+width)) :
    v.tape stack (v.head stack-1)≠blank := by
  rw [FiniteReturnStackAt.active_bank] at hstack
  have hh := congrArg (fun b : Tapes 1 2 => b.head 0) hstack
  have ht := congrArg (fun b : Tapes 1 2 => b.tape 0) hstack
  simp only [FiniteReturnStack.bank] at hh ht
  rw [hh,ht]
  have hw := width_positive call
  have he : p+(width:ℤ)-1=p+((width-1:ℕ):ℤ) := by omega
  rw [he,FiniteReturnStack.prefix_at older p _ width le_rfl ⟨width-1,by omega⟩]
  generalize FiniteReturnStack.address room (CompactComplexScheduledPCDecode.callAddress call)
    ⟨width-1,by omega⟩ = b
  cases b <;> decide

theorem runs (stack : Fin (tapes s c)) (call : ComplexRecursiveCallSchema.Call)
    (v : Tapes (tapes s c) 2) (older : ℤ → Fin 6) (p : ℤ)
    (hstack : Placement.active (FiniteReturnStackAt.placement stack) v=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart older p
        (FiniteReturnStack.address room (CompactComplexScheduledPCDecode.callAddress call)) width le_rfl) (p+width))
    (sh : Shape) (rows ell precision : ℕ) (hr : 0<rows) (f : Array sh rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh precision ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh precision)
    (hs : v.tape source=NativeZeroPadding.word (NativeZeroPaddingArray.word f)) (hh : v.head source=0) :
    HoareTime (program stack) (fun w => w=v) (fun w => w=output call v f)
      (2*width+6+5*CompactNativeRoleTransferBudget.volume rows sh ell precision) := by
  have hb := saved_occupied stack call v older p hstack
  have hg := FiniteReturnGuard.exact_run stack v
  rw [show decide (v.tape stack (v.head stack-1)=blank)=false by simp [hb]] at hg
  have h := FiniteDispatch.hoare_selected _ (guardStates stack) (guardFamily stack) guardSelect v
    (FiniteReturnGuard.terminal v false) 1 2 _ _ hg (FiniteReturnGuard.terminal_halt stack v false)
    (by rfl) (child_runs stack call v older p hstack sh rows ell precision hr f hw hs hh)
  exact h.consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem runs_saved (stack : Fin (tapes s c)) (call : ComplexRecursiveCallSchema.Call)
    (v : Tapes (tapes s c) 2) (older : ℤ → Fin 6) (p : ℤ)
    (hstack : Placement.active (FiniteReturnStackAt.placement stack) v=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart older p (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (p+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)))
    (sh : Shape) (rows ell precision : ℕ) (hr : 0<rows) (f : Array sh rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh precision ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh precision)
    (hs : v.tape source=NativeZeroPadding.word (NativeZeroPaddingArray.word f)) (hh : v.head source=0) :
    HoareTime (program stack) (fun w => w=v) (fun w => w=output call v f)
      (2*width+6+5*CompactNativeRoleTransferBudget.volume rows sh ell precision) :=
  runs stack call v older p (hstack.trans (CompactComplexSourceReadyDirection.saved_bank_eq call older p).symm)
    sh rows ell precision hr f hw hs hh

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyOrientation
