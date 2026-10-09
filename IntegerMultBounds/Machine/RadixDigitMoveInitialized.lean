import IntegerMultBounds.Machine.RadixDigitMoveCore
import IntegerMultBounds.Machine.CleanExecution

/-! The redistribution core with paid clock installation and physical cleanup
of all private role, clock, and tracking tapes. Four input descriptors are
preserved; their generation is separate from this initialized core. -/
namespace IntegerMultBounds.Machine.RadixDigitMoveInitialized
variable {Q a n m : ℕ}
noncomputable section
open CountedLoopReuseAlphabet (binary empty)
open RadixDigitMoveCore (count)

def isClock (i : Fin 6) : Bool := i == 0 || i == 2

def controls (bs gs cs hs : List Bool) : Tapes 6 a :=
  ⟨fun i => if isClock i then 0 else 1,
   ![fun _ => blank,binary bs,fun _ => blank,binary gs,binary cs,binary hs]⟩

def bank (source : ℤ → Fin (a+4)) (bs gs cs hs : List Bool) : Tapes (count Q) a :=
  (CyclicRowCopy.payload source (fun _ _ => blank) 0 (fun _ => 0)).append (controls bs gs cs hs)

def initControls (a : ℕ) : Program 6 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun s sy => if s = 0 then some (1,fun i =>
    if isClock i then (separator,Move.right) else (sy i,Move.stay)) else none

theorem init_controls_hoare (bs gs cs hs : List Bool) :
    HoareTime (initControls a) (fun v => v = controls bs gs cs hs)
      (fun v => v = RadixDigitMoveCore.controls bs gs cs hs) 1 := by
  let last : Config 6 2 a := ⟨1,(RadixDigitMoveCore.controls (a := a) bs gs cs hs).head,
    (RadixDigitMoveCore.controls bs gs cs hs).tape⟩
  have hstep : step (initControls a) ((controls bs gs cs hs).start (initControls a)) = some last := by
    simp only [step,initControls,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> rfl
    · funext i z; fin_cases i <;>
        simp [controls,RadixDigitMoveCore.controls,isClock,empty] <;> rintro rfl <;> rfl
  rintro v rfl
  exact ⟨1,last,le_rfl,by simpa only [run_one] using hstep,by simp [step,initControls,last],rfl⟩

def initializer (Q a : ℕ) := Placement.placed (initControls a)
  (finAddFlip : Fin (6+(1+Q)) ≃ Fin ((1+Q)+6))

private theorem flip_active {s t : ℕ} (v : Tapes s a) (w : Tapes t a) :
    Placement.active (finAddFlip : Fin (t+s) ≃ Fin (s+t)) (v.append w) = w := by
  cases w
  simp [Placement.active,Tapes.append,finAddFlip_apply_castAdd]

private theorem flip_extra {s t : ℕ} (v : Tapes s a) (w : Tapes t a) :
    Placement.extra (finAddFlip : Fin (t+s) ≃ Fin (s+t)) (v.append w) = v := by
  cases v
  simp [Placement.extra,Tapes.append,finAddFlip_apply_natAdd]

theorem initialize_hoare (source : ℤ → Fin (a+4)) (bs gs cs hs : List Bool) :
    HoareTime (initializer Q a) (fun v => v = bank source bs gs cs hs)
      (fun v => v = RadixDigitMoveCore.bank source (fun _ _ => blank) 0 (fun _ => 0) bs gs cs hs) 1 := by
  let payload := CyclicRowCopy.payload source (fun _ : Fin Q => fun _ => blank) 0 (fun _ => 0)
  apply (Placement.hoare_at (init_controls_hoare (a := a) bs gs cs hs) finAddFlip
    (payload.append (controls bs gs cs hs)) (flip_active _ _)).consequence (fun _ h => h) _ le_rfl
  rintro x ⟨small,hsmall,rfl⟩
  subst small
  rw [Placement.replace,flip_extra]
  simpa only [flip_active,flip_extra,payload,RadixDigitMoveCore.bank] using Placement.view
    (finAddFlip : Fin (6+(1+Q)) ≃ Fin ((1+Q)+6))
    (payload.append (RadixDigitMoveCore.controls bs gs cs hs))

def right : Fin (count Q) → Bool := Fin.addCases (fun _ => false) (fun i => !isClock i)
def keep : Fin (count Q) → Bool := Fin.addCases (fun i => i == 0) (fun i => !isClock i)

def coreProgram (Q a : ℕ) := seq (initializer Q a) (RadixDigitMoveCore.program Q a)
def program (Q a : ℕ) := CleanExecution.program (coreProgram Q a) right keep

private theorem initial_heads (source : ℤ → Fin (a+4)) (bs gs cs hs : List Bool) :
    (bank (Q := Q) source bs gs cs hs).head = TrackedInit.position right := by
  funext i
  refine Fin.addCases (m := 1+Q) (n := 6) ?_ ?_ i
  · intro j
    refine Fin.addCases (m := 1) (n := Q) ?_ ?_ j
    · intro k; fin_cases k; simp [bank,right,Tapes.append,TrackedInit.position,CyclicRowCopy.payload]
    · intro k; simp [bank,right,Tapes.append,TrackedInit.position,CyclicRowCopy.payload]
  · intro j
    simp only [bank,Tapes.append,right,Fin.addCases_right,TrackedInit.position]
    fin_cases j <;> rfl

private theorem initial_private (source : ℤ → Fin (a+4)) (bs gs cs hs : List Bool) :
    ∀ i, keep (Q := Q) i = false → (bank source bs gs cs hs).tape i = fun _ => blank := by
  intro i
  refine Fin.addCases (m := 1+Q) (n := 6) ?_ ?_ i
  · intro j
    refine Fin.addCases (m := 1) (n := Q) ?_ ?_ j
    · intro k; fin_cases k; simp [keep,Fin.ext_iff]
    · intro k; simp [keep,bank,Tapes.append,CyclicRowCopy.payload]
  · intro j
    fin_cases j <;> simp [keep,bank,Tapes.append,controls,isClock]

private theorem retained_bank (source : ℤ → Fin (a+4)) (roles : Fin Q → ℤ → Fin (a+4))
    (bs gs cs hs : List Bool) :
    TrackedCleanupList.retained keep (RadixDigitMoveCore.bank source roles 0 (fun _ => 0) bs gs cs hs) =
      bank source bs gs cs hs := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    refine Fin.addCases (m := 1+Q) (n := 6) ?_ ?_ i
    · intro j
      refine Fin.addCases (m := 1) (n := Q) ?_ ?_ j
      · intro k; fin_cases k
        simp [TrackedCleanupList.retained,keep,RadixDigitMoveCore.bank,bank,Tapes.append,CyclicRowCopy.payload,Fin.ext_iff]
      · intro k
        simp [TrackedCleanupList.retained,keep,RadixDigitMoveCore.bank,bank,Tapes.append,CyclicRowCopy.payload,Fin.ext_iff]
    · intro j
      simp only [TrackedCleanupList.retained,keep,RadixDigitMoveCore.bank,bank,Tapes.append,Fin.addCases_right]
      fin_cases j <;> rfl

theorem redistribute_hoare (source : ℤ → Fin (a+4))
    (rows : Fin n → Fin Q → List (Fin (a+4))) (rows' : Fin m → Fin Q → List (Fin (a+4)))
    (B C : ℕ) (bs gs cs hs : List Bool)
    (hlen : ∀ i j, (rows i j).length = B) (hlen' : ∀ i j, (rows' i j).length = C)
    (hb : Counter.value bs = B) (hg : Counter.value gs = n)
    (hc : Counter.value cs = C) (hh : Counter.value hs = m)
    (hroles : ∀ j, CyclicRowSplit.roleWord rows j = CyclicRowSplit.roleWord rows' j)
    (hwords : (CyclicRowSplit.sourceWord rows).length = (CyclicRowSplit.sourceWord rows').length) :
    HoareTime (program Q a)
      (fun v => v = (bank (putWord source 0 (CyclicRowSplit.sourceWord rows)) bs gs cs hs).append (SharedBank.empty (count Q) a))
      (fun v => v = (bank (putWord source 0 (CyclicRowSplit.sourceWord rows')) bs gs cs hs).append (SharedBank.empty (count Q) a))
      ((2+5*count Q)*(2*(n*(7*(Q*B)+Q*(7*bs.length+17))+6*n+7*gs.length+16)+
       2*(m*(7*(Q*C)+Q*(7*cs.length+17))+6*m+7*hs.length+16)+5)+11*count Q+4) := by
  have h := (initialize_hoare (putWord source 0 (CyclicRowSplit.sourceWord rows)) bs gs cs hs).seq
    (RadixDigitMoveCore.redistribute_hoare source rows rows' B C bs gs cs hs hlen hlen' hb hg hc hh hroles hwords)
  have hh' := CleanExecution.realizes (coreProgram Q a) right keep _ _ _
    (initial_heads _ _ _ _ _) (initial_private _ _ _ _ _) h
  simp only [retained_bank] at hh'
  exact hh'.consequence (fun _ h => h) (fun _ h => h) (le_of_eq (by unfold count; ring))

end
end IntegerMultBounds.Machine.RadixDigitMoveInitialized
