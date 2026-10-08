import IntegerMultBounds.Machine.TrackedCleanupAt
import IntegerMultBounds.Machine.TrackedHoare

/-! A fixed finite cleanup list for a tracked execution. Every private data
pair is erased; retained common data and heads are framed unchanged while
only their trackers are erased. All tape visits and list joins are charged. -/
namespace IntegerMultBounds.Machine.TrackedCleanupList
open SharedPlacementAlphabet (setTape)
variable {t a : ℕ}
noncomputable section

def retained (keep : Fin t → Bool) (v : Tapes t a) : Tapes t a :=
  ⟨fun i => if keep i then v.head i else 0,
   fun i => if keep i then v.tape i else fun _ => blank⟩

def result (keep : Fin t → Bool) (v : Tapes t a) (lo hi : Fin t → ℤ) (n : ℕ) : Tapes (t+t) a :=
  (⟨fun i => if i.val < n ∧ keep i = false then 0 else v.head i,
    fun i => if i.val < n ∧ keep i = false then (fun _ => blank) else v.tape i⟩ : Tapes t a).append
  ⟨fun i => if i.val < n then 0 else v.head i,
   fun i => if i.val < n then (fun _ => blank) else TrackedCleanup.tracker (lo i) (hi i)⟩

theorem data_ne_tracker (j : Fin t) : Fin.castAdd t j ≠ Fin.natAdd t j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  have hj := j.isLt
  omega

private theorem data_ne_any_tracker (i j : Fin t) : Fin.castAdd t i ≠ Fin.natAdd t j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  have hi := i.isLt
  omega

def stage (keep : Fin t → Bool) (j : Fin t) : Program (t+t) 4 a :=
  if keep j then TrackedCleanupAt.singleProgram (Fin.natAdd t j)
  else TrackedCleanupAt.pairProgram (Fin.castAdd t j) (Fin.natAdd t j) (data_ne_tracker j)

private theorem result_single (keep : Fin t → Bool) (v : Tapes t a) (lo hi : Fin t → ℤ)
    (j : Fin t) (hk : keep j = true) :
    setTape (result keep v lo hi j.val) (Fin.natAdd t j) (fun _ => blank) 0 =
      result keep v lo hi (j.val+1) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases with
  | left i =>
    by_cases hij : i = j
    · subst i; simp [-Fin.natAdd_eq_addNat,result,Tapes.append,hk,data_ne_any_tracker]
    · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
      have he : i < j ↔ i ≤ j := by change i.val < j.val ↔ i.val ≤ j.val; omega
      simp [-Fin.natAdd_eq_addNat,result,Tapes.append,he,data_ne_any_tracker]
  | right i =>
    by_cases hij : i = j
    · subst i; simp [-Fin.natAdd_eq_addNat,result,Tapes.append]
    · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
      have he : i < j ↔ i ≤ j := by change i.val < j.val ↔ i.val ≤ j.val; omega
      simp [-Fin.natAdd_eq_addNat,result,Tapes.append,hij,he]

private theorem result_pair (keep : Fin t → Bool) (v : Tapes t a) (lo hi : Fin t → ℤ)
    (j : Fin t) (hk : keep j = false) :
    setTape (setTape (result keep v lo hi j.val) (Fin.castAdd t j) (fun _ => blank) 0)
      (Fin.natAdd t j) (fun _ => blank) 0 = result keep v lo hi (j.val+1) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases with
  | left i =>
    by_cases hij : i = j
    · subst i; simp [-Fin.natAdd_eq_addNat,result,setTape,Tapes.append,hk,data_ne_any_tracker]
    · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
      have he : i < j ↔ i ≤ j := by change i.val < j.val ↔ i.val ≤ j.val; omega
      simp [-Fin.natAdd_eq_addNat,result,setTape,Tapes.append,hij,he,data_ne_any_tracker]
  | right i =>
    have hn : Fin.natAdd t i ≠ Fin.castAdd t j := by
      intro h; have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
      have hj := j.isLt
      omega
    by_cases hij : i = j
    · subst i; simp [-Fin.natAdd_eq_addNat,result,setTape,Tapes.append]
    · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
      have he : i < j ↔ i ≤ j := by change i.val < j.val ↔ i.val ≤ j.val; omega
      simp [-Fin.natAdd_eq_addNat,result,setTape,Tapes.append,hij,he,hn]

theorem stage_hoare (keep : Fin t → Bool) (v : Tapes t a) (lo hi : Fin t → ℤ)
    (B : ℕ) (hs : TrackedHoare.Intervals v lo hi B (fun i => keep i = false)) (j : Fin t) :
    HoareTime (stage keep j) (fun w => w = result keep v lo hi j.val)
      (fun w => w = result keep v lo hi (j.val+1)) (5*B+5) := by
  obtain ⟨hlo,hl,hh,hhi,hpl,hph⟩ := hs.1 j
  cases hk : keep j with
  | false =>
    have hc := TrackedCleanupAt.pair_hoare (Fin.castAdd t j) (Fin.natAdd t j) (data_ne_tracker j)
      (result keep v lo hi j.val) (lo j) (hi j) B hl hh
      (by simpa [-Fin.natAdd_eq_addNat,result,Tapes.append] using And.intro hpl hph) hlo hhi
      (by simp [-Fin.natAdd_eq_addNat,result,Tapes.append]) (by simp [-Fin.natAdd_eq_addNat,result,Tapes.append])
      (by simpa [-Fin.natAdd_eq_addNat,result,Tapes.append] using hs.2 j hk)
    simpa only [stage,hk,Bool.false_eq_true,ite_false,result_pair keep v lo hi j hk] using hc
  | true =>
    have hc := TrackedCleanupAt.single_hoare (Fin.natAdd t j)
      (result keep v lo hi j.val) (lo j) (hi j) B hl hh
      (by simpa [-Fin.natAdd_eq_addNat,result,Tapes.append] using And.intro hpl hph) hlo hhi
      (by simp [-Fin.natAdd_eq_addNat,result,Tapes.append])
    simpa only [stage,hk,ite_true,result_single keep v lo hi j hk] using hc

def states : ℕ → ℕ
  | 0 => 1
  | n+1 => states n+4

private def haltProgram (ht : 0 < t) : Program (t+t) 1 a :=
  ⟨by omega,0,fun _ _ => none⟩

def initialStages (keep : Fin t → Bool) (ht : 0 < t) :
    (n : ℕ) → n ≤ t → Program (t+t) (states n) a
  | 0,_ => haltProgram ht
  | n+1,hn => seq (initialStages keep ht n (by omega)) (stage keep ⟨n,by omega⟩)

def program (keep : Fin t → Bool) (ht : 0 < t) := initialStages (a := a) keep ht t le_rfl

theorem initialStages_hoare (keep : Fin t → Bool) (ht : 0 < t) (v : Tapes t a)
    (lo hi : Fin t → ℤ) (B : ℕ) (hs : TrackedHoare.Intervals v lo hi B (fun i => keep i = false))
    (n : ℕ) (hn : n ≤ t) :
    HoareTime (initialStages keep ht n hn) (fun w => w = result keep v lo hi 0)
      (fun w => w = result keep v lo hi n) (n*(5*B+6)) := by
  induction n with
  | zero => rintro w rfl; exact ⟨0,_,by omega,rfl,rfl,rfl⟩
  | succ n ih =>
    have hc := (ih (by omega)).seq (stage_hoare keep v lo hi B hs ⟨n,by omega⟩)
    exact hc.consequence (fun _ h => h) (fun _ h => h) (le_of_eq (by ring))

theorem result_zero (keep : Fin t → Bool) (v : Tapes t a) (lo hi : Fin t → ℤ) :
    result keep v lo hi 0 = TrackedHoare.bank v lo hi := by
  cases v
  simp [result,TrackedHoare.bank]

theorem result_all (keep : Fin t → Bool) (v : Tapes t a) (lo hi : Fin t → ℤ) :
    result keep v lo hi t = (retained keep v).append (SharedBank.empty t a) := by
  unfold result retained SharedBank.empty
  simp only [Fin.isLt,ite_true,true_and]
  congr 2 <;> funext i <;> cases keep i <;> rfl

/-- Fixed machine, exact clean bank, and one charged join per original tape.
Runtime interval boundaries are read from trackers, never built into control. -/
theorem cleanup_hoare (keep : Fin t → Bool) (ht : 0 < t) (v : Tapes t a)
    (lo hi : Fin t → ℤ) (B : ℕ) (hs : TrackedHoare.Intervals v lo hi B (fun i => keep i = false)) :
    HoareTime (program keep ht) (fun w => w = TrackedHoare.bank v lo hi)
      (fun w => w = (retained keep v).append (SharedBank.empty t a)) (t*(5*B+6)) := by
  simpa only [program,result_zero,result_all] using initialStages_hoare keep ht v lo hi B hs t le_rfl

/-- Direct consumer for the existential interval postcondition of tracked
execution; no caller has to choose runtime interval bounds in the program. -/
theorem cleanup_exists_hoare (keep : Fin t → Bool) (ht : 0 < t) (v : Tapes t a) (B : ℕ) :
    HoareTime (program keep ht)
      (fun w => ∃ lo hi, TrackedHoare.Intervals v lo hi B (fun i => keep i = false) ∧
        w = TrackedHoare.bank v lo hi)
      (fun w => w = (retained keep v).append (SharedBank.empty t a)) (t*(5*B+6)) := by
  rintro w ⟨lo,hi,hs,rfl⟩
  exact cleanup_hoare keep ht v lo hi B hs _ rfl

theorem retained_common (keep : Fin t → Bool) (v : Tapes t a) (i : Fin t) (hi : keep i = true) :
    (retained keep v).head i = v.head i ∧ (retained keep v).tape i = v.tape i := by
  simp [retained,hi]

theorem retained_private (keep : Fin t → Bool) (v : Tapes t a) (i : Fin t) (hi : keep i = false) :
    (retained keep v).head i = 0 ∧ (retained keep v).tape i = fun _ => blank := by
  simp [retained,hi]

theorem states_eq (n : ℕ) : states n = 1+4*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [states,ih]; omega

end
end IntegerMultBounds.Machine.TrackedCleanupList
