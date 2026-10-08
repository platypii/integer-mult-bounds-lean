import IntegerMultBounds.Machine.Hoare

/-! Physical erasure guided by a synchronized visited-interval tape. An origin
marker survives the outward sweep and restores both heads to zero. Internal
blank data cells never serve as delimiters. -/
namespace IntegerMultBounds.Machine.TrackedCleanup
variable {q : ℕ}

/-- Origin and visited cells have distinct symbols in the existing alphabet. -/
def tracker (lo hi z : ℤ) : Fin (q+4) :=
  if z = 0 then separator else if lo ≤ z ∧ z ≤ hi then bitSymbol false else blank

def origin (z : ℤ) : Fin (q+4) := if z = 0 then separator else blank

def erased (f : ℤ → Fin (q+4)) (lo p z : ℤ) : Fin (q+4) :=
  if lo ≤ z ∧ z < p then blank else f z

def swept (lo hi p z : ℤ) : Fin (q+4) :=
  if z = 0 then separator else erased (tracker lo hi) lo p z

def cfg (s : Fin 4) (f g : ℤ → Fin (q+4)) (p : ℤ) : Config 2 4 q :=
  ⟨s,fun _ => p,![f,g]⟩

def bank (f g : ℤ → Fin (q+4)) (p : ℤ) : Tapes 2 q := (cfg 0 f g p).tapes

def program (q : ℕ) : Program 2 4 q where
  tapes_pos := by decide
  start := 0
  transition := fun s sy =>
    if s = 0 then
      if sy 1 = blank then some (1,fun i => (sy i,.right))
      else some (0,fun i => (sy i,.left))
    else if s = 1 then
      if sy 1 = blank then some (2,fun i => (sy i,.left))
      else some (1,fun i => (if i = 1 ∧ sy 1 = separator then separator else blank,.right))
    else if s = 2 then
      if sy 1 = separator then some (3,fun _ => (blank,.stay))
      else some (2,fun i => (sy i,.left))
    else none

private theorem track_nonblank (lo hi p : ℤ) (hl : lo ≤ p) (hh : p ≤ hi) :
    tracker (q := q) lo hi p ≠ blank := by
  by_cases hp : p = 0 <;> simp [tracker,hp,hl,hh,separator,blank,bitSymbol,Fin.ext_iff]

private theorem retain_step (s s' : Fin 4) (f g : ℤ → Fin (q+4)) (p : ℤ) (m : Move)
    (h : (program q).transition s (![f,g] · p) = some (s',fun i => (![f,g] i p,m))) :
    step (program q) (cfg s f g p) = some (cfg s' f g (p+m.offset)) := by
  simp only [step,cfg,h]
  congr 1
  congr 1
  funext i z
  by_cases hz : z = p <;> simp [hz]

private theorem seek_step (f : ℤ → Fin (q+4)) (lo hi p : ℤ) (hl : lo ≤ p) (hh : p ≤ hi) :
    step (program q) (cfg 0 f (tracker lo hi) p) = some (cfg 0 f (tracker lo hi) (p-1)) := by
  apply retain_step (m := .left)
  simp [program,track_nonblank lo hi p hl hh]

private theorem seek_run (f : ℤ → Fin (q+4)) (lo hi : ℤ) (n : ℕ) (hh : lo+n ≤ hi) :
    run (program q) (n+1) (cfg 0 f (tracker lo hi) (lo+n)) =
      some (cfg 0 f (tracker lo hi) (lo-1)) := by
  induction n with
  | zero => simpa only [Nat.cast_zero,add_zero,Nat.zero_add,run_one] using seek_step f lo hi lo le_rfl (by simpa using hh)
  | succ n ih =>
    rw [run,seek_step f lo hi (lo+(n+1 : ℕ)) (by omega) hh]
    simp only [Option.bind_some]
    convert ih (by omega) using 1; congr 2; omega

private theorem enter_step (f : ℤ → Fin (q+4)) (lo hi : ℤ) (hl : lo ≤ 0) :
    step (program q) (cfg 0 f (tracker lo hi) (lo-1)) = some (cfg 1 f (tracker lo hi) lo) := by
  have hp : lo-1 ≠ 0 := by omega
  have hs := retain_step (q := q) 0 1 f (tracker lo hi) (lo-1) .right
    (by simp [program,tracker,hp])
  simpa only [Move.offset,sub_add_cancel] using hs

private theorem erased_start (f : ℤ → Fin (q+4)) (lo : ℤ) : erased f lo lo = f := by
  funext z
  simp [erased]

private theorem swept_start (lo hi : ℤ) : swept (q := q) lo hi lo = tracker lo hi := by
  funext z
  by_cases hz : z = 0 <;> simp [swept,erased,tracker,hz]

private theorem sweep_step (f : ℤ → Fin (q+4)) (lo hi p : ℤ) (hl : lo ≤ p) (hh : p ≤ hi) :
    step (program q) (cfg 1 (erased f lo p) (swept lo hi p) p) =
      some (cfg 1 (erased f lo (p+1)) (swept lo hi (p+1)) (p+1)) := by
  have hr : swept (q := q) lo hi p p = tracker lo hi p := by
    by_cases hp : p = 0 <;> simp [swept,erased,tracker,hp]
  have hnb := track_nonblank (q := q) lo hi p hl hh
  simp only [step,cfg,program,show (1 : Fin 4) ≠ 0 by decide,ite_false,ite_true,
    Matrix.cons_val_one,Matrix.cons_val_zero,hr,hnb,Move.offset]
  congr 1
  congr 1
  funext i z
  fin_cases i
  · by_cases hz : z = p
    · subst z; simp [erased,hl]
    · have he : (lo ≤ z ∧ z ≤ p) ↔ (lo ≤ z ∧ z < p) := by omega
      simp [erased,hz,he]
  · by_cases hz : z = p
    · subst z
      by_cases hp : p = 0 <;> simp [swept,erased,tracker,hp,hl,hh,bitSymbol,separator,Fin.ext_iff]
    · by_cases hz0 : z = 0
      · subst z; simp [swept,hz]
      · have he : (lo ≤ z ∧ z ≤ p) ↔ (lo ≤ z ∧ z < p) := by omega
        simp [swept,erased,hz,hz0,he]

private theorem sweep_run (f : ℤ → Fin (q+4)) (lo hi : ℤ) (n : ℕ) (hh : lo+n ≤ hi+1) :
    run (program q) n (cfg 1 f (tracker lo hi) lo) =
      some (cfg 1 (erased f lo (lo+n)) (swept lo hi (lo+n)) (lo+n)) := by
  induction n with
  | zero => simp [run,erased_start,swept_start]
  | succ n ih =>
    rw [run_add,ih (by omega)]
    simp only [Option.bind_some,run_one]
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using
      sweep_step f lo hi (lo+n) (by omega) (by omega)

private theorem erased_all (f : ℤ → Fin (q+4)) (lo hi : ℤ)
    (hf : ∀ z, z < lo ∨ hi < z → f z = blank) : erased f lo (hi+1) = fun _ => blank := by
  funext z
  by_cases hz : lo ≤ z ∧ z < hi+1
  · simp [erased,hz]
  · simp only [erased,hz,ite_false]
    exact hf z (by omega)

private theorem swept_all (lo hi : ℤ) : swept (q := q) lo hi (hi+1) = origin := by
  funext z
  by_cases hz : z = 0
  · simp [swept,origin,hz]
  · by_cases hr : lo ≤ z ∧ z ≤ hi <;> simp [swept,origin,erased,tracker,hz,hr]

private theorem turn_step (hi : ℤ) (hh : 0 ≤ hi) :
    step (program q) (cfg 1 (fun _ => blank) origin (hi+1)) =
      some (cfg 2 (fun _ => blank) origin hi) := by
  have hn : hi+1 ≠ 0 := by omega
  have hs := retain_step (q := q) 1 2 (fun _ => blank) origin (hi+1) .left
    (by simp [program,origin,hn])
  simpa only [Move.offset,add_neg_cancel_right] using hs

private theorem return_run (n : ℕ) :
    run (program q) n (cfg 2 (fun _ => blank) origin n) =
      some (cfg 2 (fun _ => blank) origin 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hs : step (program q) (cfg 2 (fun _ => blank) origin (n+1)) =
        some (cfg 2 (fun _ => blank) origin n) := by
      have ht := retain_step (q := q) 2 2 (fun _ => blank) origin (n+1) .left
        (by simp [program,origin,show (n : ℤ)+1 ≠ 0 by omega,show (blank : Fin (q+4)) ≠ separator by simp [blank,separator,Fin.ext_iff]])
      simpa only [Move.offset,add_neg_cancel_right] using ht
    rw [run]
    simpa only [Nat.cast_add,Nat.cast_one,hs,Option.bind_some] using ih

private theorem finish_step :
    step (program q) (cfg 2 (fun _ => blank) origin 0) =
      some (cfg 3 (fun _ => blank) (fun _ => blank) 0) := by
  simp only [step,cfg,program,show (2 : Fin 4) ≠ 0 by decide,show (2 : Fin 4) ≠ 1 by decide,
    ite_false,ite_true,Matrix.cons_val_one,Matrix.cons_val_zero,origin,Move.offset]
  congr 1
  congr 1
  funext i z
  fin_cases i <;> by_cases hz : z = 0 <;> simp [hz,origin]

/-- Complete physical cleanup, including the origin marker and both heads. -/
theorem cleanup_hoare (f : ℤ → Fin (q+4)) (lo hi p : ℤ)
    (hl : lo ≤ 0) (hh : 0 ≤ hi) (hp : lo ≤ p ∧ p ≤ hi)
    (hf : ∀ z, z < lo ∨ hi < z → f z = blank) :
    HoareTime (program q) (fun v => v = bank f (tracker lo hi) p)
      (fun v => v = bank (fun _ => blank) (fun _ => blank) 0)
      ((p-lo).toNat+(hi-lo+1).toNat+hi.toNat+4) := by
  have hn : ((p-lo).toNat : ℤ) = p-lo := Int.toNat_of_nonneg (by omega)
  have hm : ((hi-lo+1).toNat : ℤ) = hi-lo+1 := Int.toNat_of_nonneg (by omega)
  have hh' : (hi.toNat : ℤ) = hi := Int.toNat_of_nonneg hh
  have hseek := seek_run f lo hi (p-lo).toNat (by omega)
  have hp' : lo+((p-lo).toNat : ℤ) = p := by omega
  rw [hp'] at hseek
  have hsweep := sweep_run f lo hi (hi-lo+1).toNat (by omega)
  have he : lo+((hi-lo+1).toNat : ℤ) = hi+1 := by omega
  rw [he,erased_all f lo hi hf,swept_all] at hsweep
  have hreturn := return_run (q := q) hi.toNat
  rw [hh'] at hreturn
  intro v hv
  subst v
  refine ⟨_,cfg 3 (fun _ => blank) (fun _ => blank) 0,le_rfl,?_,?_,rfl⟩
  · change run (program q) _ (cfg 0 f (tracker lo hi) p) = _
    rw [show (p-lo).toNat+(hi-lo+1).toNat+hi.toNat+4 =
      ((p-lo).toNat+1)+(1+((hi-lo+1).toNat+(1+(hi.toNat+1)))) by omega,
      run_add,hseek]
    simp only [Option.bind_some]
    rw [run_add]
    simp only [run_one,enter_step f lo hi hl,Option.bind_some]
    rw [run_add,hsweep]
    simp only [Option.bind_some]
    rw [run_add]
    simp only [run_one,turn_step hi hh,Option.bind_some]
    rw [run_add,hreturn]
    simp only [Option.bind_some,run_one,finish_step]
  · simp [step,program,cfg]

/-- Runtime is linear in the proved visited radius, independently of symbols. -/
theorem cleanup_hoare_linear (f : ℤ → Fin (q+4)) (lo hi p : ℤ) (B : ℕ)
    (hl : lo ≤ 0) (hh : 0 ≤ hi) (hp : lo ≤ p ∧ p ≤ hi)
    (hlo : -(B : ℤ) ≤ lo) (hhi : hi ≤ B)
    (hf : ∀ z, z < lo ∨ hi < z → f z = blank) :
    HoareTime (program q) (fun v => v = bank f (tracker lo hi) p)
      (fun v => v = bank (fun _ => blank) (fun _ => blank) 0) (5*B+5) := by
  apply (cleanup_hoare f lo hi p hl hh hp hf).consequence (fun _ h => h) (fun _ h => h) ?_
  have hn : ((p-lo).toNat : ℤ) = p-lo := Int.toNat_of_nonneg (by omega)
  have hm : ((hi-lo+1).toNat : ℤ) = hi-lo+1 := Int.toNat_of_nonneg (by omega)
  have hr : (hi.toNat : ℤ) = hi := Int.toNat_of_nonneg hh
  omega

end IntegerMultBounds.Machine.TrackedCleanup
