import IntegerMultBounds.Machine.CyclicRowCopy

/-! One complete physical cyclic role distribution: each successive raw row
is copied to its fixed role tape. A single row descriptor and reusable clock
are shared across every role. Source and output heads advance physically. -/
namespace IntegerMultBounds.Machine.CyclicRowCycle
open CyclicRowCopy (bank)
variable {a c : ℕ}

def rowPrefix (words : Fin c → List (Fin (a+4))) (n : ℕ) : List (Fin (a+4)) :=
  ((List.ofFn words).take n).flatten

theorem prefix_succ (words : Fin c → List (Fin (a+4))) (j : Fin c) :
    rowPrefix words (j.val+1) = rowPrefix words j.val ++ words j := by
  unfold rowPrefix
  rw [List.take_succ_eq_append_getElem (by simp),List.flatten_append]
  simp

theorem prefix_all (words : Fin c → List (Fin (a+4))) :
    rowPrefix words c = (List.ofFn words).flatten := by
  unfold rowPrefix
  rw [List.take_of_length_le (by simp)]

theorem source_row (source : ℤ → Fin (a+4)) (p : ℤ)
    (words : Fin c → List (Fin (a+4))) (j : Fin c) :
    putWord (putWord source p (List.ofFn words).flatten)
      (p+(rowPrefix words j.val).length) (words j) =
      putWord source p (List.ofFn words).flatten := by
  have he : rowPrefix words j.val ++ words j ++ ((List.ofFn words).drop (j.val+1)).flatten =
      (List.ofFn words).flatten := by
    rw [← prefix_succ]
    change ((List.ofFn words).take (j.val+1)).flatten ++ _ = _
    rw [← List.flatten_append,List.take_append_drop]
  have hh := WordSegments.middle source p (rowPrefix words j.val) (words j)
    (((List.ofFn words).drop (j.val+1)).flatten)
  rw [he] at hh
  exact hh

/-- Closed arithmetic keeps the fixed role count out of kernel recursion. -/
def states (n : ℕ) : ℕ := 1+18*n

theorem states_zero : states 0 = 1 := rfl

theorem states_succ (n : ℕ) : states (n+1) = states n+18 := by
  unfold states
  omega

/-- State-index transport changes neither transitions nor tape behaviour. -/
def castStates {t q r a : ℕ} (h : q=r) (M : Program t q a) : Program t r a := h ▸ M

theorem castStates_hoare {t q r a : ℕ} (h : q=r) (M : Program t q a)
    {pre post : TapePred t a} {b : ℕ} (hh : HoareTime M pre post b) :
    HoareTime (castStates h M) pre post b := by
  cases h
  exact hh

private def haltProgram (c a : ℕ) : Program ((1+c)+2) 1 a :=
  ⟨by omega,0,fun _ _ => none⟩

def initialStages (c a : ℕ) : (n : ℕ) → n ≤ c → Program ((1+c)+2) (states n) a
  | 0,_ => haltProgram c a
  | n+1,hn => castStates (states_succ n).symm
      (seq (initialStages c a n (by omega)) (CyclicRowCopy.program ⟨n,by omega⟩))

def program (c a : ℕ) := initialStages c a c le_rfl

def result (source : ℤ → Fin (a+4)) (outputs : Fin c → ℤ → Fin (a+4))
    (p : ℤ) (origins : Fin c → ℤ) (words : Fin c → List (Fin (a+4)))
    (bs : List Bool) (n : ℕ) : Tapes ((1+c)+2) a :=
  bank (putWord source p (List.ofFn words).flatten)
    (fun j => if j.val < n then putWord (outputs j) (origins j) (words j) else outputs j)
    (p+(rowPrefix words n).length)
    (fun j => if j.val < n then origins j+(words j).length else origins j) bs

private theorem result_step (source : ℤ → Fin (a+4)) (outputs : Fin c → ℤ → Fin (a+4))
    (p : ℤ) (origins : Fin c → ℤ) (words : Fin c → List (Fin (a+4)))
    (bs : List Bool) (j : Fin c) (hb : Counter.value bs = (words j).length) :
    HoareTime (CyclicRowCopy.program j)
      (fun v => v = result source outputs p origins words bs j.val)
      (fun v => v = result source outputs p origins words bs (j.val+1))
      (7*(words j).length+7*bs.length+16) := by
  have hh := CyclicRowCopy.copy_hoare j (putWord source p (List.ofFn words).flatten)
    (fun k => if k.val < j.val then putWord (outputs k) (origins k) (words k) else outputs k)
    (p+(rowPrefix words j.val).length)
    (fun k => if k.val < j.val then origins k+(words k).length else origins k)
    (words j) bs hb
  rw [source_row] at hh
  simp only [lt_self_iff_false,ite_false] at hh
  apply hh.consequence (fun _ h => h) _ le_rfl
  intro v hv
  rw [hv]
  unfold result
  rw [prefix_succ,List.length_append,Nat.cast_add,← add_assoc]
  congr 1
  · funext k
    by_cases hk : k = j
    · subst k; simp
    · have hv : k.val ≠ j.val := fun h => hk (Fin.ext h)
      simp only [Function.update_of_ne hk]
      have he : k.val < j.val ↔ k.val < j.val+1 := by omega
      simp only [he]
  · funext k
    by_cases hk : k = j
    · subst k; simp
    · have hv : k.val ≠ j.val := fun h => hk (Fin.ext h)
      simp only [Function.update_of_ne hk]
      have he : k.val < j.val ↔ k.val < j.val+1 := by omega
      simp only [he]

theorem initialStages_hoare (source : ℤ → Fin (a+4))
    (outputs : Fin c → ℤ → Fin (a+4)) (p : ℤ) (origins : Fin c → ℤ)
    (words : Fin c → List (Fin (a+4))) (bs : List Bool)
    (hb : ∀ j, Counter.value bs = (words j).length) (n : ℕ) (hn : n ≤ c) :
    HoareTime (initialStages c a n hn)
      (fun v => v = result source outputs p origins words bs 0)
      (fun v => v = result source outputs p origins words bs n)
      (7*(rowPrefix words n).length+n*(7*bs.length+17)) := by
  induction n with
  | zero =>
    rintro v rfl
    exact ⟨0,_,by simp [rowPrefix],rfl,rfl,rfl⟩
  | succ n ih =>
    have hh := (ih (by omega)).seq
      (result_step source outputs p origins words bs ⟨n,by omega⟩ (hb ⟨n,by omega⟩))
    have hh' := castStates_hoare (states_succ n).symm _ hh
    apply hh'.consequence (fun _ h => h) (fun _ h => h) _
    rw [prefix_succ words ⟨n,by omega⟩,List.length_append]
    exact le_of_eq (by ring)

/-- One row per role, counted even if every payload cell is blank. Only fixed
many control states/tapes are used, and the row descriptor is restored. -/
theorem cycle_hoare (source : ℤ → Fin (a+4))
    (outputs : Fin c → ℤ → Fin (a+4)) (p : ℤ) (origins : Fin c → ℤ)
    (words : Fin c → List (Fin (a+4))) (bs : List Bool)
    (hb : ∀ j, Counter.value bs = (words j).length) :
    HoareTime (program c a)
      (fun v => v = bank (putWord source p (List.ofFn words).flatten) outputs p origins bs)
      (fun v => v = bank (putWord source p (List.ofFn words).flatten)
        (fun j => putWord (outputs j) (origins j) (words j))
        (p+(List.ofFn words).flatten.length) (fun j => origins j+(words j).length) bs)
      (7*(List.ofFn words).flatten.length+c*(7*bs.length+17)) := by
  have hh := initialStages_hoare source outputs p origins words bs hb c le_rfl
  simp only [result,prefix_all] at hh
  simpa only [program,rowPrefix,List.take_zero,List.flatten_nil,
    List.length_nil,Nat.cast_zero,add_zero,Nat.not_lt_zero,ite_false,Fin.isLt,ite_true] using hh

theorem states_eq (c : ℕ) : states c = 1+18*c := rfl

end IntegerMultBounds.Machine.CyclicRowCycle
