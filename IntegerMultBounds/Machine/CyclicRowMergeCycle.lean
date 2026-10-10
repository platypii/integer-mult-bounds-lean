import IntegerMultBounds.Machine.CyclicRowMergeCopy
import IntegerMultBounds.Machine.CyclicRowCycle

/-! Physical inverse cyclic traversal: take one row from each fixed role tape
and append the rows in role order to the common output. -/
namespace IntegerMultBounds.Machine.CyclicRowMergeCycle
open CyclicRowCopy (bank)
open CyclicRowCycle (states states_succ castStates castStates_hoare rowPrefix prefix_succ prefix_all)
variable {a c : ℕ}

private def haltProgram (c a : ℕ) : Program ((1+c)+2) 1 a :=
  ⟨by omega,0,fun _ _ => none⟩

def initialStages (c a : ℕ) : (n : ℕ) → n ≤ c → Program ((1+c)+2) (states n) a
  | 0,_ => haltProgram c a
  | n+1,hn => castStates (states_succ n).symm
      (seq (initialStages c a n (by omega)) (CyclicRowMergeCopy.program ⟨n,by omega⟩))

def program (c a : ℕ) := initialStages c a c le_rfl

def result (dest : ℤ → Fin (a+4)) (sources : Fin c → ℤ → Fin (a+4))
    (p : ℤ) (origins : Fin c → ℤ) (words : Fin c → List (Fin (a+4)))
    (bs : List Bool) (n : ℕ) : Tapes ((1+c)+2) a :=
  bank (putWord dest p (rowPrefix words n))
    (fun j => putWord (sources j) (origins j) (words j))
    (p+(rowPrefix words n).length)
    (fun j => if j.val < n then origins j+(words j).length else origins j) bs

private theorem result_step (dest : ℤ → Fin (a+4)) (sources : Fin c → ℤ → Fin (a+4))
    (p : ℤ) (origins : Fin c → ℤ) (words : Fin c → List (Fin (a+4)))
    (bs : List Bool) (j : Fin c) (hb : Counter.value bs = (words j).length) :
    HoareTime (CyclicRowMergeCopy.program j)
      (fun v => v = result dest sources p origins words bs j.val)
      (fun v => v = result dest sources p origins words bs (j.val+1))
      (7*(words j).length+7*bs.length+16) := by
  have hh := CyclicRowMergeCopy.copy_hoare j (putWord dest p (rowPrefix words j.val))
    (fun k => putWord (sources k) (origins k) (words k))
    (p+(rowPrefix words j.val).length)
    (fun k => if k.val < j.val then origins k+(words k).length else origins k)
    (words j) bs hb
  simp only [lt_self_iff_false,ite_false] at hh
  have he : putWord (putWord (sources j) (origins j) (words j)) (origins j) (words j) =
      putWord (sources j) (origins j) (words j) :=
    WordSegments.of_agrees _ _ _ (fun i hi => WordSegments.get _ _ _ i hi)
  rw [he,Function.update_eq_self,putWord_append_forward,← prefix_succ] at hh
  apply hh.consequence (fun _ h => h) _ le_rfl
  intro v hv
  rw [hv]
  unfold result
  rw [prefix_succ,List.length_append,Nat.cast_add,← add_assoc]
  congr 1
  funext k
  by_cases hk : k = j
  · subst k; simp
  · have hv : k.val ≠ j.val := fun h => hk (Fin.ext h)
    simp only [Function.update_of_ne hk]
    have he : k.val < j.val ↔ k.val < j.val+1 := by omega
    simp only [he]

theorem initialStages_hoare (dest : ℤ → Fin (a+4))
    (sources : Fin c → ℤ → Fin (a+4)) (p : ℤ) (origins : Fin c → ℤ)
    (words : Fin c → List (Fin (a+4))) (bs : List Bool)
    (hb : ∀ j, Counter.value bs = (words j).length) (n : ℕ) (hn : n ≤ c) :
    HoareTime (initialStages c a n hn)
      (fun v => v = result dest sources p origins words bs 0)
      (fun v => v = result dest sources p origins words bs n)
      (7*(rowPrefix words n).length+n*(7*bs.length+17)) := by
  induction n with
  | zero =>
    rintro v rfl
    exact ⟨0,_,by simp [rowPrefix],rfl,rfl,rfl⟩
  | succ n ih =>
    have hh := (ih (by omega)).seq
      (result_step dest sources p origins words bs ⟨n,by omega⟩ (hb ⟨n,by omega⟩))
    have hh' := castStates_hoare (states_succ n).symm _ hh
    apply hh'.consequence (fun _ h => h) (fun _ h => h) _
    rw [prefix_succ words ⟨n,by omega⟩,List.length_append]
    exact le_of_eq (by ring)

/-- All role heads start at their next row and finish after that row. Every
source tape and restored binary control is unchanged; output gains all rows. -/
theorem cycle_hoare (dest : ℤ → Fin (a+4))
    (sources : Fin c → ℤ → Fin (a+4)) (p : ℤ) (origins : Fin c → ℤ)
    (words : Fin c → List (Fin (a+4))) (bs : List Bool)
    (hb : ∀ j, Counter.value bs = (words j).length) :
    HoareTime (program c a)
      (fun v => v = bank dest (fun j => putWord (sources j) (origins j) (words j)) p origins bs)
      (fun v => v = bank (putWord dest p (List.ofFn words).flatten)
        (fun j => putWord (sources j) (origins j) (words j))
        (p+(List.ofFn words).flatten.length) (fun j => origins j+(words j).length) bs)
      (7*(List.ofFn words).flatten.length+c*(7*bs.length+17)) := by
  have hh := initialStages_hoare dest sources p origins words bs hb c le_rfl
  simp only [result,prefix_all] at hh
  simpa only [program,rowPrefix,List.take_zero,List.flatten_nil,
    List.length_nil,Nat.cast_zero,add_zero,Nat.not_lt_zero,ite_false,Fin.isLt,ite_true,putWord] using hh

end IntegerMultBounds.Machine.CyclicRowMergeCycle
