import IntegerMultBounds.Machine.CyclicRowNormalized

/-! Undo the fixed network role permutation during physical merging. Only the
finite wiring changes; no tape is freely permuted. The normalized merge retains
its exact runtime, source frames and restored heads. -/
namespace IntegerMultBounds.Machine.CyclicRowPermutedMerge
variable {a c n : ℕ}
open CyclicRowSplit (bank roleWord sourceWord)

def sumPerm {m n : ℕ} (e : Equiv.Perm (Fin m)) (f : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (m+n)) where
  toFun := Fin.addCases (fun i => Fin.castAdd n (e i)) (fun i => Fin.natAdd m (f i))
  invFun := Fin.addCases (fun i => Fin.castAdd n (e.symm i)) (fun i => Fin.natAdd m (f.symm i))
  left_inv := by intro i; induction i using Fin.addCases <;> simp
  right_inv := by intro i; induction i using Fin.addCases <;> simp

theorem reindex_append {m n : ℕ} (e : Equiv.Perm (Fin m)) (f : Equiv.Perm (Fin n))
    (v : Tapes m a) (w : Tapes n a) :
    (v.append w).reindex (sumPerm e f) = (v.reindex e).append (w.reindex f) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases <;>
    simp [Tapes.reindex,Tapes.append,sumPerm]

def slots (rho : Equiv.Perm (Fin c)) : Equiv.Perm (Fin (((1+c)+2)+2)) :=
  sumPerm (sumPerm (sumPerm (Equiv.refl _) rho) (Equiv.refl _)) (Equiv.refl _)

/-- The compiled wiring reads logical role j from its actual network output
slot rho j, with common output and both binary controllers fixed. -/
theorem slots_role (rho : Equiv.Perm (Fin c)) (j : Fin c) :
    slots rho (Fin.castAdd 2 (Fin.castAdd 2 (Fin.natAdd 1 j))) =
      Fin.castAdd 2 (Fin.castAdd 2 (Fin.natAdd 1 (rho j))) := by
  simp [slots,sumPerm]

theorem reindex_bank (rho : Equiv.Perm (Fin c)) (source : ℤ → Fin (a+4))
    (outputs : Fin c → ℤ → Fin (a+4)) (p : ℤ) (origins : Fin c → ℤ)
    (bs gs : List Bool) :
    (bank (CyclicRowCopy.bank source outputs p origins bs) gs).reindex (slots rho) =
      bank (CyclicRowCopy.bank source (fun j => outputs (rho.symm j)) p
        (fun j => origins (rho.symm j)) bs) gs := by
  unfold bank CyclicRowCopy.bank CountedLoopReuseAlphabet.bank CyclicRowCopy.payload slots
  rw [reindex_append,reindex_append,reindex_append]
  rfl

def program (rho : Equiv.Perm (Fin c)) (a : ℕ) :=
  reindex (CyclicRowNormalized.mergeProgram c a) (slots rho)

/-- Logical role j is physically on tape rho j. Merge restores the logical
cyclic row order, preserving every physical input role and its original head. -/
theorem merge_hoare (rho : Equiv.Perm (Fin c)) (dest : ℤ → Fin (a+4))
    (sources : Fin c → ℤ → Fin (a+4)) (p : ℤ) (origins : Fin c → ℤ)
    (rows : Fin n → Fin c → List (Fin (a+4))) (B : ℕ)
    (hw : ∀ i j, (rows i j).length = B) (bs gs : List Bool)
    (hb : Counter.value bs = B) (hg : Counter.value gs = n) :
    HoareTime (program rho a)
      (fun v => v = bank (CyclicRowCopy.bank dest
        (fun j => putWord (sources (rho.symm j)) (origins (rho.symm j))
          (roleWord rows (rho.symm j))) p (fun j => origins (rho.symm j)) bs) gs)
      (fun v => v = bank (CyclicRowCopy.bank (putWord dest p (sourceWord rows))
        (fun j => putWord (sources (rho.symm j)) (origins (rho.symm j))
          (roleWord rows (rho.symm j))) p (fun j => origins (rho.symm j)) bs) gs)
      (CyclicRowNormalized.cost c n B bs gs) := by
  have hh := (CyclicRowNormalized.merge_hoare dest sources p origins rows B hw bs gs hb hg).reindex (slots rho)
  apply hh.consequence ?_ ?_ le_rfl
  · intro v hv
    subst v
    refine ⟨_,rfl,?_⟩
    exact (reindex_bank rho dest (fun j => putWord (sources j) (origins j) (roleWord rows j)) p origins bs gs).symm
  · rintro v ⟨original,rfl,rfl⟩
    exact reindex_bank rho _ _ _ _ bs gs

end IntegerMultBounds.Machine.CyclicRowPermutedMerge
