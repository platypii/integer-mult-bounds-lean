import IntegerMultBounds.Networks.GlobalCircuit

/-! Dirty-scratch cancellation around an actual invertible scalar program. The
wrapper executes literal embedded instruction lists; its semantic theorem makes
no tape-time, grouped-gate, or sparse-incidence claim. -/

namespace IntegerMultBounds.Networks.DirtyLinearCircuit

open Circuit

section Linearity
variable {ι R : Type*} [DecidableEq ι] [CommRing R]

/-- Every elementary scalar instruction is additive on complete register states. -/
theorem gate_run_add (gate : Gate ι R) (left right : ι → R) :
    gate.run (left + right) = gate.run left + gate.run right := by
  funext i
  have hs :
      (gate.terms.map (fun p => p.2 * (left p.1 + right p.1))).sum =
        (gate.terms.map (fun p => p.2 * left p.1)).sum +
          (gate.terms.map (fun p => p.2 * right p.1)).sum := by
    simp only [mul_add, List.sum_map_add]
  by_cases hi : i = gate.target
  · subst i
    simp only [Gate.run, Pi.add_apply, Function.update_self, hs]
    ring
  · simp [Gate.run, Pi.add_apply, Function.update_of_ne hi]

/-- Additivity follows from the actual instruction list, rather than an
external assumption about the supplied scratch computation. -/
theorem run_add (program : Program ι R) (left right : ι → R) :
    run program (left + right) = run program left + run program right := by
  induction program generalizing left right with
  | nil => rfl
  | cons gate program ih =>
    rw [run_cons, gate_run_add, ih]
    rfl

end Linearity

/-- Two data banks and one scratch bank, all physically disjoint. -/
abbrev Register (n s : ℕ) := Fin n ⊕ Fin n ⊕ Fin s

def x {n s : ℕ} (i : Fin n) : Register n s := Sum.inl i
def y {n s : ℕ} (i : Fin n) : Register n s := Sum.inr (Sum.inl i)
def scratch {n s : ℕ} (i : Fin s) : Register n s := Sum.inr (Sum.inr i)

def contents {n s : ℕ} (X Y : Fin n → ZMod 2) (S : Fin s → ZMod 2) : Register n s → ZMod 2 :=
  Sum.elim X (Sum.elim Y S)

def scratchEmbedding (n s : ℕ) : Fin s ↪ Register n s :=
  ⟨scratch, fun _ _ h => Sum.inr.inj (Sum.inr.inj h)⟩

/-- Embed a real instruction list, retaining both data banks unchanged. -/
theorem scratch_run {n s : ℕ} (program : Program (Fin s) (ZMod 2))
    (X Y : Fin n → ZMod 2) (S : Fin s → ZMod 2) :
    run (GlobalCircuit.embed (scratchEmbedding n s) program) (contents X Y S) =
      contents X Y (run program S) := by
  have he := GlobalCircuit.embed_run (scratchEmbedding n s) program (contents X Y S)
  funext r
  rcases r with i | i | i
  · exact GlobalCircuit.embed_outside _ _ _ (x i) (by intro j; change Sum.inr (Sum.inr j) ≠ Sum.inl i; simp)
  · exact GlobalCircuit.embed_outside _ _ _ (y i) (by intro j; change Sum.inr (Sum.inr j) ≠ Sum.inr (Sum.inl i); simp)
  · exact congrFun he i

theorem inject_run {n s : ℕ} (G : Fin s → Fin n → ZMod 2)
    (X Y : Fin n → ZMod 2) (S : Fin s → ZMod 2) :
    run (block scratch x G) (contents X Y S) = contents X Y (S + mv G X) := by
  funext r
  rw [block_run _ _ _ (by intros; simp [scratch, x])]
  rcases r with i | i | i <;> simp [scratch, x, contents, mv]

theorem read_run {n s : ℕ} (H : Fin n → Fin s → ZMod 2)
    (X Y : Fin n → ZMod 2) (S : Fin s → ZMod 2) :
    run (block y scratch H) (contents X Y S) = contents X (Y + mv H S) S := by
  funext r
  rw [block_run _ _ _ (by intros; simp [y, scratch])]
  rcases r with i | i | i <;> simp [y, scratch, contents, mv]

/-- The literal dirty wrapper: compute, read, uncompute, inject, then repeat. -/
def program {n s : ℕ} (C J : Program (Fin s) (ZMod 2))
    (G : Fin s → Fin n → ZMod 2) (H : Fin n → Fin s → ZMod 2) :
    Program (Register n s) (ZMod 2) :=
  GlobalCircuit.embed (scratchEmbedding n s) C ++
  (block y scratch H ++
  (GlobalCircuit.embed (scratchEmbedding n s) J ++
  (block scratch x G ++
  (GlobalCircuit.embed (scratchEmbedding n s) C ++
  (block y scratch H ++
  (GlobalCircuit.embed (scratchEmbedding n s) J ++ block scratch x G))))))

private theorem self_add_zero {ι : Type*} (f : ι → ZMod 2) : f + f = 0 := by
  funext i
  simpa only [Pi.add_apply, Pi.zero_apply, ZMod.neg_eq_self_mod_two] using add_neg_cancel (f i)

/-- Arbitrary scratch is restored. The target receives the actual scratch
program applied to the injected input, followed by the linear readout. Only
actual left-inverse execution is required; forward additivity is proved above. -/
theorem program_run {n s : ℕ} (C J : Program (Fin s) (ZMod 2))
    (G : Fin s → Fin n → ZMod 2) (H : Fin n → Fin s → ZMod 2)
    (hinverse : ∀ S, run J (run C S) = S)
    (X Y : Fin n → ZMod 2) (S : Fin s → ZMod 2) :
    run (program C J G H) (contents X Y S) =
      contents X (Y + mv H (run C (mv G X))) S := by
  simp only [program, run_append, scratch_run, read_run, inject_run, hinverse, run_add, mv_add]
  have hs : S + mv G X + mv G X = S := by
    rw [add_assoc, self_add_zero, add_zero]
  have hy : Y + mv H (run C S) + (mv H (run C S) + mv H (run C (mv G X))) =
      Y + mv H (run C (mv G X)) := by
    rw [← add_assoc, add_assoc Y, self_add_zero, add_zero]
  rw [hs, hy]

end IntegerMultBounds.Networks.DirtyLinearCircuit
