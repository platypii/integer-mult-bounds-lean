module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackClass
public import IntegerMultBounds.MathlibTM2.Cover.FallbackMatrixRead

/-! Scalar entries and row-major serialization of the weighted residual. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
noncomputable section
open Matrix M8.ReversedExchange LabelTraversal
variable {m n : ℕ} {R : Type*} [CommRing R]

/-- Each residual entry reads a single coefficient of the conjugated projector. -/
def residualEntry (B : Matrix (Fin m) (Fin m) R) (α α' : Fin m → R) :
    Fin m ⊕ Fin m → Fin m ⊕ Fin m → R
  | .inl i, .inl j => α i * ((1 : Matrix (Fin m) (Fin m) R) i j - B i j) * α' j
  | .inl i, .inr j => α i * B i j.rev
  | .inr i, .inl j => B i.rev j * α' j
  | .inr i, .inr j => (1 : Matrix (Fin m) (Fin m) R) i.rev j.rev - B i.rev j.rev

theorem projectorResidual_entry (e : (Fin m ⊕ Fin m) ≃ Fin n)
    (P g : Matrix (Fin m) (Fin m) R) (α α' : Fin m → R) (i j : Fin n) :
    projectorResidual e P α α' g i j = residualEntry (g*P*g⁻¹) α α' (e.symm i) (e.symm j) := by
  have left (X : Matrix (Fin m) (Fin m) R) (i j : Fin m) : (rev (R := R) m * X) i j = X i.rev j := by
    simp [mul_apply,rev,ite_mul]
  have right (X : Matrix (Fin m) (Fin m) R) (i j : Fin m) : (X * rev (R := R) m) i j = X i j.rev := by
    simp [mul_apply,rev,mul_ite,show ∀ k : Fin m, j = k.rev ↔ k = j.rev by intro k; constructor <;> intro h <;> simp [h]]
  obtain ⟨i,rfl⟩ := e.surjective i
  obtain ⟨j,rfl⟩ := e.surjective j
  cases i <;> cases j <;>
    simp [projectorResidual,residual,fromBlocks_multiply,residualEntry,mul_diagonal,diagonal_mul,left,right]

variable {T Q A d M : ℕ} [NeZero M] {P U : Type}
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Node

/-- Assemble a matrix directly on the output stack. Reverse execution order
of the entry writers puts row zero and its first column at the tape head. -/
theorem matrixWords_writes {e : ℕ} (body : P → Pr P T Q A U) (out : Fin T) (ok : Regs T A → Prop)
    (stable : ∀ R xs, ok R → ok (Function.update R out xs))
    (entry : Fin d → Fin e → Pr P T Q A U) (matrix : Matrix (Fin d) (Fin e) (ZMod M)) (H c : ℕ)
    (run : ∀ i j, Writes body ok out (entry i j) (binSyms H (matrix i j).val) c) :
    Writes body ok out (sequence (fun i => sequence (entry i) (List.finRange e)) (List.finRange d))
      (matrixWords A H matrix) (d*(e*c+1)+1) := by
  have row (i : Fin d) := sequence_writes stable (run i) (List.finRange e)
  simpa [matrixWords,List.flatMap_def,List.finRange,List.map_ofFn,Function.comp_def] using sequence_writes stable row (List.finRange d)

theorem projectorWords_writes (body : P → Pr P T Q A U) (out : Fin T) (ok : Regs T A → Prop)
    (stable : ∀ R xs, ok R → ok (Function.update R out xs))
    (e : (Fin m ⊕ Fin m) ≃ Fin n) (proj g : Matrix (Fin m) (Fin m) (ZMod M)) (α α' : Fin m → ZMod M)
    (entry : (Fin m ⊕ Fin m) → (Fin m ⊕ Fin m) → Pr P T Q A U) (H c : ℕ)
    (emit : ∀ i j, Writes body ok out (entry i j)
      (binSyms H (residualEntry (g*proj*g⁻¹) α α' i j).val) c) :
    Writes body ok out (sequence (fun i => sequence (fun j => entry (e.symm i) (e.symm j))
      (List.finRange n)) (List.finRange n)) (matrixWords A H (projectorResidual e proj α α' g)) (n*(n*c+1)+1) := by
  apply matrixWords_writes body out ok stable
  intro i j
  rw [projectorResidual_entry]
  exact emit _ _

end
end IntegerMultBounds.MathlibTM2.Cover.Fallback
