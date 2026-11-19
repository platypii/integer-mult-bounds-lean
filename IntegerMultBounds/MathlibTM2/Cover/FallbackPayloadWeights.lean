module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackUpdateRow
public import IntegerMultBounds.MathlibTM2.Cover.FallbackBank

/-! Extract the non-anchor weights of a packed diagonal in payload-operation order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Matrix
variable {R : Type*} [CommRing R] {n : ℕ}

/-- The first coordinate uses the sign of the diagonal. Every other pair uses exactly
the diagonal entry on its non-anchor coordinate. -/
theorem diagonalBank (a : Fin (n+1) → Rˣ) (s : Rˣ) (sign : ∏ i, a i = s)
    (ops : List (RowOp (n+1) R)) (G : Matrix (Fin (n+1)) (Fin (n+1)) R)
    (undo : ∀ x, ops.foldl (fun y op => op.apply y) ((diagonal fun i => (a i : R)).mulVec x) = G.mulVec x)
    (b : ℕ) (x : Fin b → Fin (n+1) → R) :
    fallbackBank b s (fun i => a i.succ) ops (bankFields (List.finRange (n+1)) x) =
      bankFields (List.finRange (n+1)) (fun k => G.mulVec (x k)) := by
  rw [fallbackBank_fields]
  congr 1
  funext k
  rw [← undo (x k)]
  congr 1
  ext j
  have coord := congrFun (unit_pairs a) j
  rw [sign] at coord
  simp only [applyPairs_eq,mulVec_diagonal,← List.ofFn_eq_map,List.prod_ofFn]
  rw [coord]
  simp [Pi.mul_apply,Finset.prod_apply,Units.coe_prod,mul_left_comm,mul_assoc]

variable {T Q A M : ℕ} [NeZero M] {P U : Type}

theorem payloadWeights_exec (body : P → Pr P T Q A U) (r : Fin 7 ↪ Fin T) (H : ℕ)
    (a : Fin (n+1) → ZMod M) (unit : ∀ i, IsUnit (a i)) (negative : Bool)
    (sign : ∏ i, a i = if negative then -1 else 1)
    (ops : List (RowOp (n+1) (ZMod M))) (G : Matrix (Fin (n+1)) (Fin (n+1)) (ZMod M))
    (undo : ∀ x, ops.foldl (fun y op => op.apply y) ((diagonal a).mulVec x) = G.mulVec x)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (matrix : S.R (r 2) = matrixWords A H (diagonal a) ++ tail) (width : (S.R (r 1)).length = H)
    (free : ∀ i : Fin 7, i = 0 ∨ 4 ≤ i → S.R (r i) = []) :
    ∃ z t, ∃ weights : Fin n → (ZMod M)ˣ, z.user = v.user ∧ t ≤ n*(8*((n+1)*(n+1)*H)+14*H+22)+1 ∧
      Exec body (gatherMatrix (n := n) Fin.succ Fin.succ r) (mk v S) t
        (mk z {S with R := Function.update S.R (r 3) ((List.ofFn fun i => binSyms H (weights i : ZMod M).val).flatten ++ S.R (r 3))}) ∧
      (∀ i, (weights i : ZMod M) = a i.succ) ∧
      ∀ b (x : Fin b → Fin (n+1) → ZMod M),
        fallbackBank b (if negative then -1 else 1) weights ops (bankFields (List.finRange (n+1)) x) =
          bankFields (List.finRange (n+1)) (fun k => G.mulVec (x k)) := by
  let u := fun i => (unit i).unit
  have val (i) : (u i : ZMod M) = a i := (unit i).unit_spec
  obtain ⟨z,t,hz,ht,run⟩ := gatherMatrix_exec body r (diagonal a) Fin.succ Fin.succ H v S tail matrix width free
  refine ⟨z,t,fun i => u i.succ,hz,ht,by simpa [val] using run,fun i => val i.succ,?_⟩
  apply diagonalBank
  · apply Units.ext
    cases negative <;> simpa [Units.coe_prod,val] using sign
  · simpa [val] using undo

end IntegerMultBounds.MathlibTM2.Cover.Fallback
