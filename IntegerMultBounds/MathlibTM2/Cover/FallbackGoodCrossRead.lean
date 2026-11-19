module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodFactors
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodHeadShear

/-! Emit a nontrivial cross coefficient from its single archived stage. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal GoodForm Matrix
open M8.Exchange M8.ReversedExchange IntegerMultBounds.Swap.Shear
variable {P U : Type} {T Q A d M : ℕ} [NeZero M]

theorem archivedCross_writes (body : P → Pr P T Q A U) (bank : Fin 17 ↪ Fin T)
    (G : Matrix (Fin d) (Fin d) (ZMod M)) (rank : ℕ) (hr : rank ≤ d)
    (minor : ∀ t (ht : t < rank), IsUnit (lead (t+1) (lt_of_lt_of_le ht hr) G).det)
    (idem : G*G = G) (L : Matrix (Fin d) (Fin rank) (ZMod M)) (R : Matrix (Fin rank) (Fin d) (ZMod M))
    (factor : G = L*R) (inv : Fin d → ZMod M) (i j : Fin d)
    (mixed : i.rev.val < rank ↔ ¬ j.val < rank) (negative : Bool)
    (H : ℕ) (hm : M < 2^H) (tail rest : List (Fin (A+4))) :
    let k := if j.val < rank then j else i.rev
    let N := (stageAt G rank hr minor k.val (by dsimp [k]; split <;> omega)).M
    let S := stageAt G rank hr minor rank le_rfl
    let δ := fun t : Fin d => if t.val < rank then S.M t t else 1
    let δ' := fun t : Fin d => if t.val < rank then Ring.inverse (S.M t t) else 1
    let K := kMat (pivotMatrix (revPivots d rank))
      (rev d * S.U * rev d * rev d * (S.L * diagonal δ)) * diagonal (fun t => inv t * δ' t)
    let reciprocal := Ring.inverse (S.M k k)
    let signed := if (if j.val < rank then negative else !negative) then -reciprocal else reciprocal
    Writes body (fun F => F (bank 13) = matrixWords A H N ++ tail ∧
      F (bank 16) = (List.ofFn fun t => binSyms H (inv t).val).flatten ++ rest ∧
      F (bank 14) = binSyms H signed.val ∧ F (bank 2) = binSyms H M ∧
      ∀ t : Fin 17, t ≤ 1 ∨ 3 ≤ t ∧ t ≤ 11 → F (bank t) = [])
      (bank 15) (packedHeadCoefficient j.val (i.rev.val*d+j.val) bank)
      (binSyms H (if negative then -(K i j) else K i j).val)
      (8*(j.val*H)+14*H+22+(8*((i.rev.val*d+j.val)*H)+96*H*H+318*H+154)+(2*H+2)) := by
  intro k N S δ δ' K reciprocal signed
  have hk : k.val < rank := by dsimp [k]; split <;> omega
  have diag : S.M k k = N k k := archivedPivot_eq G rank hr minor ⟨k.val,hk⟩ rank le_rfl hk.le
  have coeff := archivedCross_entry G rank hr minor idem L R factor inv i j
  change K i j = _ at coeff
  have value : inv j * N i.rev j * signed = (if negative then -(K i j) else K i j) := by
    dsimp only [signed,reciprocal]
    rw [diag,coeff]
    have same (t : Fin d) (ht : t.val ≤ rank) (eq : k = t) :
        N = (stageAt G rank hr minor t.val ht).M := by subst t; rfl
    by_cases hj : j.val < rank
    · have hi : ¬ i.rev.val < rank := fun h => (mixed.mp h) hj
      have eq : k = j := ite_eq_left hj
      rw [same j hj.le eq,eq]
      cases negative <;> simp only [Bool.false_eq_true,hj,hi,dite_true,dite_false,ite_true,ite_false] <;> ring
    · have hi := mixed.mpr hj
      have eq : k = i.rev := ite_eq_right hj
      rw [same i.rev hi.le eq,eq]
      cases negative <;> simp only [Bool.false_eq_true,hj,hi,dite_true,dite_false,ite_true,ite_false,Bool.not_true,Bool.not_false] <;> ring
  rw [← value]
  exact packedHeadCoefficient_writes body bank N j i.rev inv signed H hm tail rest j

end IntegerMultBounds.MathlibTM2.Cover.Fallback
