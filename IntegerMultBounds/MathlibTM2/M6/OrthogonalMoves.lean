module

public import IntegerMultBounds.MathlibTM2.M6.OrthogonalHeight
import IntegerMultBounds.MathlibTM2.M8.Global.FrameMachine
public import IntegerMultBounds.Networks.Shared50ModularControl

/-! A single reversed coordinate layout for the original orthogonal PR589 frames. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Networks IntegerMultBounds.Networks.Certificates.PR589
open Matrix Nine

private theorem nested_mul {i j : ℕ} (le : Geometry.label i ≤ Geometry.label j) :
    labelProj i * labelProj j = labelProj i ∧ labelProj j * labelProj i = labelProj i := by
  have both (x : Geometry.Address) :
      Geometry.projector i (Geometry.projector j x) = Geometry.projector i x ∧
      Geometry.projector j (Geometry.projector i x) = Geometry.projector i x := by
    simp only [Geometry.projector_eq]
    exact ProjectionRank.project_nested Geometry.form Geometry.form_symm _ _
      (Geometry.restrict_nondegenerate _) (Geometry.restrict_nondegenerate _) le x
  constructor
  all_goals
    simp only [labelProj,← LinearMap.toMatrix'_comp]
    apply congrArg LinearMap.toMatrix'
    apply LinearMap.ext
    intro x
  · exact (both x).1
  · exact (both x).2

open IntegerMultBounds.Swap.Modular Shared50ModularControl in
/-- One fixed rational word specializes at every machine precision. All its
instruction coefficients satisfy the shared tape supplier's height bound. -/
def OrthogonalMoveModular (U : Matrix (Fin 8) (Fin 8) ℚ) : Prop :=
  (∀ op ∈ M8.Rev.revProgram U, ∀ c ∈ M8.Exchange.opCoeffs op,
    c.num.natAbs ≤ coefficientBound ∧ c.den ≤ coefficientBound) ∧
  ∀ w : ℕ, let m := prime^w
    let ops := (M8.Rev.revProgram U).map (AffineFieldProgram.mapOp (ratMod m))
    (∀ op ∈ ops, AffineFieldProgram.Legal op) ∧ ∀ s,
      AffineFieldProgram.run ops s =
        M8.ReversedExchange.revExchangeOf (reduce m (M8.ReversedExchange.rev 8)) (reduce m U) s

open Shared50ModularControl in
private theorem orthogonalMove_modular (basis : Matrix (Fin 8) (Fin 8) ℕ)
    (small : ∀ i j, basis i j ≤ 2^28) (i j : Fin 636) :
    let g := basis.map (Nat.cast : ℕ → ℚ)
    let U := g*(labelProj j-labelProj i)*g⁻¹
    U*U=U → OrthogonalMoveModular U := by
  intro g U idem
  have diff := M8.Height.bounded_sub (labelProj_bounded j) (labelProj_bounded i)
  have height := M8.Height.bounded_mul (M8.Height.bounded_mul (M8.Rev.bounded_natCast small) diff)
    (M8.Rev.bounded_inv_natCast (k := 3) small (by decide))
  have bound : M8.Exchange.expOf (U*M8.ReversedExchange.rev 8) ≤ 2^36 :=
    (M8.Rev.expOf_le (M8.Rev.bounded_mul_rev height)).trans (by simp only [Fintype.card_fin]; decide)
  have primeBound := fun e he => (M8.Rev.revNumbers_le_coefficientBound U (by decide) (by decide) bound e he).trans_lt coefficientBound_lt_prime
  refine ⟨M8.Rev.revProgram_coeffs_le_coefficientBound U (by decide) (by decide) bound,?_⟩
  intro w m ops
  refine ⟨M8.Rev.revProgram_specialize_legal prime_prime primeBound w,?_⟩
  intro s
  have act := M8.Rev.revProgram_map_run (RingHom.id (ZMod m)) idem prime_prime primeBound s
  have idOp : AffineFieldProgram.mapOp (ι := Fin 8) (RingHom.id (ZMod m)) = id := by
    funext op
    cases op <;> first | rfl | (rename_i a; cases a <;> rfl)
  change AffineFieldProgram.run (ops.map _) s = _ at act
  rw [idOp,List.map_id] at act
  exact act

open Shared50ModularControl IntegerMultBounds.Swap.Modular in
private theorem small_admissible {A : Matrix (Fin 8) (Fin 8) ℚ} {e : ℕ}
    (bound : M8.Height.Bounded A (2^e)) (size : e ≤ 2^16) (w : ℕ) :
    Admissible (prime^w) A := by
  apply admissible_of_lt prime_prime
  intro d mem
  exact ((M8.Exchange.den_mem_le bound le_rfl mem).trans (M8.Exchange.le_coefficientBound
    (size.trans (pow_le_pow_right₀ (by decide) (by decide))))).trans_lt coefficientBound_lt_prime

open Shared50ModularControl IntegerMultBounds.Swap.Modular M8.Exchange in
/-- The same residual exchange carries either nested frame into the other. -/
theorem orthogonalResidual_frames (i j : Fin 636) (nested : Geometry.label i ≤ Geometry.label j) (w : ℕ) :
    let P := reduce (prime^w) (labelProj i)
    let Q := reduce (prime^w) (labelProj j)
    ∀ s, exchange (Q-P) (exchange P s) = exchange Q s ∧
      exchange (Q-P) (exchange Q s) = exchange P s := by
  intro P Q s
  have adm (k : Fin 636) := small_admissible (labelProj_bounded k) (by decide) w
  obtain ⟨pq,qp⟩ := nested_mul nested
  have mul (a b c : Fin 636) (eq : labelProj a * labelProj b = labelProj c) :
      reduce (prime^w) (labelProj a) * reduce (prime^w) (labelProj b) = reduce (prime^w) (labelProj c) := by
    rw [← reduce_mul _ (adm a) (adm b),eq]
  have pp : P*P=P := mul i i i (labelProj_mul_self _)
  have qq : Q*Q=Q := mul j j j (labelProj_mul_self _)
  have pq' : P*Q=P := mul i j i pq
  have qp' : Q*P=P := mul j i i qp
  constructor
  · rw [M8.Global.exchange_exchange,Matrix.sub_mul,qp',pp]
    congr 1 <;> abel
  · rw [M8.Global.exchange_exchange,Matrix.sub_mul,qq,pq']
    congr 1 <;> abel

open Shared50ModularControl IntegerMultBounds.Swap.Modular M8.Exchange in
/-- In the shared reversed coordinates the reduced program performs the
actual exchange on the difference of the two original orthogonal frames. -/
theorem orthogonalMove_coordinates (basis : Matrix (Fin 8) (Fin 8) ℕ)
    (small : ∀ a b, basis a b ≤ 2^28) (i j : Fin 636) (w : ℕ) :
    let m := prime^w
    let g := basis.map (Nat.cast : ℕ → ℚ)
    let U := g*(labelProj j-labelProj i)*g⁻¹
    let G := reduce m g
    let C := reduce m (M8.ReversedExchange.rev 8)
    let encode := transform G (C*G)
    g.det ≠ 0 → OrthogonalMoveModular U → IsUnit G ∧ ∀ s,
      AffineFieldProgram.run ((M8.Rev.revProgram U).map (AffineFieldProgram.mapOp (ratMod m))) (encode s) =
        encode (exchange (reduce m (labelProj j)-reduce m (labelProj i)) s) := by
  intro m g U G C encode det spec
  have ga := small_admissible (M8.Rev.bounded_natCast small) (by decide) w
  have gi := small_admissible (M8.Rev.bounded_inv_natCast (k := 3) small (by decide)) (by decide) w
  have proj (l : Fin 636) := small_admissible (labelProj_bounded l) (by decide) w
  have hG : reduce m g⁻¹ * G = 1 := reduce_inverse m gi ga (nonsing_inv_mul g (isUnit_iff_ne_zero.mpr det))
  have diff := ModularFrameSchedule.admissible_sub m (proj j) (proj i)
  let P := reduce m (labelProj j)-reduce m (labelProj i)
  have changeBasis : reduce m U * G = G * P := by
    dsimp only [U]
    rw [reduce_mul m (admissible_mul m ga diff) gi,reduce_mul m ga diff,
      Matrix.mul_assoc _ (reduce m g⁻¹),hG,Matrix.mul_one,ModularFrameSchedule.reduce_sub m (proj j) (proj i)]
  have complement : (1-reduce m U)*G=G*(1-P) := by
    rw [Matrix.sub_mul,Matrix.mul_sub,one_mul,mul_one,changeBasis]
  have rev : Admissible m (M8.ReversedExchange.rev 8) := by
    intro a b
    simp only [M8.ReversedExchange.rev,Matrix.of_apply]
    split <;> simp
  have cc : C*C=1 := reduce_inverse m rev rev M8.ReversedExchange.rev_mul_rev
  refine ⟨isUnit_iff_exists.mpr ⟨_,mul_eq_one_comm.mp hG,hG⟩,?_⟩
  intro s
  rw [(spec.2 w).2]
  change transform 1 C (exchange (reduce m U) (transform 1 C (transform G (C*G) s))) = _
  rw [M8.ReversedExchange.transform_comp,one_mul,← Matrix.mul_assoc,cc,one_mul]
  change transform 1 C (exchange (reduce m U) (transform G G s)) = transform G (C*G) (exchange P s)
  have comm : exchange (reduce m U) (transform G G s) = transform G G (exchange P s) := by
    simp only [M8.Exchange.exchange,transform,Matrix.mulVec_add,Matrix.mulVec_mulVec,changeBasis,complement]
  rw [comm,M8.ReversedExchange.transform_comp,one_mul]

/-- In one bounded integral basis, every nested pair of the 636 original
frames has a reversed program with precisely the billed rank and pivot block.
The zero-to-retained pairs include the nine COPY windows. -/
theorem orthogonalMoves_common_basis :
    ∃ basis : Matrix (Fin 8) (Fin 8) ℕ,
      (∀ a b, basis a b ≤ 2^28) ∧ (basis.map (Nat.cast : ℕ → ℚ)).det ≠ 0 ∧
      ∀ i j : Fin 636, Geometry.label i ≤ Geometry.label j →
        let g := basis.map (Nat.cast : ℕ → ℚ)
        let U := g * (labelProj j - labelProj i) * g⁻¹
        let rank := Geometry.moveRank i j
        OrthogonalMoveModular U ∧
        (∀ s, AffineFieldProgram.run (M8.Rev.revProgram U) s =
          M8.ReversedExchange.revExchange U s) ∧
        AffineFieldProgram.interchanges (M8.Rev.revProgram U) = rank ∧
        ∀ a b, AffineFieldProgram.Op.interchange a b ∈ M8.Rev.revProgram U ↔
          (a,b) ∈ M8.ReversedExchange.revPivots 8 rank := by
  classical
  let residual := fun p : Fin 636 × Fin 636 =>
    if Geometry.label p.1 ≤ Geometry.label p.2 then labelProj p.2 - labelProj p.1 else 0
  have idem (p) : IsIdempotentElem (residual p) := by
    unfold residual
    split
    · rename_i le
      obtain ⟨ab,ba⟩ := nested_mul le
      exact M8.Exchange.sub_idempotent _ _ (labelProj_mul_self _) (labelProj_mul_self _) ab ba
    · exact zero_mul _
  obtain ⟨basis,bound,det,generic⟩ := M8.GenericBasis.exists_generic_basis_of_idempotent
    (fun k => residual (finProdFinEquiv.symm k)) (fun k => idem _)
  have degree (r : Fin (636*636) → ℕ) : M8.GenericBasis.degreeBound 8 r ≤ 2^28 := by
    have per (j) : (∑ i ∈ M8.GenericBasis.sizes (m := 8) (r j), i.val*(8+1)) ≤ 9*72 := by
      calc
        _ ≤ ∑ _i ∈ M8.GenericBasis.sizes (m := 8) (r j), 72 :=
          Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right 9 (show i.val ≤ 8 from Nat.le_of_lt_succ i.isLt)
        _ ≤ _ := by
          simp only [Finset.sum_const,smul_eq_mul]
          exact Nat.mul_le_mul_right _ (Finset.card_le_univ _)
    calc
      _ ≤ 8 + ∑ _j : Fin (636*636), 9*72 := Nat.add_le_add_left (Finset.sum_le_sum fun j _ => per j) _
      _ ≤ _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]; decide
  refine ⟨basis,fun a b => (bound a b).trans (degree _),det,?_⟩
  intro i j le g U rank
  have h := generic (finProdFinEquiv (i,j))
  have id := idem (i,j)
  simp only [Equiv.symm_apply_apply,residual,le,ite_true] at h id
  have unit : IsUnit g.det := isUnit_iff_ne_zero.mpr det
  have conjugate : U.rank = (labelProj j - labelProj i).rank := by
    rw [show U = _ from rfl,rank_mul_eq_left_of_isUnit_det _ _ (by simpa using unit.inv),
      rank_mul_eq_right_of_isUnit_det _ _ unit]
  have price : (labelProj j - labelProj i).rank = rank := by
    change Module.finrank ℚ (LinearMap.range (Matrix.toLin' (labelProj j - labelProj i))) = _
    rw [labelProj,labelProj,← map_sub,Matrix.toLin'_toMatrix']
    rfl
  have uidem : U*U=U := by
    dsimp only [U]
    calc
      _ = g * ((labelProj j-labelProj i)*(g⁻¹*g)*(labelProj j-labelProj i))*g⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [nonsing_inv_mul g unit,Matrix.mul_one,id.eq]
  have pivots := M8.Rev.mem_revProgram_interchange U (conjugate.symm ▸ h)
  exact ⟨orthogonalMove_modular basis (fun a b => (bound a b).trans (degree _)) i j uidem,
    M8.Rev.revProgram_run U uidem,(M8.Rev.revProgram_interchanges U).trans (conjugate.trans price),
    fun a b => (pivots a b).trans (by rw [conjugate,price])⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
