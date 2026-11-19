module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import IntegerMultBounds.MathlibTM2.Cover.FallbackClass

/-! Recover the projector and its residue-table entry at a physical record index. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
noncomputable section
open IntegerMultBounds.Machine.FlatCoordinateLayout
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open IntegerMultBounds.Swap.Modular (reduce Admissible)
variable {m w n : ℕ}
local notation "M" => prime^w
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

def physicalLabel (m w j : ℕ) : LabelPadding.Label m w :=
  let addr : Fin ((prime^w)^(m*m)) := ⟨j % _, Nat.mod_lt _ (pow_pos (pow_pos prime_prime.pos _) _)⟩
  fun r c => coordinates addr (finProdFinEquiv (c,r))

theorem physicalLabel_index (j : ℕ) :
    j / M^(m*m) * M^(m*m) + (LabelAddress.address (physicalLabel m w j)).val = j := by
  let addr : Fin (M^(m*m)) := ⟨j % _, Nat.mod_lt _ (pow_pos (pow_pos prime_prime.pos _) _)⟩
  have digits : M8.AtomOps.refine (Route.cols (physicalLabel m w j)) = coordinates addr := by
    funext i
    simp [M8.AtomOps.refine, Route.cols, physicalLabel, addr]
    exact congrArg (coordinates addr) (finProdFinEquiv.apply_symm_apply i)
  rw [LabelAddress.address,digits,rank_coordinates,Nat.mul_comm]
  exact Nat.div_add_mod ..

theorem physicalLabel_residue (hw : 0 < w) (j : ℕ) :
    LabelStock.residue m w 1 j = (LabelRing.res prime w hw).mapMatrix (physicalLabel m w j) := by
  simpa only [Nat.mul_one,Nat.add_zero,physicalLabel_index] using
    LabelStock.residue_at hw (j / M^(m*m)) 1 0 (by decide) (physicalLabel m w j)

theorem physicalLabel_live (hw : 0 < w) (j : ℕ) :
    LabelStock.live m w 1 j = true ↔ IsUnit (physicalLabel m w j) := by
  simp only [LabelStock.live,decide_eq_true_eq,physicalLabel_residue hw]
  exact (not_congr (LabelPadding.singular_iff hw _)).symm.trans (by simp)

theorem physicalLabel_address (g : LabelPadding.Label m w) : physicalLabel m w (LabelAddress.address g).val = g := by
  funext r c
  simp only [physicalLabel,Nat.mod_eq_of_lt (LabelAddress.address g).isLt,Fin.eta]
  simp [LabelAddress.address,M8.AtomOps.refine,Route.cols]

open Finset in
/-- A request predicate on labels selects the same number of records in each
physical box, including when the boxes have spectator prefixes. -/
theorem physicalLabel_count (m w parents : ℕ) (keep : LabelPadding.Label m w → Bool) :
    let box := (prime^w)^(m*m)
    (List.range (parents*box)).countP (fun j => keep (physicalLabel m w j)) =
      parents*(univ.filter fun g => keep g = true).card := by
  classical
  intro box
  let selected := fun j => keep (physicalLabel m w j)
  have single : (List.range box).countP selected = (univ.filter fun g => keep g = true).card := by
    have counted := (List.nodup_range (n := box)).card_eq_countP (P := fun j => selected j = true)
    have rangeSet : (List.range box).toFinset = Finset.range box := by ext; simp
    rw [rangeSet] at counted
    apply (show (List.range box).countP selected = ((Finset.range box).filter fun j => selected j = true).card
      by simpa using counted.symm).trans
    apply Finset.card_bij (fun j _ => physicalLabel m w j)
    · intro j hj
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hj).2⟩
    · intro i hi j hj same
      have index (k : ℕ) (hk : k < box) : (LabelAddress.address (physicalLabel m w k)).val = k := by
        change k < (prime^w)^(m*m) at hk
        simpa only [Nat.div_eq_of_lt hk,Nat.zero_mul,Nat.zero_add] using
          (physicalLabel_index (m := m) (w := w) k)
      simpa only [index i (mem_range.mp (mem_filter.mp hi).1), index j (mem_range.mp (mem_filter.mp hj).1)]
        using congrArg (fun g => (LabelAddress.address g).val) same
    · intro g hg
      exact ⟨(LabelAddress.address g).val, mem_filter.mpr ⟨mem_range.mpr (LabelAddress.address g).isLt,
        by simpa [selected,physicalLabel_address] using (mem_filter.mp hg).2⟩, physicalLabel_address g⟩
  have periodic (p j : ℕ) : selected (p*box+j) = selected j := by simp [selected,physicalLabel,box,Nat.add_mod]
  change (List.range (parents*box)).countP selected = _
  induction parents with
  | zero => simp
  | succ p ih =>
    rw [Nat.succ_mul,List.range_add,List.countP_append,List.countP_map,ih,Nat.succ_mul]
    simp only [Function.comp_def,periodic,single]

open GoodForm in
open scoped Classical in
def fallbackBit {r : ℕ} (hr : r ≤ m) (proj g : LabelPadding.Label m w) : Bool :=
  decide (IsUnit g ∧ ∃ k, ∃ hk : k < r, ¬IsUnit (lead (k+1) (lt_of_lt_of_le hk hr) (g*proj*g⁻¹)).det)

/-- On the scan tapes, fallback is exactly the live bit with the good-move
test cleared. Singular padding is excluded even at rank zero. -/
theorem fallbackBit_eq (hw : 0 < w) {r : ℕ} (hr : r ≤ m) (proj : LabelPadding.Label m w) (j : ℕ) :
    fallbackBit hr proj (physicalLabel m w j) =
      (LabelStock.live m w 1 j && !LabelProjector.good ((LabelRing.res prime w hw).mapMatrix proj) r hr
        (LabelStock.residue m w 1 j)) := by
  classical
  let g := physicalLabel m w j
  have live := physicalLabel_live (m := m) hw j
  by_cases unit : IsUnit g
  · have test := LabelProjector.good_at hw proj g ((Matrix.isUnit_iff_isUnit_det g).mp unit)
      r hr (j/(prime^w)^(m*m))
    rw [show j/(prime^w)^(m*m)*(prime^w)^(m*m)+(LabelAddress.address g).val = j from physicalLabel_index j] at test
    rw [live.mpr unit, Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    simp only [fallbackBit, decide_eq_true_eq, Bool.not_eq_true']
    change (IsUnit g ∧ _) ↔ _
    simp only [unit, true_and]
    rw [← Bool.not_eq_true, test]
    push Not
    rfl
  · have dead : LabelStock.live m w 1 j = false := Bool.eq_false_iff.mpr (fun h => unit (live.mp h))
    simp [fallbackBit, dead, show ¬IsUnit (physicalLabel m w j) from unit]

open Matrix Finset IntegerMultBounds.Swap.LowerTriangular IntegerMultBounds.Swap.Modular
  IntegerMultBounds.Swap.Shear M8.Exchange M8.ReversedExchange in
/-- A live record whose fallback bit is clear has the one-child weighted move. -/
theorem goodMove_of_fallbackBit_false (hw : 0 < w) (P : Matrix (Fin m) (Fin m) ℚ)
    (idempotent : P*P = P) (f : Factorization univ univ P)
    (hd : ∀ d ∈ factorizationDenominators f, d < prime) (hr : P.rank ≤ m)
    (j : ℕ) (live : LabelStock.live m w 1 j = true)
    (clear : fallbackBit hr (reduce (prime^w) P) (physicalLabel m w j) = false)
    (α α' : Fin m → ZMod (prime^w)) (hα : ∀ i, α i * α' i = 1) :
    let g := physicalLabel m w j
    ∃ (L L' R R' K : LabelPadding.Label m w) (δ δ' : Fin m → ZMod (prime^w)),
      GoodForm.UnitLower L ∧ GoodForm.UnitLower L' ∧ GoodForm.UnitLower R ∧ GoodForm.UnitLower R' ∧
      (∀ i, δ i * δ' i = 1) ∧ ∀ s : State (Fin m) (ZMod (prime^w)),
        transform (diagonal α * L * diagonal α') R'
          (cross (-K) (Weighted.child P.rank (fun i => α i * δ i) (fun i => α' i * δ' i)
            (cross K (transform (diagonal α * L' * diagonal α') R s)))) =
          transform (diagonal α) 1 (revExchangeOf (rev m) (g * reduce (prime^w) P * g⁻¹) (transform (diagonal α') 1 s)) := by
  intro g
  have unit := (physicalLabel_live hw j).mp live
  have adm : Admissible (prime^1) P := admissible_of_lt prime_prime (fun d h => hd d (by simp [factorizationDenominators,h])) 1
  have residue := LabelProjector.residue_reduce hw P (by simpa using adm)
  rw [fallbackBit_eq hw, live, Bool.true_and, residue] at clear
  apply LabelProjector.good_move_at hw P idempotent f hd hr g ((Matrix.isUnit_iff_isUnit_det g).mp unit)
    (j/(prime^w)^(m*m)) α α' hα
  rw [show j/(prime^w)^(m*m)*(prime^w)^(m*m)+(LabelAddress.address g).val = j from physicalLabel_index j]
  simpa using clear

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal LabelCycle GoodForm in
open scoped Classical in
/-- One residue-table program emits the fallback bit for each physical record,
uniformly over all widths and lifts of the request matrix. -/
theorem fallbackMask_writes {T Q A : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (r : ℕ) (hr : r ≤ m) (request : Matrix (Fin m) (Fin m) (ZMod prime))
    (rs : List (Pair T)) (hk : rs.length = m*m) (out count saved : Fin T)
    (regs : (count :: saved :: (slots rs ++ [out])).Nodup) :
    ∃ program : Pr P T Q A U, ∀ (v : RecursiveInterchangeLayout.Descriptor) (w B : ℕ)
      (proj : LabelPadding.Label m (w+1)), (LabelRing.res prime (w+1) (by omega)).mapMatrix proj = request →
      v.beforeH = B*prime^(m*((w+1)*m)) →
      let fallback := fun j => fallbackBit hr proj (physicalLabel m (w+1) j)
      Writes body (fun R => ready (prime^w) R rs ∧ R saved = [] ∧
        (R count).length = v.beforeRows*v.rows*B) out program
        (((List.range (LabelMask.records v)).map fallback).map bitSymbol)
        ((v.beforeRows*v.rows*B)*(time (prime^w) (m*m) 1+5)+4) := by
  classical
  let branch := fun g : Matrix (Fin m) (Fin m) (ZMod prime) =>
    decide (g.det ≠ 0) && !LabelProjector.good request r hr g
  obtain ⟨program,run⟩ := class_writes (body := body) m branch rs hk out count saved regs
  refine ⟨program, ?_⟩
  intro v w B proj reduction shape fallback
  have bits (j : ℕ) : branch (LabelStock.residue m (w+1) 1 j) = fallback j := by
    simp only [fallback, fallbackBit_eq (by omega : 0 < w+1), reduction, branch, LabelStock.live]
  simpa only [bits,Nat.add_one_sub_one] using run v (w+1) B (by omega) shape

open GoodForm Finset in
open scoped Classical in
/-- The minor-degree fallback bound holds on the actual record range of the
pass, with every spectator box included. -/
theorem fallbackRecordCount (w r parents : ℕ) (hr : r ≤ m) (P : LabelPadding.Label m (w+1))
    (g₀ : Matrix (Fin m) (Fin m) (ZMod prime)) (unit : g₀.det ≠ 0)
    (good : ∀ k (hk : k < r), (lead (k+1) (lt_of_lt_of_le hk hr)
      (g₀ * (LabelRing.res prime (w+1) (by omega)).mapMatrix P * g₀⁻¹)).det ≠ 0) :
    let box := (prime^(w+1))^(m*m)
    let fallback := fallbackBit hr P
    (List.range (parents*box)).countP (fun j => fallback (physicalLabel m (w+1) j)) * prime ≤
      (∑ k ∈ range r, (k+1)*(m+1)) * (parents*box) := by
  classical
  intro box fallback
  rw [physicalLabel_count m (w+1) parents fallback, Nat.mul_assoc]
  have bound := LabelPadding.fallback_count w r hr P g₀ unit good
  have card : Fintype.card (LabelPadding.Label m (w+1)) = box := by
    change Fintype.card (Fin m → Fin m → ZMod (prime^(w+1))) = _
    simp [box, ← pow_mul, Nat.mul_assoc]
  rw [card] at bound
  simp only [fallback,fallbackBit,decide_eq_true_eq]
  exact (Nat.mul_le_mul_left parents bound).trans_eq (by ring)

/-- The live addresses of one complete box enumerate the invertible matrices exactly once. -/
theorem liveLabelCount (hw : 0 < w) :
    (List.range (M^(m*m))).countP (LabelStock.live m w 1) = Nat.card (LabelPadding.Label m w)ˣ := by
  classical
  let box := M^(m*m)
  let live := (Finset.range box).filter fun j => LabelStock.live m w 1 j = true
  have bounds (j : live) : j.val < box := Finset.mem_range.mp (Finset.mem_filter.mp j.property).1
  let encode (g : (LabelPadding.Label m w)ˣ) : live := ⟨(LabelAddress.address g.val).val,
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (LabelAddress.address g.val).isLt,
      (physicalLabel_live hw _).mpr (by rw [physicalLabel_address]; exact g.isUnit)⟩⟩
  let e : live ≃ (LabelPadding.Label m w)ˣ := {
    toFun := fun j => ((physicalLabel_live hw _).mp (Finset.mem_filter.mp j.property).2).unit
    invFun := encode
    left_inv := by
      intro j
      apply Subtype.ext
      change (LabelAddress.address (physicalLabel m w j.val)).val = j.val
      simpa only [Nat.div_eq_of_lt (show j.val < M^(m*m) from bounds j),Nat.zero_mul,Nat.zero_add] using
        (physicalLabel_index (m := m) (w := w) j.val)
    right_inv := fun g => Units.ext (physicalLabel_address g.val) }
  have counted := (List.nodup_range (n := box)).card_eq_countP (P := fun j => LabelStock.live m w 1 j = true)
  have rangeSet : (List.range box).toFinset = Finset.range box := by ext; simp
  rw [rangeSet] at counted
  calc
    _ = live.card := by simpa [live,box] using counted.symm
    _ = _ := by simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using Nat.card_congr e

/-- The finite-field factor counts independent choices for successive columns. -/
theorem liveClasses_eq_product (m : ℕ) :
    LabelPadding.liveClasses m = ∏ i : Fin m, (prime^m - prime^i.val) := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  have units := LabelPadding.unit_count (m := m) 0
  simp only [pow_zero,one_pow,mul_one] at units
  rw [← units,show Nat.card (LabelPadding.Label m (0+1))ˣ = Nat.card (Matrix (Fin m) (Fin m) (ZMod prime))ˣ from
    congrArg (fun q => Nat.card (Matrix (Fin m) (Fin m) (ZMod q))ˣ) (pow_one prime)]
  simpa only [ZMod.card] using Matrix.card_GL_field (𝔽 := ZMod prime) m

/-- The last column must avoid a hyperplane. Thus at most a fraction
`(prime-1)/prime` of the payload lies in invertible classes at positive rank. -/
theorem liveClassVolume_le (m copies : ℕ) (positive : 0 < m) :
    prime * (LabelPadding.liveClasses m * copies) ≤
      (prime-1) * (prime^(m*m) * copies) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero positive.ne'
  rw [liveClasses_eq_product, Fin.prod_univ_castSucc]
  let q := prime^(n+1)
  have firstColumns : (∏ i : Fin n, (q - prime^i.val)) ≤ q^n := by
    calc
      _ ≤ ∏ _ : Fin n, q := Finset.prod_le_prod fun i _ => Nat.sub_le _ _
      _ = _ := by simp
  have last : q - prime^n = prime^n*(prime-1) := by
    simp only [q, pow_succ, Nat.mul_sub, Nat.mul_one]
  change prime * (((∏ i : Fin n, (q - prime^i.val)) * (q-prime^n)) * copies) ≤ _
  grw [firstColumns, last]
  rw [show prime^((n+1)*(n+1)) = q^n * (prime^n*prime) by
    rw [pow_mul, pow_succ (prime^(n+1)) n]; rfl]
  exact le_of_eq (by ring)

theorem physicalProjector_spec (hw : 0 < w) (j : ℕ) (live : LabelStock.live m w 1 j = true)
    (e : (Fin m ⊕ Fin m) ≃ Fin n) (P : Matrix (Fin m) (Fin m) ℚ) (hp : P*P = P)
    (adm : Admissible prime P) (α α' : Fin m → ZMod M) (ha : ∀ i, α i * α' i = 1) :
    let g := physicalLabel m w j
    let φ := LabelRing.res prime w hw
    let G := projectorResidual e (reduce M P) α α' g
    (G.det = 1 ∨ G.det = -1) ∧ φ.mapMatrix G =
      projectorResidual e (reduce prime P) (φ ∘ α) (φ ∘ α') (LabelStock.residue m w 1 j) := by
  intro g φ G
  have unit := (physicalLabel_live hw j).mp live
  have det := (Matrix.isUnit_iff_isUnit_det _).mp unit
  have liftAdm : Admissible M P := fun r c => (adm r c).pow_right w
  exact ⟨projectorResidual_sign hw e _ (by rw [← IntegerMultBounds.Swap.Modular.reduce_mul _ liftAdm liftAdm,hp]) α α' ha g det,
    by rw [physicalLabel_residue hw]; exact projectorResidual_class hw e P adm α α' g det⟩

end
end IntegerMultBounds.MathlibTM2.Cover.Fallback
