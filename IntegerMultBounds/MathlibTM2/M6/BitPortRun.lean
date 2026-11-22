module

public import IntegerMultBounds.MathlibTM2.M6.BitCopyLabel
public import IntegerMultBounds.MathlibTM2.M6.BitPortImage
public import IntegerMultBounds.MathlibTM2.M6.BitPortInverse
public import IntegerMultBounds.MathlibTM2.Cover.FallbackColumnHost
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPrefixVolume
import Mathlib.Algebra.Group.Pi.Units

/-! Physical passes for the PR589 port-frame correction. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Stack Host Cover.Fallback
open Shared50ModularControl (prime)

local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

open M8.Machine.Segments IntegerMultBounds.Swap.Modular in
/-- The two port basis changes use fixed tape programs. Each maps both
eight-digit fields, preserves the spectator and costs at most a constant
times the payload volume, uniformly in the width. -/
theorem frameBasis_runs (l : Fin 636) (inverse : Bool) :
    ∃ stages : List (FlatCoordinateSchedule.Op 16), ∀ (w W : ℕ) (_hW : 0 < W)
      (x : Fin ((prime^w)^16*W) → ZMod 2),
      let bank := fun (y : Fin ((prime^w)^16*W) → ZMod 2) => SharedBankStageInput.raw
        (FlatCoordinateShiftSharedBank.common (d := 16) (b := w) (W := W)
          (fun i => SparseRoleCircuit.encode (y i))) (FlatCoordinateCleanSchedule.tapeCount stages)
      let M := reduce (prime^w) (frameBasis l inverse)
      ∃ y, HoareTime (FlatCoordinateCleanSchedule.program stages) (fun z => z = bank x)
        (fun z => z = bank y) (FlatCoordinateCleanSchedule.constant stages * ((prime^w)^16*W)) ∧
        ∀ s j, y (FlatCoordinateLayout.index (AffineFieldCoordinates.embed (M8.Exchange.transform M M s)) j) =
          x (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j) := by
  obtain ⟨pass,action⟩ := frameBasis_pass l inverse
  let B := frameBasis l inverse
  let ops := M8.Exchange.transformOps B B
  refine ⟨description ops pass.good,?_⟩
  intro w W hW x bank M
  obtain ⟨y,exec,reads⟩ := copySegment_runs ops pass.good hW x (pass.legal w)
  exact ⟨y,exec,fun s j => (action w s) ▸ reads s j⟩

/-- The payload tape shared by every factor of a port correction. -/
noncomputable def portOwner {V : ℕ} (x : Fin V → ZMod 2) : Tapes 1 prime :=
  ⟨fun _ => 0,fun _ => putWord (fun _ => blank) 0
    (List.ofFn fun i => SparseRoleCircuit.encode (a := prime) (x i))⟩

private theorem fieldPass_owner
    (act : ∀ w : ℕ, IntegerMultBounds.Swap.Shear.State (Fin 8) (ZMod (prime^w)) →
      IntegerMultBounds.Swap.Shear.State (Fin 8) (ZMod (prime^w)))
    (stages : List (FlatCoordinateSchedule.Op 16))
    (runs : ∀ (w W : ℕ), 0 < W → ∀ x : Fin ((prime^w)^16*W) → ZMod 2,
      let bank := fun (y : Fin ((prime^w)^16*W) → ZMod 2) => SharedBankStageInput.raw
        (FlatCoordinateShiftSharedBank.common (d := 16) (b := w) (W := W)
          (fun i => SparseRoleCircuit.encode (y i))) (FlatCoordinateCleanSchedule.tapeCount stages)
      ∃ y, HoareTime (FlatCoordinateCleanSchedule.program stages) (fun z => z = bank x)
        (fun z => z = bank y) (FlatCoordinateCleanSchedule.constant stages * ((prime^w)^16*W)) ∧
        ∀ s j, y (FlatCoordinateLayout.index (AffineFieldCoordinates.embed (act w s)) j) =
          x (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j)) :
    ∃ (c : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w W, 0 < W →
      let V := (prime^w)^16*W
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V), SharedBankSkeleton.ofStage stage = machine ∧ stage.cost = c*V ∧
        ∀ x s j, stage.transform x (FlatCoordinateLayout.index
          (AffineFieldCoordinates.embed (act w s)) j) =
          x (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j) := by
  let machine : SharedBankSkeleton.Skeleton 1 prime :=
    ⟨_,_,FlatCoordinateCleanSchedule.program stages,fun _ => segmentSource stages,fun _ _ _ => Subsingleton.elim _ _⟩
  refine ⟨FlatCoordinateCleanSchedule.constant stages,machine,?_⟩
  intro w W pos V
  let bank := fun (x : Fin V → ZMod 2) => SharedBankStageInput.raw
    (FlatCoordinateShiftSharedBank.common (d := 16) (b := w) (W := W)
      (fun i => SparseRoleCircuit.encode (x i))) (FlatCoordinateCleanSchedule.tapeCount stages)
  let slot := fun _ : Fin 1 => segmentSource stages
  choose out exec read using runs w W pos
  have payload (x : Fin V → ZMod 2) : SharedBank.payload (bank x) slot = portOwner x := by
    obtain ⟨head,tape⟩ := copySegment_source stages x
    exact congrArg₂ Tapes.mk (funext fun _ => head)
      (funext fun _ => tape.trans (sourceWord_cast _ x))
  have strip (x : Fin V → ZMod 2) : SharedBank.strip (bank x) slot = basisWorkspace stages x := by
    apply congrArg₂ Tapes.mk <;> funext j <;> by_cases eq : segmentSource stages = j
    all_goals first
      | subst j; simp [SharedBank.strip,slot,basisWorkspace,SharedPlacementAlphabet.setTape]
      | simp [SharedBank.strip,slot,eq,basisWorkspace,SharedPlacementAlphabet.setTape,Function.update_of_ne (Ne.symm eq),bank]
  exact ⟨{
    tapes := _, states := _, program := FlatCoordinateCleanSchedule.program stages,
    transform := out, input := bank, output := fun x => bank (out x), slots := slot,
    slots_injective := fun _ _ _ => Subsingleton.elim _ _, cost := _, metadata := basisWorkspace stages (0 : Fin V → ZMod 2),
    input_payload := payload, output_payload := fun x => payload (out x),
    strip_input := fun x => (strip x).trans (basisWorkspace_eq stages x 0), realizes := exec },rfl,rfl,read⟩

open M8.Machine.Segments IntegerMultBounds.Swap.Modular in
/-- A fixed nonrecursive field segment acts on the owner tape at linear
volume cost and preserves the trailing spectator. -/
theorem fieldSegment_owner (ops : List (AffineFieldProgram.Op (Fin 8) ℚ)) (good : Good ops)
    (legal : ∀ w : ℕ, ∀ op ∈ ops.map (AffineFieldProgram.mapOp (ratMod (prime^w))), AffineFieldProgram.Legal op) :
    ∃ (c : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w W, 0 < W →
      let V := (prime^w)^16*W
      let run := AffineFieldProgram.run (ops.map (AffineFieldProgram.mapOp (ratMod (prime^w))))
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧ stage.cost = c*V ∧ ∀ x s j,
          stage.transform x (FlatCoordinateLayout.index (AffineFieldCoordinates.embed (run s)) j) =
            x (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j) := by
  apply fieldPass_owner _ (description ops good)
  exact fun w W hW x => copySegment_runs ops good hW x (legal w)

open IntegerMultBounds.Swap.Modular in
theorem frameBasis_owner (l : Fin 636) (inverse : Bool) :
    ∃ (c : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w W, 0 < W →
      let V := (prime^w)^16*W
      let M := reduce (prime^w) (frameBasis l inverse)
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V), SharedBankSkeleton.ofStage stage = machine ∧ stage.cost = c*V ∧
        ∀ x s j, stage.transform x (FlatCoordinateLayout.index
          (AffineFieldCoordinates.embed (M8.Exchange.transform M M s)) j) =
          x (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j) := by
  obtain ⟨stages,runs⟩ := frameBasis_runs l inverse
  exact fieldPass_owner (fun w => let M := reduce (prime^w) (frameBasis l inverse)
                                  M8.Exchange.transform M M) stages runs

open M8.Machine.Segments IntegerMultBounds.Swap.Modular in
private theorem forwardDigit_owner (reflect : Bool) :
    ∃ (c : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w W, 0 < W →
      let V := (prime^w)^16*W
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧ stage.cost = c*V ∧
        ∀ x s j, let op : AffineFieldProgram.Op (Fin 8) (ZMod (prime^w)) :=
                   if reflect then .subFromD 0 7 else .addToD 0 7
          stage.transform x (FlatCoordinateLayout.index (AffineFieldCoordinates.embed
            (AffineFieldProgram.execute op s)) j) =
            x (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j) := by
  let op : AffineFieldProgram.Op (Fin 8) ℚ := if reflect then .subFromD 0 7 else .addToD 0 7
  have good : Good [op] := by
    constructor <;> intro a ha <;> obtain rfl : a = op := List.mem_singleton.mp ha <;>
      try (cases reflect <;> trivial)
    apply M8.Machine.Coordinates.CoeffBounded.supported _ (by cases reflect <;> trivial)
    intro r hr
    have sign : r = 1 ∨ r = -1 := by
      cases reflect <;> simp [op,M8.Exchange.opCoeffs] at hr <;> tauto
    have one : 1 ≤ coefficientBound := Nat.one_le_two_pow
    rcases sign with rfl | rfl <;> exact ⟨by simpa using one,by simpa using one⟩
  apply fieldPass_owner _ (description [op] good)
  intro w W hW x
  have legal : ∀ a ∈ [AffineFieldProgram.mapOp (ratMod (prime^w)) op], AffineFieldProgram.Legal a := by
    intro a ha
    obtain rfl := List.mem_singleton.mp ha
    cases reflect <;> trivial
  obtain ⟨y,exec,read⟩ := copySegment_runs [op] good hW x legal
  exact ⟨y,exec,fun s j => by cases reflect <;> exact read s j⟩

open Matrix in
/-- In this basis column `i` is the direction of a shear. The remaining
columns, apart from `j`, lie in the kernel of its control row. -/
def shearBasis {d : ℕ} {R : Type*} [CommRing R] (i j : Fin d)
    (v n : Fin d → R) (q : R) : Matrix (Fin d) (Fin d) R := fun a b =>
  if b = i then v a else if b = j then (Pi.single j 1 : Fin d → R) a
  else ((Pi.single b 1 : Fin d → R) - (Pi.single j (q*n b) : Fin d → R)) a

open Matrix in
theorem shearBasis_spec {d : ℕ} {R : Type*} [CommRing R] {i j : Fin d}
    {v n : Fin d → R} {q : R} (order : i < j)
    (direction : ∀ a, a < i → v a = 0) (control : ∀ b, j < b → n b = 0)
    (pivot : IsUnit (v i)) (inv : n j * q = 1) (zero : n ⬝ᵥ v = 0) :
    let B := shearBasis i j v n q
    IntegerMultBounds.Swap.Shear.LowerTriangular B ∧ IsUnit B ∧
      (∀ a, B a i = v a) ∧ n ᵥ* B = Pi.single j (n j) := by
  intro B
  have lower : IntegerMultBounds.Swap.Shear.LowerTriangular B := by
    intro a b hab
    by_cases hi : b = i
    · subst b; simpa [B,shearBasis] using direction a hab
    by_cases hj : b = j
    · subst b; simp [B,shearBasis,hi,Pi.single_eq_of_ne hab.ne]
    by_cases eq : a = j
    · subst a; simp [B,shearBasis,hi,hj,control b hab,Pi.single_eq_of_ne hab.ne]
    · simp [B,shearBasis,hi,hj,Pi.single_eq_of_ne hab.ne,Pi.single_eq_of_ne eq]
  have diag (a : Fin d) : IsUnit (B a a) := by
    by_cases hi : a = i
    · subst a; simpa [B,shearBasis] using pivot
    by_cases hj : a = j <;> simp [B,shearBasis,hi,hj,order.ne.symm,Pi.single_eq_of_ne]
  refine ⟨lower,(Matrix.isUnit_iff_isUnit_det _).mpr ?_,by simp [B,shearBasis],?_⟩
  · rw [B.det_of_isLowerTriangular lower]
    suffices h : ∀ s : Finset (Fin d), IsUnit (∏ a ∈ s, B a a) from h _
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s fresh ih => simpa [Finset.prod_insert fresh] using (diag a).mul ih
  · funext b
    by_cases hi : b = i
    · subst b
      simpa [B,shearBasis,Matrix.vecMul,Pi.single_eq_of_ne order.ne] using zero
    by_cases hj : b = j
    · subst b; simp [B,shearBasis,Matrix.vecMul,hi,dotProduct_single]
    · change n ⬝ᵥ (fun a => B a b) = _
      simp only [B,shearBasis,if_neg hi,if_neg hj,Pi.single_eq_of_ne hj]
      change n ⬝ᵥ (Pi.single b 1 - Pi.single j (q*n b)) = 0
      rw [dotProduct_sub,dotProduct_single,dotProduct_single,mul_one,← mul_assoc,inv,one_mul,sub_self]

open Matrix in
/-- Updating one digit in the shear basis performs the full rank-one
update on packed addresses. -/
theorem shearBasis_shift {d : ℕ} {R : Type*} [CommRing R]
    {B : Matrix (Fin d) (Fin d) R} {n v : Fin d → R} {i j : Fin d}
    (column : ∀ a, B a i = v a) (row : n ᵥ* B = Pi.single j (n j))
    (c : R) (x : Fin d → R) :
    B *ᵥ OrderedAffine.execute (.shift i j (c*n j)) x =
      B *ᵥ x + (c * (n ⬝ᵥ (B *ᵥ x))) • v := by
  let k := (c*n j)*x j
  have shift : OrderedAffine.execute (.shift i j (c*n j)) x = x + Pi.single i k := by
    funext a
    by_cases eq : a = i
    · subst a; simp [OrderedAffine.execute,k]
    · simp [OrderedAffine.execute,Function.update_of_ne eq,Pi.single_eq_of_ne eq]
  rw [shift,mulVec_add,dotProduct_mulVec,row,single_dotProduct]
  congr 1
  funext a
  change (fun b => B a b) ⬝ᵥ Pi.single i k = c * (n j * x j) * v a
  rw [dotProduct_single,column,mul_comm (v a)]
  simp only [k,mul_assoc]

open Matrix AffineFieldCoordinates in
/-- On the packed tape the two address halves give a single control row
and a single direction column for both port shears. -/
theorem embed_portShear {R : Type*} [CommRing R] (c : R) (n v : Fin 8 → R)
    (zero : n ⬝ᵥ v = 0) (s : Swap.Shear.State (Fin 8) R) :
    let row := embed (n,-n)
    let direction := embed (-v,v)
    embed (portShearEquiv c n v zero s) = embed s + (c*(row ⬝ᵥ embed s)) • direction := by
  intro row direction
  have control : row ⬝ᵥ embed s = n ⬝ᵥ (s.1-s.2) := by
    change (∑ i : Fin (8+8), embed (n,-n) i * embed s i) = _
    rw [Fin.sum_univ_add,dotProduct_sub]
    simp only [embed,Fin.addCases_left,Fin.addCases_right,Pi.neg_apply,neg_mul,Finset.sum_neg_distrib,
      dotProduct,sub_eq_add_neg]
  rw [control]
  funext i
  induction i using Fin.addCases <;>
    simp only [direction,embed,portShearEquiv,Equiv.coe_fn_mk,Pi.add_apply,Pi.smul_apply,
      Fin.addCases_left,Fin.addCases_right,Pi.sub_apply,Pi.neg_apply,smul_eq_mul,mul_neg,sub_eq_add_neg]

open Matrix AffineFieldCoordinates in
/-- The sole nontriangular operation is a shift from the second half into
the first. Its pivots are the first direction digit and last control digit. -/
theorem portShear_shift {R : Type*} [CommRing R] (c : R) (n v : Fin 8 → R)
    (zero : n ⬝ᵥ v = 0) (i j : Fin 8) (q : R)
    (direction : ∀ a, a < i → v a = 0) (control : ∀ b, j < b → n b = 0)
    (pivot : IsUnit (v i)) (inv : n j * q = 1) :
    let B := shearBasis (hIndex i) (dIndex j) (embed (-v,v)) (embed (n,-n)) (-q)
    IntegerMultBounds.Swap.Shear.LowerTriangular B ∧ IsUnit B ∧
      ∀ x s, B *ᵥ x = embed s →
        B *ᵥ OrderedAffine.execute (.shift (hIndex i) (dIndex j) (c * -(n j))) x =
          embed (portShearEquiv c n v zero s) := by
  intro B
  let u := embed (-v,v)
  let r := embed (n,-n)
  have lead (a : Fin (8+8)) (h : a < hIndex i) : u a = 0 := by
    induction a using Fin.addCases with
    | left a => simpa only [u,embed,Fin.addCases_left,Pi.neg_apply,neg_eq_zero] using
        direction a (show a.val < i.val from h)
    | right a => exact False.elim ((h_before_d i a).asymm h)
  have tail (b : Fin (8+8)) (h : dIndex j < b) : r b = 0 := by
    induction b using Fin.addCases with
    | left b => exact False.elim ((h_before_d b j).asymm h)
    | right b =>
      have lt : j < b := by change 8+j.val < 8+b.val at h; omega
      simpa only [r,embed,Fin.addCases_right,Pi.neg_apply,neg_eq_zero] using control b lt
  have orth : r ⬝ᵥ u = 0 := by
    change (∑ k : Fin (8+8), embed (n,-n) k * embed (-v,v) k) = 0
    rw [Fin.sum_univ_add]
    simp only [embed,Fin.addCases_left,Fin.addCases_right,Pi.neg_apply,mul_neg,neg_mul,Finset.sum_neg_distrib]
    change -(n ⬝ᵥ v) + -(n ⬝ᵥ v) = 0
    rw [zero,neg_zero,add_zero]
  obtain ⟨lower,unit,col,row⟩ := shearBasis_spec (q := -q) (h_before_d i j) lead tail
    (by simpa only [u,embed_h,Pi.neg_apply] using pivot.neg)
    (by simpa only [r,embed_d,Pi.neg_apply,neg_mul_neg] using inv) orth
  refine ⟨lower,unit,fun x s coord => ?_⟩
  have shift := shearBasis_shift col row c x
  change B *ᵥ _ = B *ᵥ x + (c*(r ⬝ᵥ (B *ᵥ x))) • u at shift
  rw [coord] at shift
  simpa only [r,embed_d,Pi.neg_apply] using shift.trans (embed_portShear c n v zero s).symm

open Matrix in
private theorem scale_shift {R : Type*} [CommRing R] {d : ℕ} {i j : Fin d}
    (distinct : j ≠ i) (k : R) (x : Fin d → R) :
    let D := diagonal (fun a => if a = i then k else 1)
    D *ᵥ OrderedAffine.execute (.shift i j 1) x =
      OrderedAffine.execute (.shift i j k) (D *ᵥ x) := by
  intro D
  funext a
  by_cases eq : a = i
  · subst a; simp [D,OrderedAffine.execute,mulVec_diagonal,distinct,mul_add]
  · simp [D,OrderedAffine.execute,mulVec_diagonal,Function.update_of_ne eq,eq]

open Matrix AffineFieldCoordinates IntegerMultBounds.Swap.Modular in
/-- Entry and exit at the same PR589 port use exactly the same scalar
shift between the first and last packed digits. Only the triangular basis
depends on the side. -/
theorem selectedPort_shift (w : ℕ) (t : Fin 111) (atExit : Bool) :
    let R := ZMod (prime^w)
    let v := fun i : Fin 8 => (translatedEntry t i.val : R)
    let n := fun i : Fin 8 => (targetNormal t i : R)
    let U := reduce (prime^w) (selectedProjector ⟨2+t.val,by omega⟩)
    let V := reduce (prime^w) (selectedProjector ⟨525+t.val,by omega⟩)
    let P := translatedPortProjector R (4:R)⁻¹ t
    let u := if atExit then V *ᵥ v else v
    let r := if atExit then n else n ᵥ* (1-U)
    let i := hIndex (0 : Fin 8)
    let j := dIndex (Fin.last 7)
    let B := shearBasis i j (embed (-u,u)) (embed (r,-r)) (-(n (Fin.last 7))⁻¹)
    let k := (4:R)⁻¹ * -(n (Fin.last 7))
    let D := diagonal (fun a => if a = i then k else 1)
    IntegerMultBounds.Swap.Shear.LowerTriangular (B*D) ∧ IsUnit (B*D) ∧
      ∀ x s, (B*D) *ᵥ x = embed s →
        (B*D) *ᵥ OrderedAffine.execute (.shift i j 1) x =
          embed (if atExit then M8.Exchange.exchange V (M8.Exchange.exchange (1-P) s)
            else M8.Exchange.exchange P (M8.Exchange.exchange U s)) := by
  intro R v n U V P u r i j B k D
  obtain ⟨lead,last,entry,exit⟩ := portShear_pivots w t
  have front : IsUnit (u 0) := by cases atExit <;> simp only [u,Bool.false_eq_true,ite_false,ite_true] <;>
                                     first | exact lead | exact exit.symm ▸ lead
  have back : r (Fin.last 7) = n (Fin.last 7) := by cases atExit <;> first | exact entry | rfl
  have orth : r ⬝ᵥ u = 0 := by
    cases atExit <;> first | exact (portShear_controls w t).1 | exact (portShear_controls w t).2
  obtain ⟨lower,unit,shift⟩ := portShear_shift (4:R)⁻¹ r u orth 0 (Fin.last 7) (n (Fin.last 7))⁻¹
    (by intro a h; exact False.elim (Fin.not_lt_zero a h))
    (by intro b h; exact False.elim ((Fin.le_last b).not_gt h))
    front (by rw [back]; exact ZMod.mul_inv_of_unit _ last)
  have four : IsUnit (4:R) := by simpa using prefix_denominator_unit 4 (by decide) (by decide) w
  have quarter : IsUnit (4:R)⁻¹ := isUnit_iff_exists_inv.mpr ⟨4,ZMod.inv_mul_of_unit _ four⟩
  have ku : IsUnit k := quarter.mul last.neg
  have du : IsUnit D := Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr fun a => by
    by_cases h : a = i <;> simp [h,ku])
  refine ⟨fun a b h => by simp only [D,mul_diagonal,show B a b = 0 from lower a b h,zero_mul],
    unit.mul du,fun x s hx => ?_⟩
  rw [← mulVec_mulVec] at hx ⊢
  rw [scale_shift (h_before_d (0 : Fin 8) (Fin.last 7)).ne.symm k x]
  have moved := shift (D *ᵥ x) s hx
  rw [back] at moved
  apply moved.trans
  apply congrArg embed
  cases atExit <;> first | exact ((portFrame_shears w t s).1).symm | exact ((portFrame_shears w t s).2).symm

open Matrix AffineFieldCoordinates in
/-- The port basis is polynomial in three scalars: the reciprocals of
the leading line entry, the last normal entry, and four. -/
def portBasis {R : Type*} [CommRing R] (t : Fin 111) (atExit : Bool)
    (leadInv lastInv quarter : R) : Matrix (Fin 16) (Fin 16) R :=
  let v := fun i : Fin 8 => (translatedEntry t i.val : R)
  let n := fun i : Fin 8 => (targetNormal t i : R)
  let u := if atExit then v - Pi.single (Fin.last 7) (4*lastInv) else v
  let r := if atExit then n else n - Pi.single 0 (4*leadInv)
  let i := hIndex (0 : Fin 8)
  let j := dIndex (Fin.last 7)
  shearBasis i j (embed (-u,u)) (embed (r,-r)) (-lastInv) *
    diagonal (fun a => if a = i then quarter * -(n (Fin.last 7)) else 1)

open Matrix AffineFieldCoordinates in
theorem portBasis_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (t : Fin 111) (atExit : Bool) (a b c : R) :
    (portBasis t atExit a b c).map f = portBasis t atExit (f a) (f b) (f c) := by
  have single {d : ℕ} (i j : Fin d) (x : R) :
      f ((Pi.single i x : Fin d → R) j) = (Pi.single i (f x) : Fin d → S) j := by
    by_cases eq : j = i <;> simp [eq,Pi.single_eq_of_ne]
  have fields (u v : Fin 8 → R) (i : Fin (8+8)) :
      f (embed (u,v) i) = embed (f ∘ u,f ∘ v) i := by
    induction i using Fin.addCases <;> simp only [embed,Fin.addCases_left,Fin.addCases_right,Function.comp_apply]
  ext i j
  change f ((portBasis t atExit a b c) i j) = _
  simp only [portBasis,mul_diagonal,map_mul]
  congr 1
  · simp only [shearBasis]
    split_ifs <;> cases atExit <;>
      simp only [ite_true,Bool.false_eq_true,ite_false,Pi.sub_apply,map_sub,single,map_one,map_mul,
        fields,Function.comp_def,Pi.neg_apply,map_neg,map_intCast,map_ofNat] <;> rfl
  · split_ifs <;> simp


open Matrix AffineFieldCoordinates IntegerMultBounds.Swap.Modular in
theorem portBasis_shift (w : ℕ) (t : Fin 111) (atExit : Bool) :
    let R := ZMod (prime^w)
    let B := portBasis t atExit (translatedEntry t 0 : R)⁻¹ (targetNormal t (Fin.last 7) : R)⁻¹ (4:R)⁻¹
    let U := reduce (prime^w) (selectedProjector ⟨2+t.val,by omega⟩)
    let V := reduce (prime^w) (selectedProjector ⟨525+t.val,by omega⟩)
    let P := translatedPortProjector R (4:R)⁻¹ t
    IntegerMultBounds.Swap.Shear.LowerTriangular B ∧ IsUnit B ∧
      ∀ x s, B *ᵥ x = embed s →
        B *ᵥ OrderedAffine.execute (.shift (hIndex (0 : Fin 8)) (dIndex (Fin.last 7)) 1) x =
          embed (if atExit then M8.Exchange.exchange V (M8.Exchange.exchange (1-P) s)
            else M8.Exchange.exchange P (M8.Exchange.exchange U s)) := by
  obtain ⟨row,col⟩ := portShear_vectors w t
  have action := selectedPort_shift w t atExit
  dsimp only at action row col
  rw [row,col] at action
  exact action

open IntegerMultBounds.Swap.Modular in
private theorem lift_port_inverse {m : ℕ} (z : ℤ) (unit : IsUnit (z : ZMod m)) :
    ∃ a : denCoprime m, (a : ℚ) = (z : ℚ)⁻¹ ∧ toZMod m a = (z : ZMod m)⁻¹ := by
  by_cases hz : z = 0
  · subst z; exact ⟨0,by simp,by simp [ZMod.inv_zero]⟩
  have nz : (z : ℚ) ≠ 0 := by exact_mod_cast hz
  have cop := Int.isCoprime_iff_nat_coprime.mp ((ZMod.coe_int_isUnit_iff_isCoprime _ _).mp unit)
  let a : denCoprime m := ⟨(z : ℚ)⁻¹,by
    change ((z : ℚ)⁻¹).den.Coprime m
    simpa [Rat.den_inv_of_ne_zero nz] using cop.symm⟩
  refine ⟨a,rfl,unit.mul_right_cancel ?_⟩
  have identity : a * (z : denCoprime m) = 1 := Subtype.ext (inv_mul_cancel₀ nz)
  have mapped := congrArg (toZMod m) identity
  simpa only [map_mul,map_intCast,map_one,ZMod.inv_mul_of_unit _ unit] using mapped

open IntegerMultBounds.Swap.Modular in
/-- Each port has one fixed rational basis whose reduction supplies its
triangular chart at every precision. -/
theorem rationalPortBasis_reduction (w : ℕ) (t : Fin 111) (atExit : Bool) :
    let m := prime^w
    let a := translatedEntry t 0
    let b := targetNormal t (Fin.last 7)
    let B := portBasis t atExit (a : ℚ)⁻¹ (b : ℚ)⁻¹ (4:ℚ)⁻¹
    Admissible m B ∧ reduce m B = portBasis t atExit (a : ZMod m)⁻¹ (b : ZMod m)⁻¹ (4:ZMod m)⁻¹ := by
  intro m a b B
  obtain ⟨lead,last,_,_⟩ := portShear_pivots w t
  obtain ⟨u,hu,mu⟩ := lift_port_inverse a lead
  obtain ⟨v,hv,mv⟩ := lift_port_inverse b last
  obtain ⟨q,hq,mq⟩ := lift_port_inverse (m := m) 4
    (by simpa using prefix_denominator_unit 4 (by decide) (by decide) w)
  let C := portBasis t atExit u v q
  have coeff : C.map (denCoprime m).subtype = B := by
    rw [portBasis_map]
    simp only [Subring.subtype_apply,hu,hv,hq,Int.cast_ofNat,B]
  refine ⟨fun i j => coeff ▸ (C i j).property,?_⟩
  rw [← coeff]
  change C.map (toZMod m) = _
  rw [portBasis_map,mu,mv,mq,Int.cast_ofNat]

/-- The single rational chart compiled for each side of each port. -/
def rationalPortBasis (t : Fin 111) (atExit : Bool) : Matrix (Fin 16) (Fin 16) ℚ :=
  portBasis t atExit (translatedEntry t 0 : ℚ)⁻¹ (targetNormal t (Fin.last 7) : ℚ)⁻¹ (4:ℚ)⁻¹

open M8.Height Matrix AffineFieldCoordinates in
theorem rationalPortBasis_height (t : Fin 111) (atExit : Bool) :
    Bounded (rationalPortBasis t atExit) (2^512) := by
  let v := fun i : Fin 8 => (translatedEntry t i.val : ℚ)
  let n := fun i : Fin 8 => (targetNormal t i : ℚ)
  let u := if atExit then v - Pi.single (Fin.last 7) (4*(n (Fin.last 7))⁻¹) else v
  let r := if atExit then n else n - Pi.single 0 (4*(v 0)⁻¹)
  have normal : ∀ (l : Fin 111) (i : Fin 8), (targetNormal l i).natAbs ≤ 2^100 := by decide +kernel
  have nv (i) : ht (n i) ≤ 2^100 := by simpa [n,ht] using normal t i
  have vv (i) : ht (v i) ≤ 2^100 := by
    simpa [v,ht] using (translatedEntry_bound t i).trans (show 1344 ≤ 2^100 by decide)
  have one (k : ℕ) : 1 ≤ 2^k := Nat.one_le_two_pow
  have single {k : ℕ} (i j : Fin k) (x : ℚ) {h : ℕ} (pos : 1 ≤ h) (hx : ht x ≤ h) :
      ht ((Pi.single i x : Fin k → ℚ) j) ≤ h := by
    by_cases eq : j = i <;> simp [eq,Pi.single_eq_of_ne,pos,hx]
  have four : ht 4 = 4 := by decide
  have adjust (x y : Fin 8 → ℚ) (j : Fin 8) (hx : ∀ i, ht (x i) ≤ 2^100)
      (hy : ht (y j) ≤ 2^100) (i : Fin 8) :
      ht (x i - (Pi.single j (4*(y j)⁻¹) : Fin 8 → ℚ) i) ≤ 2^203 := by
    have coeff := (ht_mul 4 (y j)⁻¹).trans (Nat.mul_le_mul (four.le) ((ht_inv _).le.trans hy))
    exact (ht_sub ..).trans ((Nat.mul_le_mul (Nat.mul_le_mul_left 2 (hx i))
      (single j i _ (by decide : 1 ≤ 4*2^100) coeff)).trans (by decide))
  have uh (i) : ht (u i) ≤ 2^203 := by
    cases atExit
    · exact (vv i).trans (by decide)
    · exact adjust v n _ vv (nv _) i
  have rh (i) : ht (r i) ≤ 2^203 := by
    cases atExit
    · exact adjust n v _ nv (vv _) i
    · exact (nv i).trans (by decide)
  have packed (x : Fin 8 → ℚ) (hx : ∀ i, ht (x i) ≤ 2^203) (a : Fin (8+8)) :
      ht (embed (-x,x) a) ≤ 2^203 ∧ ht (embed (x,-x) a) ≤ 2^203 := by
    induction a using Fin.addCases <;> simp only [embed,Fin.addCases_left,Fin.addCases_right,Pi.neg_apply,ht_neg,and_self,hx]
  intro a b
  let i := hIndex (0 : Fin 8)
  let j := dIndex (Fin.last 7)
  let q := -(n (Fin.last 7))⁻¹
  let k := (4:ℚ)⁻¹ * -(n (Fin.last 7))
  change ht ((shearBasis i j (embed (-u,u)) (embed (r,-r)) q * diagonal (fun a => if a=i then k else 1)) a b) ≤ _
  rw [mul_diagonal]
  apply (ht_mul ..).trans
  have kh : ht (if b=i then k else 1) ≤ 4*2^100 := by
    split
    · exact (ht_mul ..).trans (Nat.mul_le_mul (by simp [four]) (by simpa using nv (Fin.last 7)))
    · simp
  suffices h : ht (shearBasis i j (embed (-u,u)) (embed (r,-r)) q a b) ≤ 2^305 from
    (Nat.mul_le_mul h kh).trans (by decide)
  unfold shearBasis
  split
  · exact (packed u uh a).1.trans (by decide)
  split
  · exact single j a 1 (one _) (ht_one.le.trans (one _))
  · have prod := (ht_mul q (embed (r,-r) b)).trans (Nat.mul_le_mul
        (show ht q ≤ 2^100 by simpa [q] using nv (Fin.last 7)) (packed r rh b).2)
    exact (ht_sub ..).trans ((Nat.mul_le_mul (Nat.mul_le_mul_left 2 (single b a 1 le_rfl ht_one.le))
      (single j a _ (by decide : 1 ≤ 2^100*2^203) prod)).trans (by decide))

open Matrix IntegerMultBounds.Swap.Modular in
private theorem flatMatrix_owner (word : List (PortInverse.Op 16))
    (support : ∀ op ∈ word, FlatCoordinateSchedule.Supported op)
    (matrix : ∀ w : ℕ, Matrix (Fin 16) (Fin 16) (ZMod (prime^w)))
    (unit : ∀ w, IsUnit (matrix w))
    (action : ∀ w x, OrderedAffine.run (word.map (OrderedAffine.mapOp (ratMod (prime^w)))) x = matrix w *ᵥ x) :
    ∃ (C : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w W, 0 < W →
      let V := (prime^w)^16*W
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧ stage.cost = C*V ∧ ∀ x a j,
          stage.transform x (FlatCoordinateLayout.index (matrix w *ᵥ a) j) =
            x (FlatCoordinateLayout.index a j) := by
  let ops := FlatCoordinateSchedule.ofList word support
  let machine : SharedBankSkeleton.Skeleton 1 prime :=
    ⟨_,_,FlatCoordinateCleanSchedule.program ops,fun _ => segmentSource ops,fun _ _ _ => Subsingleton.elim _ _⟩
  refine ⟨FlatCoordinateCleanSchedule.constant ops,machine,?_⟩
  intro w W hW V
  let M := matrix w
  let addr := (FlatCoordinateLayout.rankEquiv (Q := prime^w) (d := 16)).prodCongr (Equiv.refl (Fin W))
  let pack := addr.trans finProdFinEquiv
  let out := fun (x : Fin V → ZMod 2) i => x (pack ((M⁻¹ *ᵥ (pack.symm i).1),(pack.symm i).2))
  have move (x a j) : out x (pack (M *ᵥ a,j)) = x (pack (a,j)) := by
    have inv : M⁻¹ * M = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp (unit w))
    simp only [out,Equiv.symm_apply_apply,mulVec_mulVec,inv,one_mulVec]
  have actions : ops.map (fun op => op.action w) = word.map (OrderedAffine.mapOp (ratMod (prime^w))) := by
    change ops.map ((OrderedAffine.mapOp (ratMod (prime^w))) ∘ FlatCoordinateSchedule.Op.rational) = _
    rw [← List.map_map,FlatCoordinateSchedule.rational_ofList _]
  let bank := fun (x : Fin V → ZMod 2) => SharedBankStageInput.raw
    (FlatCoordinateShiftSharedBank.common (d := 16) (b := w) (W := W)
      (fun i => SparseRoleCircuit.encode (x i))) (FlatCoordinateCleanSchedule.tapeCount ops)
  have exec (x : Fin V → ZMod 2) : HoareTime machine.program (fun z => z = bank x)
      (fun z => z = bank (out x)) (FlatCoordinateCleanSchedule.constant ops*V) := by
    let bits : FlatCoordinateStages.Array 16 w W := fun i => SparseRoleCircuit.encode (a := 0) (x i)
    have output : FlatCoordinateInitializedSchedule.array ops w W hW bits =
        fun i => SparseRoleCircuit.encode (out x i) := by
      funext i
      obtain ⟨⟨a,j⟩,rfl⟩ := pack.surjective i
      obtain ⟨a,rfl⟩ := (mulVec_surjective_iff_isUnit.mpr (unit w)) a
      rw [move]
      have read := FlatCoordinateInitializedSchedule.array_entry ops w W hW bits a j
      rw [actions] at read
      exact (congrArg (fun z => FlatCoordinateInitializedSchedule.array ops w W hW bits (FlatCoordinateLayout.index (Q := prime^w) z j)) (action w a)).symm.trans read
    apply (FlatCoordinateCleanSchedule.realizes ops w W hW bits).consequence (fun _ h => h) _ le_rfl
    intro z h
    exact h.1.trans (congrArg (fun a => SharedBankStageInput.raw
      (FlatCoordinateShiftSharedBank.common a) (FlatCoordinateCleanSchedule.tapeCount ops)) output)
  let slot := fun _ : Fin 1 => segmentSource ops
  have payload (x) : SharedBank.payload (bank x) slot = portOwner x := by
    obtain ⟨head,tape⟩ := copySegment_source ops x
    exact congrArg₂ Tapes.mk (funext fun _ => head) (funext fun _ => tape.trans (sourceWord_cast _ x))
  have strip (x) : SharedBank.strip (bank x) slot = basisWorkspace ops x := by
    apply congrArg₂ Tapes.mk <;> funext j <;> by_cases eq : segmentSource ops = j
    all_goals first
      | subst j; simp [SharedBank.strip,slot,basisWorkspace,SharedPlacementAlphabet.setTape]
      | simp [SharedBank.strip,slot,eq,basisWorkspace,SharedPlacementAlphabet.setTape,Function.update_of_ne (Ne.symm eq),bank]
  exact ⟨{ tapes := _, states := _, program := machine.program, transform := out, input := bank,
           output := fun x => bank (out x),slots := slot,slots_injective := fun _ _ _ => Subsingleton.elim _ _,
           cost := FlatCoordinateCleanSchedule.constant ops*V,metadata := basisWorkspace ops (0 : Fin V → ZMod 2),
           input_payload := payload,output_payload := fun x => payload _,realizes := exec,
           strip_input := fun x => (strip x).trans (basisWorkspace_eq ops x 0) },rfl,rfl,move⟩

open Matrix IntegerMultBounds.Swap.Modular in
private theorem triangularPort_owner (E : Matrix (Fin 16) (Fin 16) ℚ)
    (bounded : ∀ op ∈ OrderedAffine.program E, PortInverse.bounded op)
    (valid : ∀ w, let M := reduce (prime^w) E
      IntegerMultBounds.Swap.Shear.LowerTriangular M ∧ IsUnit M) (inverse : Bool) :
    ∃ (C : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w W, 0 < W →
      let V := (prime^w)^16*W
      let M := reduce (prime^w) E
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧ stage.cost = C*V ∧ ∀ x a j,
          stage.transform x (FlatCoordinateLayout.index ((if inverse then M⁻¹ else M) *ᵥ a) j) =
            x (FlatCoordinateLayout.index a j) := by
  let ops := OrderedAffine.program E
  have forward (w : ℕ) (x) : OrderedAffine.run (ops.map (OrderedAffine.mapOp (ratMod (prime^w)))) x =
      reduce (prime^w) E *ᵥ x := by
    rw [show ops.map _ = OrderedAffine.program (reduce (prime^w) E) from (OrderedAffine.program_map _ E).symm]
    exact OrderedAffine.program_run (valid w).1 x
  cases inverse with
  | false => exact flatMatrix_owner ops (fun op h => PortInverse.supported (bounded op h)) _ (fun w => (valid w).2) forward
  | true =>
    refine flatMatrix_owner (ops.reverse.map PortInverse.undo) ?_ (fun w => (reduce (prime^w) E)⁻¹) ?_ ?_
    · intro op h
      obtain ⟨o,ho,rfl⟩ := List.mem_map.mp h
      exact PortInverse.supported (PortInverse.undo_bounded (bounded o (List.mem_reverse.mp ho)))
    · intro w
      exact isUnit_nonsing_inv_iff.mpr (valid w).2
    · intro w x
      let M := reduce (prime^w) E
      have right : M*M⁻¹ = 1 := mul_nonsing_inv M ((isUnit_iff_isUnit_det M).mp (valid w).2)
      have cancel : M *ᵥ (M⁻¹ *ᵥ x) = x := by rw [mulVec_mulVec,right,one_mulVec]
      have back := PortInverse.run_undo w ops bounded (M⁻¹ *ᵥ x)
      dsimp only at back
      rw [forward w] at back
      exact (congrArg (OrderedAffine.run _) cancel.symm).trans back

open Matrix M8.Height IntegerMultBounds.Swap.Modular in
/-- A fixed tape program executes the surrounding rational basis in time
linear in the payload volume, uniformly in the radix precision. -/
theorem rationalPortBasis_owner (t : Fin 111) (atExit inverse : Bool) :
    ∃ (c : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w W, 0 < W →
      let V := (prime^w)^16*W
      let B := reduce (prime^w) (rationalPortBasis t atExit)
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧ stage.cost = c*V ∧ ∀ x a j,
          stage.transform x (FlatCoordinateLayout.index ((if inverse then B⁻¹ else B) *ᵥ a) j) = x (FlatCoordinateLayout.index a j) := by
  let E := rationalPortBasis t atExit
  have valid (w : ℕ) : IntegerMultBounds.Swap.Shear.LowerTriangular (reduce (prime^w) E) ∧
      IsUnit (reduce (prime^w) E) := by
    dsimp only [E,rationalPortBasis]
    rw [(rationalPortBasis_reduction w t atExit).2]
    exact ⟨(portBasis_shift w t atExit).1,(portBasis_shift w t atExit).2.1⟩
  apply triangularPort_owner E _ valid inverse
  intro op hop
  have bound (i j) : ht (E i j) ≤ coefficientBound := by
    exact (rationalPortBasis_height t atExit i j).trans
      (M8.Exchange.le_coefficientBound (show 512 ≤ 2^53000 from
        (show 512 ≤ 2^9 by decide).trans (Nat.pow_le_pow_right (by decide) (by decide))))
  rcases OrderedAffine.coefficient_origin E op hop with ⟨i,rfl⟩ | ⟨i,j,lt,rfl⟩
  · refine ⟨?_,bound i i⟩
    have modPrime : IntegerMultBounds.Swap.Shear.LowerTriangular (reduce prime E) ∧
        IsUnit (reduce prime E) := by
      let holds (m : ℕ) := IntegerMultBounds.Swap.Shear.LowerTriangular (reduce m E) ∧ IsUnit (reduce m E)
      exact (congrArg holds (pow_one prime)).mp (valid 1)
    letI : Fact prime.Prime := ⟨Shared50ModularControl.prime_prime⟩
    have nz := (OrderedAffine.diagonal_unit modPrime.1 modPrime.2 i).ne_zero
    intro eq
    exact nz (by change ratMod prime (E i i) = 0; rw [eq,ratMod_zero])
  · exact ⟨lt,bound i j⟩

open Cover RecursiveInterchangeLayout M8.RevMachine SharedPlacementAlphabet in
/-- A packed digit swap on the same source tape used by the basis passes. -/
theorem digitSwap_view_owner_cost [M8.Machine.Net] (i j : Fin 16) (lt : i < j)
    (price : ℕ → ℕ → ℕ) (paid : ∀ w W, 0 < w → 0 < W →
      let u := swapView prime w W i j
      M8.Machine.ArbitraryWidthOriginalTotalRun.cost u (Routines.hdr u) ≤ price w W) :
    ∃ machine : SharedBankSkeleton.Skeleton 1 prime, ∀ w W, 0 < w → 0 < W →
    let V := (prime^w)^16*W
    ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
      SharedBankSkeleton.ofStage stage = machine ∧ stage.cost = 3808274*V + price w W ∧
      (∃ S : Stacks stage.tapes prime, RepT (stage.input 0) S.L S.R) ∧
      ∀ x, LabelView.Swapped prime (swapView prime w W i j) (ext x) (ext (stage.transform x)) := by
  let io : Fin 1 := 0
  let block := LabelSwap.program io
  let slots := fun k : Fin 1 => block.slots (Fin.castAdd 24 k)
  refine ⟨⟨_,_,block.program,slots,fun _ _ _ => Subsingleton.elim _ _⟩,?_⟩
  intro w W hw hW V
  let v := payloadView prime 16 w W
  have size : volume prime v = V := by simp [v,payloadView,volume,V,← pow_mul,Nat.mul_comm]
  have leading : Blocks.Leading block := Blocks.seq_leading _ _
  let d := LabelPrepare.input v 16 i.val j.val w
  let bank := fun (x : Fin V → ZMod 2) => SharedBankStageInput.raw (LabelCall.bank (portOwner x) v d) block.tapes
  have hv : v.beforeH = 1*prime^(16*w) := by simp [v,payloadView]
  have hp : v.Positive := by simp [v,payloadView,Descriptor.Positive,hW,Shared50ModularControl.prime_prime.pos]
  have view : LabelView.colView prime w 16 i.val j.val 1 v = swapView prime w W i j := by
    simp [LabelView.colView,swapView,v,payloadView,FlatCoordinateLayout.suffixFields,
      ← pow_mul,Nat.mul_comm,Nat.sub_sub,Nat.add_comm]
  let result := fun x : Fin V → ZMod 2 => LabelSwap.runs_at_view_cost lt j.isLt hw (by decide : 0 < 1) hv hp
    (portOwner x) io (fun t => x (Fin.cast size t)) rfl (sourceWord_cast size x).symm
  let out := fun x t => (result x).choose (Fin.cast size.symm t)
  have word (x) : M8.Machine.ArbitraryWidthHighExchangeShared.sourceWord (v := v) (result x).choose =
      (portOwner (out x)).tape io := by
    exact sourceWord_cast size (out x)
  have same (x) : setTape (portOwner x) io ((portOwner (out x)).tape io) 0 = portOwner (out x) := by
    apply congrArg₂ Tapes.mk <;> funext k <;> obtain rfl : k = io := Subsingleton.elim _ _ <;> simp [portOwner]
  refine ⟨{
    tapes := _, states := _, program := block.program, transform := out, input := bank,
    output := fun x => bank (out x), slots := slots, slots_injective := fun _ _ _ => Subsingleton.elim _ _,
    metadata := SharedBank.strip (bank 0) slots, cost := 3808274*V + price w W,
    input_payload := fun x => copyRoute_payload block leading _ v d,
    output_payload := fun x => copyRoute_payload block leading _ v d,
    strip_input := fun x => routePrivate block leading _ _ v d, realizes := ?_ },rfl,rfl,?_,?_⟩
  · intro x
    have run := (result x).choose_spec.2
    change GraphContract.Runs block _ (LabelCall.bank (setTape _ io _ 0) v d) _ at run
    rw [word,same,size,view] at run
    exact Blocks.runs_mono run (Nat.add_le_add_left (paid w W hw hW) _)
  · let payload := List.ofFn fun _ : Fin V => SparseRoleCircuit.encode (a := prime) (0 : ZMod 2)
    let owners : Stacks 1 prime := ⟨[],[],fun _ => [],fun _ => payload⟩
    apply swap_bank_seed (by simpa using Fintype.card_le_of_injective block.slots block.slots_injective)
      (portOwner 0) v d owners
    intro i z
    simp [portOwner,owners,payload,readAt_nil_left,putWord_blank_zero]
  · intro x
    have swap := (result x).choose_spec.1
    let y := (result x).choose
    change LabelView.Swapped prime _ (ext (fun t => x (Fin.cast size t))) (ext y) at swap
    change LabelView.Swapped prime _ (ext x) (ext (fun t => y (Fin.cast size.symm t)))
    rw [ext_cast]
    exact (congrArg (fun u => LabelView.Swapped prime u (ext x) (ext y)) view).mp
      (by simpa only [ext_cast] using swap)

open Cover RecursiveInterchangeLayout M8.RevMachine in
theorem digitSwap_view_owner [M8.Machine.Net] (i j : Fin 16) (lt : i < j) :
    ∃ machine : SharedBankSkeleton.Skeleton 1 prime, ∀ w W, 0 < w → 0 < W →
    let V := (prime^w)^16*W
    ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
      SharedBankSkeleton.ofStage stage = machine ∧ stage.cost = 3808274*V + LeafCore.coreCost V w ∧
      ∀ x, LabelView.Swapped prime (swapView prime w W i j) (ext x) (ext (stage.transform x)) := by
  obtain ⟨machine,build⟩ := digitSwap_view_owner_cost i j lt (fun w W => LeafCore.coreCost ((prime^w)^16*W) w) (by
    intro w W hw hW u
    have size : volume prime u = (prime^w)^16*W := swapView_volume i j lt
    have positive : u.Positive := LeafCore.positive_of_volume
      (size ▸ Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW)
    simpa only [size,show u.width = w from rfl] using LeafCore.cost_le positive)
  refine ⟨machine,?_⟩
  intro w W hw hW
  obtain ⟨stage,fixed,price,_,swap⟩ := build w W hw hW
  exact ⟨stage,fixed,price,swap⟩

open Cover RecursiveInterchangeLayout M8.RevMachine in
theorem digitSwap_owner [M8.Machine.Net] (i j : Fin 16) (lt : i < j) :
    ∃ machine : SharedBankSkeleton.Skeleton 1 prime, ∀ w W, 0 < w → 0 < W →
    let V := (prime^w)^16*W
    ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
      SharedBankSkeleton.ofStage stage = machine ∧ stage.cost = 3808274*V + LeafCore.coreCost V w ∧
      ∀ x coords k, stage.transform x (FlatCoordinateLayout.index (coords ∘ Equiv.swap i j) k) =
        x (FlatCoordinateLayout.index coords k) := by
  obtain ⟨machine,runs⟩ := digitSwap_view_owner i j lt
  refine ⟨machine,?_⟩
  intro w W hw hW V
  obtain ⟨stage,fixed,cost,swap⟩ := runs w W hw hW
  exact ⟨stage,fixed,cost,fun x coords k => by
    simpa only [ext_apply] using swapView_apply i j lt (swap x) coords k⟩

open AffineFieldCoordinates M8.RevMachine in
/-- The backward digit addition uses one interchange. Adding into the
last digit before the swap preserves the sum, and subtracting after it
restores the last digit. -/
theorem backwardDigit_owner [M8.Machine.Net] :
    ∃ (c : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^16*W
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧ stage.cost = c*V + LeafCore.coreCost V w + 2 ∧
        ∀ x coords j, stage.transform x (FlatCoordinateLayout.index
          (OrderedAffine.execute (.shift (hIndex (0 : Fin 8)) (dIndex (Fin.last 7)) 1) coords) j) =
          x (FlatCoordinateLayout.index coords j) := by
  obtain ⟨a,add,adds⟩ := forwardDigit_owner false
  obtain ⟨b,sub,subs⟩ := forwardDigit_owner true
  obtain ⟨swap,swaps⟩ := digitSwap_owner 0 15 (by decide)
  refine ⟨a+b+3808274,SharedBankSkeleton.compose (SharedBankSkeleton.compose add swap) sub,?_⟩
  intro w W hw hW V
  obtain ⟨A,fa,ca,ar⟩ := adds w W hW
  obtain ⟨S,fs,cs,sr⟩ := swaps w W hw hW
  obtain ⟨B,fb,cb,br⟩ := subs w W hW
  refine ⟨SharedBankStage.compose (SharedBankStage.compose A S) B,?_,?_,?_⟩
  · simp only [SharedBankSkeleton.ofStage_compose,fa,fs,fb]
  · change A.cost+S.cost+1+B.cost+1 = _
    rw [ca,cs,cb]
    ring
  · intro x coords j
    let s : IntegerMultBounds.Swap.Shear.State (Fin 8) (ZMod (prime^w)) := (coords ∘ hIndex,coords ∘ dIndex)
    have packed : embed s = coords := by
      funext i
      induction i using Fin.addCases (m := 8) (n := 8) with
      | left i => exact embed_h s i
      | right i => exact embed_d s i
    rw [← packed]
    let y := AffineFieldProgram.execute (.addToD 0 7) s
    let z := AffineFieldProgram.execute (.interchange 0 7) y
    have exchanged : embed z = embed y ∘ Equiv.swap 0 15 := by
      funext i
      fin_cases i <;> rfl
    have finish : OrderedAffine.execute (.shift (hIndex (0 : Fin 8)) (dIndex (Fin.last 7)) 1) (embed s) =
        embed (AffineFieldProgram.execute (.subFromD 0 7) z) := by
      funext i
      fin_cases i <;> first | rfl
                            | (change s.1 0 + 1 * s.2 7 = s.2 7 + s.1 0; rw [one_mul,add_comm])
                            | (change s.2 7 = s.2 7 + s.1 0 - s.1 0; rw [add_sub_cancel_right])
    change B.transform (S.transform (A.transform x)) _ = _
    rw [finish]
    apply (br (S.transform (A.transform x)) z j).trans
    rw [exchanged]
    exact (sr (A.transform x) (embed y) j).trans (ar x s j)

open Matrix IntegerMultBounds.Swap.Modular in
private theorem negateDigit_owner (i : Fin 16) :
    ∃ (c : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w W, 0 < W →
      let V := (prime^w)^16*W
      let D : Matrix (Fin 16) (Fin 16) (ZMod (prime^w)) := diagonal (fun a => if a=i then -1 else 1)
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧ stage.cost = c*V ∧ ∀ x a j,
          stage.transform x (FlatCoordinateLayout.index (D *ᵥ a) j) = x (FlatCoordinateLayout.index a j) := by
  apply flatMatrix_owner [.scale i (-1)] _ (fun w => diagonal (fun a => if a=i then (-1 : ZMod (prime^w)) else 1))
  · intro w
    apply Matrix.isUnit_diagonal.mpr
    exact Pi.isUnit_iff.mpr fun a => by split <;> simp
  · intro w x
    funext a
    by_cases eq : a=i <;>
      simp [OrderedAffine.run,OrderedAffine.execute,OrderedAffine.mapOp,mulVec_diagonal,eq,
        M8.AtomSegment.ratMod_neg_one,Function.update_apply]
  · intro op mem
    obtain rfl := List.mem_singleton.mp mem
    have one : 1 ≤ coefficientBound := Nat.one_le_two_pow
    exact Or.inr ⟨by decide,by simpa using one,by simpa using one⟩

open Matrix AffineFieldCoordinates M8.RevMachine in
/-- The inverse read uses the same digit addition between two first-digit
negations. Both negations are linear-volume scans. -/
theorem backwardDigit_inverse_owner [M8.Machine.Net] :
    ∃ (c : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^16*W
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧ stage.cost = c*V + LeafCore.coreCost V w + 4 ∧
        ∀ x coords j, stage.transform x (FlatCoordinateLayout.index coords j) = x (FlatCoordinateLayout.index
          (OrderedAffine.execute (.shift (hIndex (0 : Fin 8)) (dIndex (Fin.last 7)) 1) coords) j) := by
  let i := hIndex (0 : Fin 8)
  let k := dIndex (Fin.last 7)
  obtain ⟨a,neg,negates⟩ := negateDigit_owner i
  obtain ⟨b,shift,shifts⟩ := backwardDigit_owner
  refine ⟨a+b+a,SharedBankSkeleton.compose (SharedBankSkeleton.compose neg shift) neg,?_⟩
  intro w W hw hW V
  obtain ⟨A,fa,ca,ar⟩ := negates w W hW
  obtain ⟨S,fs,cs,sr⟩ := shifts w W hw hW
  refine ⟨SharedBankStage.compose (SharedBankStage.compose A S) A,?_,?_,?_⟩
  · simp only [SharedBankSkeleton.ofStage_compose,fa,fs]
  · change A.cost+S.cost+1+A.cost+1 = _
    rw [ca,cs]
    ring
  · intro x coords j
    let D : Matrix (Fin 16) (Fin 16) (ZMod (prime^w)) := diagonal (fun a => if a=i then -1 else 1)
    let add := OrderedAffine.execute (.shift i k (1 : ZMod (prime^w)))
    have restore : D *ᵥ add (D *ᵥ add coords) = coords := by
      funext l
      by_cases eq : l=i
      · subst l
        simp [D,add,OrderedAffine.execute,mulVec_diagonal,Function.update_apply,show k ≠ i by decide]
      · simp [D,add,OrderedAffine.execute,mulVec_diagonal,Function.update_apply,eq]
    change A.transform (S.transform (A.transform x)) _ = _
    calc
      _ = A.transform (S.transform (A.transform x)) (FlatCoordinateLayout.index (D *ᵥ add (D *ᵥ add coords)) j) :=
        congrArg (fun v => A.transform (S.transform (A.transform x)) (FlatCoordinateLayout.index v j)) restore.symm
      _ = _ := (ar _ _ j).trans ((sr _ _ j).trans (ar _ _ j))

open Matrix AffineFieldCoordinates IntegerMultBounds.Swap.Modular M8.RevMachine in
/-- The complete physical port correction has one charged interchange
between two linear-volume passes. Its program is fixed across widths. -/
theorem portCorrection_owner [M8.Machine.Net] (t : Fin 111) (atExit : Bool) (inverse : Bool := false) :
    ∃ (c : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^16*W
      let P := translatedPortProjector (ZMod (prime^w)) (4:ZMod (prime^w))⁻¹ t
      let U := reduce (prime^w) (selectedProjector ⟨2+t.val,by omega⟩)
      let T := reduce (prime^w) (selectedProjector ⟨525+t.val,by omega⟩)
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧ stage.cost = c*V + LeafCore.coreCost V w + (if inverse then 6 else 4) ∧
        ∀ x s j, let moved := if atExit then M8.Exchange.exchange T (M8.Exchange.exchange (1-P) s)
          else M8.Exchange.exchange P (M8.Exchange.exchange U s)
          stage.transform x (FlatCoordinateLayout.index (embed (if inverse then s else moved)) j) =
            x (FlatCoordinateLayout.index (embed (if inverse then moved else s)) j) := by
  obtain ⟨a,toChart,before⟩ := rationalPortBasis_owner t atExit true
  have digit : ∃ (b : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^16*W
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧ stage.cost = b*V + LeafCore.coreCost V w + (if inverse then 4 else 2) ∧
        ∀ x coords j, let moved := OrderedAffine.execute (.shift (hIndex (0 : Fin 8)) (dIndex (Fin.last 7)) 1) coords
          stage.transform x (FlatCoordinateLayout.index (if inverse then coords else moved) j) =
            x (FlatCoordinateLayout.index (if inverse then moved else coords) j) := by
    cases inverse
    · exact backwardDigit_owner
    · exact backwardDigit_inverse_owner
  obtain ⟨b,shift,middle⟩ := digit
  obtain ⟨c,fromChart,after⟩ := rationalPortBasis_owner t atExit false
  refine ⟨a+b+c,SharedBankSkeleton.compose (SharedBankSkeleton.compose toChart shift) fromChart,?_⟩
  intro w W hw hW V P U T
  obtain ⟨A,fa,ca,ar⟩ := before w W hW
  obtain ⟨S,fs,cs,sr⟩ := middle w W hw hW
  obtain ⟨D,fd,cd,dr⟩ := after w W hW
  refine ⟨SharedBankStage.compose (SharedBankStage.compose A S) D,?_,?_,?_⟩
  · simp only [SharedBankSkeleton.ofStage_compose,fa,fs,fd]
  · change A.cost+S.cost+1+D.cost+1 = _
    rw [ca,cs,cd]
    cases inverse <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> ring
  · intro x s j moved
    let B := reduce (prime^w) (rationalPortBasis t atExit)
    have red : B = _ := (rationalPortBasis_reduction w t atExit).2
    obtain ⟨_,unit,correct⟩ := portBasis_shift w t atExit
    rw [← red] at unit correct
    let coords := B⁻¹ *ᵥ embed s
    have enter : B *ᵥ coords = embed s := by
      rw [show B *ᵥ coords = (B*B⁻¹) *ᵥ embed s from mulVec_mulVec ..,
        mul_nonsing_inv B ((isUnit_iff_isUnit_det B).mp unit),one_mulVec]
    let step := OrderedAffine.execute (.shift (hIndex (0 : Fin 8)) (dIndex (Fin.last 7)) (1 : ZMod (prime^w))) coords
    have leave : B *ᵥ step = embed moved := correct coords s enter
    have back : B⁻¹ *ᵥ embed moved = step := by
      rw [← leave,mulVec_mulVec,nonsing_inv_mul B ((isUnit_iff_isUnit_det B).mp unit),one_mulVec]
    change D.transform (S.transform (A.transform x)) _ = _
    cases inverse with
    | false =>
      change D.transform (S.transform (A.transform x)) (FlatCoordinateLayout.index (embed moved) j) = _
      rw [← leave]
      exact (dr _ _ j).trans ((sr _ coords j).trans (ar x (embed s) j))
    | true =>
      change D.transform (S.transform (A.transform x)) (FlatCoordinateLayout.index (embed s) j) = _
      rw [← enter]
      apply (dr _ coords j).trans
      apply (sr _ coords j).trans
      have read := ar x (embed moved) j
      change A.transform x (FlatCoordinateLayout.index (B⁻¹ *ᵥ embed moved) j) = _ at read
      rwa [back] at read

/-- Install a one-tape port pass on one permanent owner. All remaining
owner tapes form a stationary frame throughout the run. -/
noncomputable def placePort {k V : ℕ} (dst : Fin (k+1))
    (s : SharedBankStage.Stage _ 1 prime (@portOwner V)) :
    SharedBankStage.Stage _ (k+1) prime (phaseOwners (N := V)) := by
  let slot : Fin (k+1) → Fin (s.tapes+k) :=
    dst.succAboveCases (Fin.castAdd k (s.slots 0)) (Fin.natAdd s.tapes)
  let frame := fun data : Fin (k+1) → Fin V → ZMod 2 => phaseOwners (data ∘ dst.succAbove)
  let moved := fun data : Fin (k+1) → Fin V → ZMod 2 => Function.update data dst (s.transform (data dst))
  have payload (data : Fin (k+1) → Fin V → ZMod 2) (v : Tapes s.tapes prime) (x : Fin V → ZMod 2)
      (hv : SharedBank.payload v s.slots = portOwner x) :
      SharedBank.payload (v.append (frame data)) slot = phaseOwners (Function.update data dst x) := by
    have head := congrArg (fun z : Tapes 1 prime => z.head 0) hv
    have tape := congrArg (fun z : Tapes 1 prime => z.tape 0) hv
    apply congrArg₂ Tapes.mk <;> funext j <;> induction j using Fin.succAboveCases dst
    all_goals first
      | simpa [slot,SharedBank.payload,phaseOwners,portOwner,Tapes.append] using head
      | simpa [slot,SharedBank.payload,phaseOwners,portOwner,Tapes.append] using tape
      | simp [slot,SharedBank.payload,phaseOwners,frame,Tapes.append,Function.update_of_ne]
  have sep (a : Fin s.tapes) (b : Fin k) : Fin.castAdd k a ≠ Fin.natAdd s.tapes b := by
    intro h
    have val := congrArg Fin.val h
    simp only [Fin.val_castAdd,Fin.val_natAdd] at val
    omega
  refine {
    tapes := s.tapes+k, states := s.states, program := extend s.program k, transform := moved,
    input := fun data => (s.input (data dst)).append (frame data),
    output := fun data => (s.output (data dst)).append (frame data), slots := slot,
    slots_injective := ?_, metadata := s.metadata.append (SharedBank.empty k prime), cost := s.cost,
    input_payload := fun data => by simpa using payload data _ _ (s.input_payload (data dst)),
    output_payload := fun data => payload data _ _ (s.output_payload (data dst)),
    strip_input := ?_, realizes := ?_ }
  · intro a b h
    induction a using Fin.succAboveCases dst <;> induction b using Fin.succAboveCases dst <;>
      simpa [slot,sep,Ne.symm (sep _ _)] using h
  · intro data
    rw [← s.strip_input (data dst)]
    have left (i : Fin s.tapes) : (∃ j, slot j = Fin.castAdd k i) ↔ ∃ j, s.slots j = i := by
      constructor
      · rintro ⟨j,h⟩
        induction j using Fin.succAboveCases dst
        · exact ⟨0,by simpa [slot,sep,Ne.symm (sep _ _)] using h⟩
        · simp [slot,Ne.symm (sep _ _)] at h
      · rintro ⟨j,h⟩
        obtain rfl : j = 0 := Subsingleton.elim _ _
        exact ⟨dst,by simp [slot,h]⟩
    have right (i : Fin k) : ∃ j, slot j = Fin.natAdd s.tapes i := ⟨dst.succAbove i,by simp [slot]⟩
    apply congrArg₂ Tapes.mk <;> funext j <;> induction j using Fin.addCases <;>
      simp [SharedBank.strip,Tapes.append,left,right,SharedBank.empty]
  · intro data
    apply ((s.realizes (data dst)).extend (frame data)).consequence _ _ le_rfl
    · rintro v rfl; exact ⟨_,rfl,rfl⟩
    · rintro v ⟨_,rfl,rfl⟩; rfl

/-- Packed action of the two digit transpositions, one per field. -/
def portSwapDigits {R : Type*} (x : Fin 16 → R) : Fin 16 → R :=
  x ∘ Equiv.swap 0 7 ∘ Equiv.swap 8 15

open Matrix in
theorem portSwapDigits_embed {R : Type*} [CommRing R] (s : IntegerMultBounds.Swap.Shear.State (Fin 8) R) :
    portSwapDigits (AffineFieldCoordinates.embed s) =
      AffineFieldCoordinates.embed (M8.Exchange.transform (portPivotSwap R) (portPivotSwap R) s) := by
  have swap (x : Fin 8 → R) : portPivotSwap R *ᵥ x = x ∘ Equiv.swap 0 (Fin.last 7) := by
    funext i
    simp [portPivotSwap,mulVec,dotProduct,ite_mul]
  rw [M8.Exchange.transform,swap,swap]
  funext i
  fin_cases i <;> rfl

open IntegerMultBounds.Swap.Modular M8.RevMachine in
/-- Run all four factors of a port chart on one permanent payload tape,
including both physical digit swaps and all three program joins. -/
theorem portChart_owner [M8.Machine.Net] (k l : Fin 636) :
    ∃ (c : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^16*W
      let T := reduce (prime^w) (frameBasis l false) * portPivotSwap (ZMod (prime^w)) *
        reduce (prime^w) (frameBasis k true)
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧ stage.cost = c*V + 2*LeafCore.coreCost V w + 3 ∧
        ∀ x s j, stage.transform x (FlatCoordinateLayout.index
          (AffineFieldCoordinates.embed (M8.Exchange.transform T T s)) j) =
          x (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j) := by
  obtain ⟨a,first,before⟩ := frameBasis_owner k true
  obtain ⟨b,last,after⟩ := frameBasis_owner l false
  obtain ⟨hi,hswap⟩ := digitSwap_owner (0 : Fin 16) 7 (by decide)
  obtain ⟨di,dswap⟩ := digitSwap_owner (8 : Fin 16) 15 (by decide)
  let machine := SharedBankSkeleton.compose (SharedBankSkeleton.compose (SharedBankSkeleton.compose first hi) di) last
  refine ⟨a+b+2*3808274,machine,?_⟩
  intro w W hw hW V T
  obtain ⟨A,fa,ac,ar⟩ := before w W hW
  obtain ⟨B,fb,bc,br⟩ := after w W hW
  obtain ⟨H,fh,hc,hr⟩ := hswap w W hw hW
  obtain ⟨D,fd,dc,dr⟩ := dswap w W hw hW
  refine ⟨SharedBankStage.compose (SharedBankStage.compose (SharedBankStage.compose A H) D) B,?_,?_,?_⟩
  · simp only [SharedBankSkeleton.ofStage_compose,fa,fb,fh,fd,machine]
  · change A.cost+H.cost+1+D.cost+1+B.cost+1 = _
    rw [ac,bc,hc,dc]
    dsimp only [V]
    ring
  · intro x s j
    let C := reduce (prime^w) (frameBasis l false)
    let E := reduce (prime^w) (frameBasis k true)
    let J := portPivotSwap (ZMod (prime^w))
    let y := M8.Exchange.transform E E s
    have factor : M8.Exchange.transform T T s =
        M8.Exchange.transform C C (M8.Exchange.transform J J y) := by
      simp only [M8.Exchange.transform,T,C,E,J,y,Matrix.mulVec_mulVec,Matrix.mul_assoc]
    change B.transform (D.transform (H.transform (A.transform x))) _ = _
    rw [factor,br,← portSwapDigits_embed]
    unfold portSwapDigits
    rw [show AffineFieldCoordinates.embed y ∘ Equiv.swap 0 7 ∘ Equiv.swap 8 15 =
      (AffineFieldCoordinates.embed y ∘ Equiv.swap 0 7) ∘ Equiv.swap 8 15 from rfl,dr,hr]
    exact ar x s j

local notation "N" => rowSwapBlock.tapes+35

/-- Swap digits zero and seven on both fields in the shared column bank.
Both calls restore their private workspace and the saved pivot stream. -/
theorem portPivotSwap_exec [M8.Machine.Net] {P U : Type} {w W : ℕ} (H J : ℕ)
    (hm : prime^(w+1) < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P (N+1) columnCapacity prime U) (v : HS (N+1) columnCapacity prime U)
    (S : Stacks (N+1) prime) (record : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (original : Fin ((prime^(w+1))^16*W) → ZMod 2)
    (addr : (Fin 16 → ZMod (prime^(w+1))) → Fin 16 → ZMod (prime^(w+1))) :
    let ready := ColumnRecordReady columnBank H J record SparseRoleCircuit.encode (fun _ => blank) dest 0 q original
    let clean := fun (D : Stacks (N+1) prime) => ∀ k : Fin N, 35 ≤ k.val →
      D.L (columnPorts k) = [] ∧ D.R (columnPorts k) = []
    let cost := fun i j => 1+completeSwapTime (P := Empty) (U := U) Empty.elim 16 i j w W H J
    ready addr S → clean S → ∃ z F n, z.user = v.user ∧ n ≤ cost 0 7 + cost 8 15 ∧
      Exec body (.seq (columnSwapProgram 16 0 7) (columnSwapProgram 16 8 15)) (mk v S) n (mk z F) ∧
      ready (portSwapDigits ∘ addr) F ∧ clean F ∧
      F.L (Fin.last N) = S.L (Fin.last N) ∧ F.R (Fin.last N) = S.R (Fin.last N) := by
  intro ready clean cost before free
  obtain ⟨u,D,m,hu,hm',first,next,freeD,hl,hr⟩ := columnSwapRecord_exec (0 : Fin 16) 7
    (by decide) H J hm hw hW body v S record dest q original addr before free
  obtain ⟨z,F,n,hz,hn,last,out,freeF,hl',hr'⟩ := columnSwapRecord_exec (8 : Fin 16) 15
    (by decide) H J hm hw hW body u D record dest q original _ next freeD
  exact ⟨z,F,m+n,hz.trans hu,Nat.add_le_add hm' hn,Exec.seq first last,out,freeF,hl'.trans hl,hr'.trans hr⟩

/-- Both swaps, including header setup and workspace cleanup, fit the
stage's volume and atom-width rate with canonical binary headers. -/
theorem portPivotSwap_cost [M8.Machine.Net] (U : Type) :
    ∃ base swaps : ℕ, ∀ w W, 0 < W →
      let M := prime^(w+1)
      let cost := fun i j => 1+completeSwapTime (P := Empty) (U := U) Empty.elim 16 i j w W (Nat.size M) (Nat.size W)
      cost 0 7 + cost 8 15 ≤ (base+swaps*swapVolumeRate w)*(M^16*W) := by
  have one (i j : ℕ) : ∃ a b : ℕ, ∀ w W, 0 < W →
      let M := prime^(w+1)
      1+completeSwapTime (P := Empty) (U := U) Empty.elim 16 i j w W (Nat.size M) (Nat.size W) ≤
        (a+b*swapVolumeRate w)*(M^16*W) := by
    let cost := completeSwapTime (P := Empty) (U := U) Empty.elim 16 i j
    obtain ⟨a,setup⟩ := completeSwapTime_setup_le (P := Empty) (U := U) Empty.elim 16 i j
    have ctr : ∃ c : ℕ, ∀ w H J, cost w 0 H J = cost w 0 H 0 + c*J :=
      ⟨_,fun w H J => completeSwapTime_eq_setup_add_counter _ 16 i j w 0 H J⟩
    have vol : ∃ b : ℕ, ∀ w W H J, cost w W H J ≤ cost w 0 H J +
        b*swapVolumeRate w*((prime^(w+1))^16*W) :=
      ⟨_,fun w W H J => completeSwapTime_le_setup_add_volume _ 16 i j w W H J⟩
    obtain ⟨c,counter⟩ := ctr
    obtain ⟨b,bound⟩ := vol
    let k := 2*(Nat.size prime+1)^2
    refine ⟨1+a*k+c,b,?_⟩
    intro w W hW M
    let H := Nat.size M
    let J := Nat.size W
    have positive : 0 < M^16 := pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _
    have size : M^16 ≤ M^16*W := Nat.le_mul_of_pos_right _ hW
    have bits : 0 < (H+1)^2 := pow_pos (by omega) _
    have field := prefixSetup_volume_le w 15
    change (w+1+M^15)*(H+1)^2 ≤ k*M^16 at field
    have digits : 0 < M^15 := pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _
    rw [Nat.add_mul] at field
    have overhead := (Nat.add_le_add (Nat.le_mul_of_pos_right (w+1) bits)
      (Nat.le_mul_of_pos_left ((H+1)^2) digits)).trans (field.trans (Nat.mul_le_mul_left k size))
    have header := (setup w H).trans (Nat.mul_le_mul_left a overhead)
    have len : J ≤ W := Nat.size_le.mpr Nat.lt_two_pow_self
    have count := Nat.mul_le_mul_left c (len.trans (Nat.le_mul_of_pos_left W positive))
    have run := bound w W H J
    rw [counter] at run
    change cost w W H J ≤ cost w 0 H 0 + c*J + b*swapVolumeRate w*(M^16*W) at run
    change cost w 0 H 0 ≤ _ at header
    change 1+cost w W H J ≤ _
    rw [Nat.add_mul,Nat.add_mul,Nat.add_mul,Nat.one_mul,Nat.mul_assoc]
    have := Nat.mul_pos positive hW
    omega
  obtain ⟨a,b,first⟩ := one 0 7
  obtain ⟨c,d,last⟩ := one 8 15
  refine ⟨a+c,b+d,?_⟩
  intro w W hW M cost
  exact (Nat.add_le_add (first w W hW) (last w W hW)).trans_eq (by ring)

end IntegerMultBounds.MathlibTM2.M6.BitNode
