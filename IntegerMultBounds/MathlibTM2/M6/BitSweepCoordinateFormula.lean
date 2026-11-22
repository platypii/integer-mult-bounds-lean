module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepRecordAddress
public import IntegerMultBounds.MathlibTM2.Cover.FallbackFormulaInputs

/-! Modular arithmetic for the parent coordinates of a sweep record. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589 Certificates.PR589.Nine
open Cover.Fallback Matrix
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

noncomputable def dotFormula {κ ι : Type} [Fintype κ] (row x : κ → RingFormula ι) :=
  RingFormula.sum (Finset.univ.toList.map fun j => .mul (row j) (x j))

private theorem dotFormula_eval {κ ι R : Type} [Fintype κ] [CommRing R]
    (read : ι → R) (row x : κ → RingFormula ι) :
    RingFormula.eval read (dotFormula row x) =
      (fun j => RingFormula.eval read (row j)) ⬝ᵥ (fun j => RingFormula.eval read (x j)) := by
  simp [dotFormula,RingFormula.eval_sum,List.map_map,Function.comp_def,RingFormula.eval,
    Finset.sum_map_toList,dotProduct]

/-- Apply the parent weights and reversal after either port decoder. -/
def parentDigitFormula {ι : Type} (weight : Fin 64 → RingFormula ι)
    (h d : Axis → RingFormula ι) (k : Fin 128) : RingFormula ι :=
  Sum.elim (fun i => .mul (weight i) (h (stageAxis.symm i)))
    (fun i : Fin 64 => d (stageAxis.symm i.rev)) ((@finSumFinEquiv 64 64).symm k)

theorem parentDigitFormula_eval {ι : Type} (w : ℕ) (read : ι → ZMod (prime^w))
    (weight : Fin 64 → RingFormula ι) (h d : Axis → RingFormula ι)
    (units : ∀ i, IsUnit (RingFormula.eval read (weight i))) (k : Fin 128) :
    RingFormula.eval read (parentDigitFormula weight h d k) =
      nodeDigitsEquiv w (RingFormula.eval read ∘ weight) units
        (RingFormula.eval read ∘ h,RingFormula.eval read ∘ d) k := by
  obtain ⟨i,rfl⟩ := (@finSumFinEquiv 64 64).surjective k
  cases i <;> simp [nodeDigitsEquiv,parentDigitFormula,fromBlocks_mulVec,diagonal_apply,
    M8.ReversedExchange.rev,mulVec,dotProduct,Function.comp_def,RingFormula.eval]

/-- Each inactive source digit is a row of the port chart applied to the
corresponding half of the destination, followed by the parent frame. -/
noncomputable def inactiveDigitFormula {ι : Type} (chart : Axis → ChartAxis → RingFormula ι)
    (weight : Fin 64 → RingFormula ι) (digit : Fin 128 → RingFormula ι) :=
  parentDigitFormula weight
    (fun i => dotFormula (chart i) (fun j => digit ((helperFieldOrder none).symm (.inl j))))
    (fun i => dotFormula (chart i) (fun j => digit ((helperFieldOrder none).symm (.inr j))))

theorem inactiveDigitFormula_eval {ι : Type} (w : ℕ) (c : PortCertificate) (read : ι → ZMod (prime^w))
    (chart : Axis → ChartAxis → RingFormula ι) (weight : Fin 64 → RingFormula ι)
    (digit : Fin 128 → RingFormula ι) (coeff : ∀ i j, RingFormula.eval read (chart i j) =
      Swap.Modular.reduce (prime^w) c.fullChart i j) (units : ∀ i, IsUnit (RingFormula.eval read (weight i)))
    (k : Fin 128) :
    RingFormula.eval read (inactiveDigitFormula chart weight digit k) =
      nodeDigitsEquiv w (RingFormula.eval read ∘ weight) units
        (decodeHelperField c none w (RingFormula.eval read ∘ digit)) k := by
  unfold inactiveDigitFormula
  rw [parentDigitFormula_eval w read _ _ _ units]
  apply congrArg (fun s => nodeDigitsEquiv w (RingFormula.eval read ∘ weight) units s k)
  apply Prod.ext <;> funext i <;>
    simp [dotFormula_eval,coeff,decodeHelperField,mulVec]

open RingFormula in
/-- Read chart coefficients from one matrix tape. Rows zero and one of the
second tape hold the two destination halves, and row two holds the weights. -/
noncomputable def inactiveCoordinateCode (k : Fin 128) : RingFormula (Entry Bool 64) :=
  inactiveDigitFormula (fun i j => matrixInput false (stageAxis i) (remainderAxis.symm j))
    (matrixInput true 2) (fun j => Sum.elim (matrixInput true 0) (matrixInput true 1)
      ((@finSumFinEquiv 64 64).symm j)) k

open RingFormula Host Stack Cover.LabelTraversal in
theorem inactiveCoordinate_writes {T Q A : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (ports : Leaf (Entry Bool 64) → Fin T → Fin 7 ↪ Fin T) (bank : ℕ → Fin T → Fin 13 ↪ Fin T)
    (w H : ℕ) (fits : prime^w < 2^H) (c : PortCertificate)
    (mat : Bool → Matrix (Fin 64) (Fin 64) (ZMod (prime^w)))
    (chart : ∀ i j, mat false (stageAxis i) (remainderAxis.symm j) = Swap.Modular.reduce (prime^w) c.fullChart i j)
    (x : Fin 128 → ZMod (prime^w)) (firstHalf : ∀ i, mat true 0 i = x (@finSumFinEquiv 64 64 (.inl i)))
    (secondHalf : ∀ i, mat true 1 i = x (@finSumFinEquiv 64 64 (.inr i))) (units : ∀ i, IsUnit (mat true 2 i))
    (k : Fin 128) (out : Fin T) :
    let f := inactiveCoordinateCode k
    Writes body (prepared bank (entryValue mat) H (leafReady ports mat H) f 0 out) out
      (compile (readLeaf ports) bank f 0 out)
      (binSyms H (nodeDigitsEquiv w (mat true 2) units (decodeHelperField c none w x) k).val)
      (time H (readTime H) f) := by
  intro f
  let digit := fun j => Sum.elim (matrixInput true 0) (matrixInput true 1) ((@finSumFinEquiv 64 64).symm j)
  have digits : eval (entryValue mat) ∘ digit = x := by
    funext j
    obtain ⟨i,rfl⟩ := (@finSumFinEquiv 64 64).surjective j
    cases i <;> simp [digit,eval,entryValue,matrixInput,firstHalf,secondHalf]
  have value := inactiveDigitFormula_eval w c (entryValue mat)
    (fun i j => matrixInput false (stageAxis i) (remainderAxis.symm j)) (matrixInput true 2) digit chart units k
  rw [digits] at value
  exact value ▸ compile_from_matrices body ports bank mat H fits f out

open RingFormula in
noncomputable def activeHalfFormula (side : Fin 64) (i : Axis) : RingFormula (Entry Bool 64) :=
  dotFormula (fun j => matrixInput false (stageAxis i) (stageAxis j))
    (Sum.elim (fun a => dotFormula
      (fun b => matrixInput true ⟨3+a.val,by omega⟩ (stageAxis (.inl b)))
      (fun b => matrixInput true side (stageAxis (.inl b))))
      (fun j => matrixInput true side (stageAxis (.inr j))))

open RingFormula in
noncomputable def activeCoordinateCode (k : Fin 128) : RingFormula (Entry Bool 64) :=
  parentDigitFormula (matrixInput true 2) (activeHalfFormula 0) (activeHalfFormula 1) k

open RingFormula in
theorem activeHalf_eval (w : ℕ) (mat : Bool → Matrix (Fin 64) (Fin 64) (ZMod (prime^w)))
    (H : Matrix Axis Axis (ZMod (prime^w))) (side : Fin 64) (x : Axis → ZMod (prime^w))
    (route : ∀ i j, mat false (stageAxis i) (stageAxis j) = H i j)
    (translate : ∀ a b : Fin 8, mat true ⟨3+a.val,by omega⟩ (stageAxis (.inl b)) =
      ((undoTranslation a b : ℤ) : ZMod (prime^w)))
    (input : ∀ j, mat true side (stageAxis j) = x j) :
    eval (entryValue mat) ∘ activeHalfFormula side =
      H.mulVec (Sum.elim ((undoTranslation.map (Int.cast : ℤ → ZMod (prime^w))).mulVec (x ∘ Sum.inl))
        (x ∘ Sum.inr)) := by
  funext i
  simp only [Function.comp_apply,activeHalfFormula,dotFormula_eval,matrixInput,eval,entryValue,route,mulVec]
  apply congrArg (dotProduct (H i))
  funext j
  cases j <;> simp [dotFormula_eval,eval,entryValue,translate,input,Function.comp_def,mulVec,Matrix.map]

open RingFormula Host Stack Cover.LabelTraversal in
/-- On the active port the two data rows contain the local and exterior
fields in stage-axis order. The translation occupies eight more rows. -/
theorem activeCoordinate_writes {T Q A : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (ports : Leaf (Entry Bool 64) → Fin T → Fin 7 ↪ Fin T) (bank : ℕ → Fin T → Fin 13 ↪ Fin T)
    (w H : ℕ) (fits : prime^w < 2^H) (c : PortCertificate) (n : Fin 9)
    (mat : Bool → Matrix (Fin 64) (Fin 64) (ZMod (prime^w)))
    (route : ∀ i j, mat false (stageAxis i) (stageAxis j) = Swap.Modular.reduce (prime^w) (c.stageRoute n) i j)
    (translate : ∀ a b : Fin 8, mat true ⟨3+a.val,by omega⟩ (stageAxis (.inl b)) =
      ((undoTranslation a b : ℤ) : ZMod (prime^w)))
    (x : Swap.Shear.State Axis (ZMod (prime^w)))
    (h : ∀ j, mat true 0 (stageAxis j) = x.1 j) (d : ∀ j, mat true 1 (stageAxis j) = x.2 j)
    (units : ∀ i, IsUnit (mat true 2 i)) (k : Fin 128) (out : Fin T) :
    let f := activeCoordinateCode k
    let D := undoTranslation.map (Int.cast : ℤ → ZMod (prime^w))
    let R := Swap.Modular.reduce (prime^w) (c.stageRoute n)
    let fields := chartHalves x
    let s := chartHalves.symm (M8.Exchange.transform D D fields.1,fields.2)
    Writes body (prepared bank (entryValue mat) H (leafReady ports mat H) f 0 out) out
      (compile (readLeaf ports) bank f 0 out)
      (binSyms H (nodeDigitsEquiv w (mat true 2) units (M8.Exchange.transform R R s) k).val)
      (time H (readTime H) f) := by
  intro f D R fields s
  have value := parentDigitFormula_eval w (entryValue mat) (matrixInput true 2)
    (activeHalfFormula 0) (activeHalfFormula 1) units k
  rw [activeHalf_eval w mat R 0 x.1 route translate h,activeHalf_eval w mat R 1 x.2 route translate d] at value
  exact value ▸ compile_from_matrices body ports bank mat H fits f out

/-- Decode the destination once. Translating the two local fields in this
state gives precisely the active address decoder used by the rank proof. -/
theorem chartAddress_decode_local {Q W : ℕ} [NeZero Q]
    (u : Swap.Shear.State (Fin 8) (ZMod Q)) (t : Fin (Q^112*W))
    (f : Swap.Shear.State (Fin 8) (ZMod Q) → Swap.Shear.State (Fin 8) (ZMod Q)) :
    let x := (chartAddress.symm (copyAddress.symm (u,t))).1
    chartHalves.symm (f (chartHalves x).1,(chartHalves x).2) =
      (chartAddress.symm (copyAddress.symm (f u,t))).1 := by
  let p := chartAddress.symm (copyAddress.symm (u,t))
  have move := chartAddress_local p.1 p.2 f
  rw [show (p.1,p.2) = p from rfl] at move
  simp only [p,Equiv.apply_symm_apply] at move
  simpa only [Equiv.symm_apply_apply] using congrArg (fun i => (chartAddress.symm i).1) move.symm

open RingFormula in
/-- A single quadratic bound covers all 128 coordinate evaluations per
record in either chart. Its constant is independent of the parent and stage. -/
theorem sweepCoordinate_time :
    ∃ C : ℕ, ∀ H : ℕ, ∀ active : Bool,
      (∑ k : Fin 128, time H (readTime H)
        (if active then activeCoordinateCode k else inactiveCoordinateCode k)) ≤ C*(H+1)^2 := by
  let cost := fun (f : Fin 128 → RingFormula (Entry Bool 64)) => ∑ k, time 1 (readTime 1) (f k)
  have bound (f : Fin 128 → RingFormula (Entry Bool 64)) (H) :
      (∑ k, time H (readTime H) (f k)) ≤ cost f*(H+1)^2 := by
    unfold cost
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun k _ => time_readTime_le (f k) H
  refine ⟨max (cost inactiveCoordinateCode) (cost activeCoordinateCode),?_⟩
  intro H active
  cases active
  · exact (bound inactiveCoordinateCode H).trans (Nat.mul_le_mul_right _ (le_max_left ..))
  · exact (bound activeCoordinateCode H).trans (Nat.mul_le_mul_right _ (le_max_right ..))

end IntegerMultBounds.MathlibTM2.M6.BitNode
