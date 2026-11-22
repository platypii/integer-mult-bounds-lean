module

public import IntegerMultBounds.MathlibTM2.M6.BitInactiveChartRun
public import IntegerMultBounds.MathlibTM2.M8.Height
public import IntegerMultBounds.MathlibTM2.M6.BitSweepChartEntries

/-! Execute the active port route and translate its two live polynomial fields. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589 Certificates.PR589.Nine
open Shared50ModularControl (prime)
open Matrix IntegerMultBounds.Swap.Modular M8.RevMachine
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

private def shiftBack : Matrix (Fin 8) (Fin 8) ℤ :=
  of fun i j => (j.val.choose i.val : ℤ) * 2^(j.val-i.val)

private theorem shift_cancel : shiftBack * undoTranslation = 1 := by decide +kernel

private theorem shift_bound : ∀ i j, (shiftBack i j).natAbs ≤ 10000 := by decide +kernel

private theorem shift_cast_cancel (R : Type*) [CommRing R] :
    shiftBack.map (Int.cast : ℤ → R) * undoTranslation.map (Int.cast : ℤ → R) = 1 := by
  let f := (Int.castRingHom R).mapMatrix (m := Fin 8)
  exact (map_mul f _ _).symm.trans ((congrArg f shift_cancel).trans (map_one f))

private theorem shift_reduce (w : ℕ) :
    shiftBack.map (Int.cast : ℤ → ZMod (prime^w)) =
      (undoTranslation.map (Int.cast : ℤ → ZMod (prime^w)))⁻¹ :=
  (inv_eq_left_inv (shift_cast_cancel _)).symm

private def localShift (S : Matrix (Fin 8) (Fin 8) ℤ) : Matrix Axis Axis ℚ :=
  fromBlocks (S.map (Int.cast : ℤ → ℚ)) 0 0 1

private theorem localShift_bound (i j) :
    ((localShift shiftBack i j).num.natAbs ≤ 10000 ∧ (localShift shiftBack i j).den ≤ 10000) := by
  cases i with
  | inl i =>
    cases j with
    | inl j => simpa [localShift] using shift_bound i j
    | inr j => simp [localShift]
  | inr i =>
    cases j with
    | inl j => simp [localShift]
    | inr j => simp [localShift,one_apply]; split <;> decide

private theorem translatedWindow_index {w W : ℕ} (s : Swap.Shear.State Axis (ZMod (prime^w))) (j : Fin W) :
    let T := reduce (prime^w) (localShift shiftBack)
    (FlatCoordinateLayout.index (Sum.elim (T *ᵥ s.1) (T *ᵥ s.2) ∘ helperDigits) j).val =
      (activeWindowAddress (0 : Fin 1) s j).val := by
  intro T
  let D := undoTranslation.map (Int.cast : ℤ → ZMod (prime^w))
  let move := M8.Exchange.transform D⁻¹ D⁻¹
  have mat : T = fromBlocks D⁻¹ 0 0 1 := by
    rw [← show shiftBack.map (Int.cast : ℤ → ZMod (prime^w)) = D⁻¹ from shift_reduce w]
    ext (i|i) (j|j) <;> simp [T,localShift,reduce,ratMod,one_apply] <;> split <;> simp
  have state : (T *ᵥ s.1,T *ᵥ s.2) = chartHalves.symm (move (chartHalves s).1,(chartHalves s).2) := by
    rw [mat]
    apply Prod.ext <;> simp [fromBlocks_mulVec] <;> rfl
  rw [helperDigits_index (T *ᵥ s.1,T *ᵥ s.2),state,← chartAddress_local s j move]
  simp [activeWindowAddress,copyAddress_index,FlatCoordinateLayout.index,finProdFinEquiv_apply_val,move,D]

private theorem activeSweep_cell {w W : ℕ} (n : Fin 9) (r : Role)
    (active : r.bank.val / 2 = BitHosting.activePair n.val)
    (s : Swap.Shear.State Axis (ZMod (prime^w))) (j : Fin W) :
    let H := reduce (prime^w) ((port r.port.val).stageRoute n)
    let y := M8.Exchange.transform H H s
    let T := reduce (prime^w) (localShift shiftBack)
    (flatToSweep w W n r (flatWindowEquiv w W (s,j))).val =
      (FlatCoordinateLayout.index (Sum.elim (T *ᵥ y.1) (T *ᵥ y.2) ∘ helperDigits) j).val := by
  intro H y T
  simp only [flatToSweep,Equiv.trans_apply,Equiv.symm_apply_apply,sweepRoleEquiv,active,↓reduceIte]
  exact (translatedWindow_index y j).symm

/-- Each stage role reaches its certified sweep address on one fixed owner
tape. The live case adds the inverse polynomial translation on the local axes. -/
theorem sweepChart_owner [M8.Machine.Net] (n : Fin 9) (r : Role) (backward : Bool := false) :
    ∃ (a k : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^128*W
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧
        stage.cost = a*V+k*(3808274*V+LeafCore.coreCost V w+1)+2 ∧
        HasStackSeed stage.metadata ∧ ∀ x i,
          routedCell backward x (stage.transform x) i ((flatToSweep w W n r i).cast
            (by simpa only [Nat.one_mul] using ordinaryCompact_width (prime^w) W)) := by
  by_cases active : r.bank.val / 2 = BitHosting.activePair n.val
  swap
  · obtain ⟨a,k,m,build⟩ := inactiveChart_owner n r active backward
    refine ⟨a,k,m,?_⟩
    intro w W hw hW V
    obtain ⟨stage,fixed,cost,seed,read⟩ := build w W hw hW
    exact ⟨stage,fixed,cost,seed,read⟩
  have cancel : localShift shiftBack * localShift undoTranslation = 1 := by
    simp [localShift,fromBlocks_multiply,shift_cast_cancel]
  let c := port r.port.val
  have checked := port_checked _ r.port.isLt
  let H := c.stageRoute n
  have inverse : (localShift shiftBack * H) * (H * localShift undoTranslation) = 1 := by
    rw [mul_assoc, ← mul_assoc H H, c.stageRoute_mul_self checked n, one_mul, cancel]
  have smallShift : M8.Height.Bounded (localShift shiftBack) (2^14) := fun i j =>
    (max_le (localShift_bound i j).1 (localShift_bound i j).2).trans (by decide)
  have smallRoute : M8.Height.Bounded H (2^2) := fun i j =>
    max_le (stageRoute_entry c checked n i j).1 (stageRoute_entry c checked n i j).2
  have height := M8.Height.bounded_mul smallShift smallRoute
  obtain ⟨a,k,m,build⟩ := pairedChart_owner _ _ inverse
    (fun i j => ⟨(M8.Height.num_le_ht _).trans (height i j),
      (M8.Height.den_le_ht _).trans (height i j)⟩) helperDigits backward
    ((Nat.pow_le_pow_left (by decide : 2 ≤ 10) _).trans
      (pow_le_pow_right₀ (by decide : 1 ≤ (10:ℕ)) (by simp [Axis])))
  refine ⟨a,k,m,?_⟩
  intro w W hw hW V
  obtain ⟨A,fixed,cost,seed,read⟩ := build w W hw hW
  refine ⟨A,fixed,cost,seed,?_⟩
  intro x i
  obtain ⟨⟨s,j⟩,rfl⟩ := (flatWindowEquiv w W).surjective i
  have adm : Admissible (prime^w) (localShift shiftBack) := by
    intro i k
    cases i <;> cases k <;> simp [localShift,one_apply] <;> split <;> simp
  have eq := activeSweep_cell n r active s j
  have cell := read x s j
  rw [reduce_mul _ adm (stageRoute_admissible c checked n w)] at cell
  simp only [← mulVec_mulVec] at cell
  let R := reduce (prime^w) H
  let T := reduce (prime^w) (localShift shiftBack)
  have dst : (flatToSweep w W n r (flatWindowEquiv w W (s,j))).cast
      (by simpa only [Nat.one_mul] using ordinaryCompact_width (prime^w) W) =
      FlatCoordinateLayout.index (Sum.elim (T *ᵥ (R *ᵥ s.1)) (T *ᵥ (R *ᵥ s.2)) ∘ helperDigits) j :=
    Fin.ext eq
  rw [dst]
  exact cell

end IntegerMultBounds.MathlibTM2.M6.BitNode
