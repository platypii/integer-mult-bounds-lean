module

public import IntegerMultBounds.MathlibTM2.M6.BitInactiveChartRun
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
        stage.cost ≤ a*V+k*(3808274*V+LeafCore.coreCost V w+1)+5 ∧
        HasStackSeed stage.metadata ∧ ∀ x i,
          routedCell backward x (stage.transform x) i ((flatToSweep w W n r i).cast
            (by simpa only [Nat.one_mul] using ordinaryCompact_width (prime^w) W)) := by
  by_cases active : r.bank.val / 2 = BitHosting.activePair n.val
  swap
  · obtain ⟨a,k,m,build⟩ := inactiveChart_owner n r active backward
    refine ⟨a,k,m,?_⟩
    intro w W hw hW V
    obtain ⟨stage,fixed,cost,seed,read⟩ := build w W hw hW
    exact ⟨stage,fixed,by dsimp only [V]; rw [cost]; omega,seed,read⟩
  let c := port r.port.val
  have checked := port_checked _ r.port.isLt
  let H := c.stageRoute n
  obtain ⟨a,k,m,route⟩ := pairedChart_owner H H (c.stageRoute_mul_self checked n)
    (fun i j => ⟨(stageRoute_entry c checked n i j).1.trans (by decide),
      (stageRoute_entry c checked n i j).2.trans (by decide)⟩) flatParentOrder backward
  have cancel : localShift shiftBack * localShift undoTranslation = 1 := by
    simp [localShift,fromBlocks_multiply,shift_cast_cancel]
  obtain ⟨b,l,p,translate⟩ := pairedChart_owner _ _ cancel localShift_bound helperDigits backward
  refine ⟨a+b,k+l,(if backward then SharedBankSkeleton.compose p m else SharedBankSkeleton.compose m p),?_⟩
  intro w W hw hW V
  obtain ⟨A,fa,ca,sa,ra⟩ := route w W hw hW
  obtain ⟨B,fb,cb,sb,rb⟩ := translate w W hw hW
  refine ⟨(if backward then SharedBankStage.compose B A else SharedBankStage.compose A B),?_,?_,?_,?_⟩
  · cases backward <;> simp [fa,fb]
  · cases backward <;> simp only [Bool.false_eq_true,↓reduceIte] <;>
        first | change A.cost+B.cost+1 ≤ _ | change B.cost+A.cost+1 ≤ _
    all_goals
      dsimp only [V]
      rw [ca,cb,Nat.add_mul,Nat.add_mul]
      omega
  · cases backward
    · exact compose_seed sa sb
    · exact compose_seed sb sa
  · intro x i
    obtain ⟨⟨s,j⟩,rfl⟩ := (flatWindowEquiv w W).surjective i
    let y := M8.Exchange.transform (reduce (prime^w) H) (reduce (prime^w) H) s
    let T := reduce (prime^w) (localShift shiftBack)
    let cell := FlatCoordinateLayout.index (Sum.elim (T *ᵥ y.1) (T *ᵥ y.2) ∘ helperDigits) j
    have dst : (flatToSweep w W n r (flatWindowEquiv w W (s,j))).cast
        (by simpa only [Nat.one_mul] using ordinaryCompact_width (prime^w) W) = cell :=
      Fin.ext (activeSweep_cell n r active s j)
    rw [dst]
    cases backward with
    | false => exact (rb (A.transform x) y j).trans (ra x s j)
    | true => exact (ra (B.transform x) s j).trans (rb x y j)

/-- One rate covers entry and return for every stage and port, at every
precision and spectator count. -/
theorem sweepChart_cost [M8.Machine.Net] :
    ∃ C : ℝ, ∀ (n : Fin 9) (r : Role) (backward : Bool),
      ∃ machine : SharedBankSkeleton.Skeleton 1 prime, ∀ (w W : ℕ), 0 < w → 0 < W →
      let V := (prime^w)^128*W
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧
        (stage.cost : ℝ) ≤ C * V * (w : ℝ)^M8.Machine.BudgetBound.tau ∧
        HasStackSeed stage.metadata ∧ ∀ x i,
          routedCell backward x (stage.transform x) i ((flatToSweep w W n r i).cast
            (by simpa only [Nat.one_mul] using ordinaryCompact_width (prime^w) W)) := by
  choose a k machine build using fun p : Fin 9 × Role × Bool => sweepChart_owner p.1 p.2.1 p.2.2
  let rate := fun p => (a p : ℝ) + (k p : ℝ)*(3808275+|LeafCore.C|) + 5
  obtain ⟨C,bound⟩ := Finite.exists_le rate
  refine ⟨C,?_⟩
  intro n r backward
  let p := (n,r,backward)
  refine ⟨machine p,?_⟩
  intro w W hw hW V
  obtain ⟨stage,fixed,price,seed,read⟩ := build p w W hw hW
  refine ⟨stage,fixed,?_,seed,read⟩
  let power := (w : ℝ)^M8.Machine.BudgetBound.tau
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast hw : (1 : ℝ) ≤ w)
    M8.Machine.BudgetBound.exponent_range.1.le
  have volume : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW
  have scans : (V : ℝ) ≤ V*power := le_mul_of_one_le_right (Nat.cast_nonneg _) one
  have joins : 1 ≤ (V : ℝ)*power := one_le_mul_of_one_le_of_one_le (by exact_mod_cast volume) one
  have core := RevBudget.coreCost_le V w (L := power) (by rw [max_eq_right hw])
  have swap : 3808274*(V : ℝ)+LeafCore.coreCost V w+1 ≤ (3808275+|LeafCore.C|)*(V*power) := by
    nlinarith only [scans,core,joins]
  calc
    (stage.cost : ℝ) ≤ ((a p*V + k p*(3808274*V+LeafCore.coreCost V w+1)+5 : ℕ) : ℝ) := by exact_mod_cast price
    _ ≤ rate p * (V*power) := by
      push_cast
      dsimp only [rate]
      nlinarith only [mul_le_mul_of_nonneg_left scans (Nat.cast_nonneg (a p)),
        mul_le_mul_of_nonneg_left swap (Nat.cast_nonneg (k p)),joins]
    _ ≤ C * V * power := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (bound p) (by positivity)

end IntegerMultBounds.MathlibTM2.M6.BitNode
