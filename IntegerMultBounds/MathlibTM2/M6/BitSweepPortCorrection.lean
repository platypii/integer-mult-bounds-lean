module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepRead

/-! Place the active port corrections around one compact sweep. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open Certificates.PR589 Certificates.PR589.Nine AffineFieldCoordinates FlatCoordinateLayout
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

noncomputable def sourceOwner (n : Fin 9) (k : (Fin 32 × Fin 5) × Fin 111) : Fin 142081 :=
  ownerTape n k.1.1 k.1.2 (k.2.castLE (by decide))

private theorem source_injective (n : Fin 9) : Function.Injective (sourceOwner n) := by
  rintro ⟨p,t⟩ ⟨q,u⟩ eqn
  have same : p = q := by
    by_contra other
    exact otherRunMissesPort n p q other _ (u.castLE (by decide)) (by change u.val < 222; omega) eqn
  subst q
  exact Prod.ext rfl (Fin.ext (congrArg (Fin.val : Fin 661 → ℕ) (ownerTape_injective n p.1 p.2 eqn)))

private theorem source_ne_target (n : Fin 9) (k l : (Fin 32 × Fin 5) × Fin 111) :
    sourceOwner n k ≠ targetOwner n l := by
  obtain ⟨p,t⟩ := k
  obtain ⟨q,u⟩ := l
  by_cases same : p = q
  · subst q
    intro eqn
    have h := congrArg (Fin.val : Fin 661 → ℕ) (ownerTape_injective n p.1 p.2 eqn)
    change t.val = 111+u.val at h
    omega
  · exact otherRunMissesPort n p q same _ ⟨111+u.val,by omega⟩ (by dsimp; omega)

/-- Physical active-port cell for a full modular window, inherited block and spectator. -/
noncomputable def activeWindowAddress {w B W : ℕ} (b : Fin B)
    (s : Swap.Shear.State Axis (ZMod (prime^w))) (j : Fin W) : Fin ((prime^w)^16*(B*((prime^w)^112*W))) :=
  let D := undoTranslation.map (Int.cast : ℤ → ZMod (prime^w))
  let a := copyAddress (chartAddress (s,j))
  index (embed (M8.Exchange.transform D⁻¹ D⁻¹ a.1)) (finProdFinEquiv (b,a.2))

/-- The active port chart enumerates the compact owner exactly once, including
the inherited block and every spectator position. -/
noncomputable def activeWindowEquiv (w B W : ℕ) :
    Fin B × (Swap.Shear.State Axis (ZMod (prime^w)) × Fin W) ≃
      Fin ((prime^w)^16*(B*((prime^w)^112*W))) :=
  let D := undoTranslation.map (Int.cast : ℤ → ZMod (prime^w))
  let unit := (Matrix.isUnit_iff_isUnit_det D).mp (translatedPort_modular w 0).1
  let basis : Equiv.Perm (Swap.Shear.State (Fin 8) (ZMod (prime^w))) :=
    ⟨M8.Exchange.transform D⁻¹ D⁻¹,M8.Exchange.transform D D,
      fun s => by simp [M8.Exchange.transform,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv D unit],
      fun s => by simp [M8.Exchange.transform,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul D unit]⟩
  let split := chartAddress.trans copyAddress
  let swap : Fin B × (_ × Fin ((prime^w)^112*W)) ≃ _ × (Fin B × Fin ((prime^w)^112*W)) :=
    ⟨fun (b,s,k) => (s,b,k),fun (s,b,k) => (b,s,k),fun _ => rfl,fun _ => rfl⟩
  ((Equiv.refl _).prodCongr split).trans <| swap.trans <|
    (basis.prodCongr finProdFinEquiv).trans copyAddress.symm

@[simp] theorem activeWindowEquiv_apply {w B W : ℕ} (b : Fin B)
    (s : Swap.Shear.State Axis (ZMod (prime^w))) (k : Fin W) :
    activeWindowEquiv w B W (b,s,k) = activeWindowAddress b s k := rfl

/-- Inactive ports enumerate the same owner through their own chart. -/
noncomputable def inactiveWindowEquiv (w B W : ℕ) (lane : BankLane) :
    Fin B × (Swap.Shear.State Axis (ZMod (prime^w)) × Fin W) ≃
      Fin ((prime^w)^16*(B*((prime^w)^112*W))) := by
  let address := fun (p : Fin B × (Swap.Shear.State Axis (ZMod (prime^w)) × Fin W)) =>
    stagedCoordinateEquiv (prime^w) B W
      (p.1,helperSlotField (port lane.2.1.val) none w p.2.1,p.2.2)
  let decode := fun i =>
    let (b,x,j) := (stagedCoordinateEquiv (prime^w) B W).symm i
    (b,decodeHelperField (port lane.2.1.val) none w x,j)
  have back : Function.RightInverse decode address := by
    intro i
    obtain ⟨⟨b,x,j⟩,rfl⟩ := (stagedCoordinateEquiv (prime^w) B W).surjective i
    simp only [decode,address,Equiv.symm_apply_apply,
      decodeHelperField_rightInverse _ (port_checked _ lane.2.1.isLt) none w x]
  have inj := (Finite.injective_iff_surjective_of_equiv (activeWindowEquiv w B W)).mpr back.surjective
  exact ⟨address,decode,fun x => inj (back (address x)),back⟩

theorem inactiveWindowEquiv_read {w B W : ℕ} (lane : BankLane) (b : Fin B) (j : Fin W)
    (z : Axis ⊕ Axis → ℚ) :
    let v := addressMod (prime^w) z
    inactiveWindowEquiv w B W lane (b,(v ∘ Sum.inl,v ∘ Sum.inr),j) = sweepAddress b j lane z := rfl

/-- All 17,760 source/target pairs receive their two corrections.
Other owners are preserved by each pass. -/
theorem sweepPortCorrections [M8.Machine.Net] :
    ∃ (C : ℝ) (tapes : ℕ), ∀ (n : Fin 9) (w B W : ℕ), 0 < w → 0 < B*((prime^w)^112*W) →
      let K := (prime^w)^112*W
      let V := (prime^w)^16*(B*K)
      ∃ enter leave : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        enter.tapes ≤ tapes ∧ leave.tapes ≤ tapes ∧
        ((enter.cost+leave.cost : ℕ) : ℝ) ≤ C*(w : ℝ)^M8.Machine.BudgetBound.tau*V ∧
        (∀ x i, (∀ k, sourceOwner n k ≠ i) → enter.transform x i = x i) ∧
        (∀ y i, (∀ k, targetOwner n k ≠ i) → leave.transform y i = y i) ∧
        ∀ x y, sweepEffect n w B W (enter.transform x) y →
          ∀ (k : (Fin 32 × Fin 5) × Fin 111) (b : Fin B)
            (s : Swap.Shear.State Axis (ZMod (prime^w))) (j : Fin W),
            let cell := fun v => activeWindowAddress b v j
            let L := Matrix.diagonal fun i : Exterior => if i.1.val < n.val then (1 : ZMod (prime^w)) else 0
            let frame := fun (P : Matrix (Fin 8) (Fin 8) (ZMod (prime^w))) =>
              M8.Exchange.exchange (Matrix.fromBlocks P 0 0 L)
            let P := Swap.Modular.reduce (prime^w) (port k.2.val).lineProj
            let src := sourceOwner n k
            let dst := targetOwner n k
            leave.transform y src (cell s) = x src (cell (frame P (frame 1 s))) ∧
            leave.transform y dst (cell s) =
              x dst (cell (frame (1-P) (frame 0 s))) + x src (cell (frame 1 (frame 0 s))) := by
  classical
  choose c preSize postSize build using sweepEffect_correctedPort
  let jobs := stageRuns.product (List.finRange 111)
  have unique := stageRuns_nodup.product (List.nodup_finRange 111)
  have mem (k : (Fin 32 × Fin 5) × Fin 111) : k ∈ jobs :=
    List.mem_flatMap.mpr ⟨k.1,mem_stageRuns _,List.mem_map.mpr ⟨k.2,List.mem_finRange _,rfl⟩⟩
  have count : jobs.length = 17760 := by
    exact (List.length_product stageRuns (List.finRange 111)).trans (by rw [stageRuns_length,List.length_finRange])
  let base := (jobs.map fun k => c k.2).sum
  let total := fun (size : Fin 111 → ℕ) => 142081+(jobs.map fun k => 142081+(size k.2+142080)).sum
  refine ⟨(base : ℝ)+17760*(2*|LeafCore.C|+14),max (total preSize) (total postSize),?_⟩
  intro n w B W hw hW K V
  choose pre post preFixed postFixed price correct using fun t => build t w B W hw hW
  obtain ⟨enter,enterTapes,paid,entry,keep⟩ := compilePortsSized ⟨sourceOwner n,source_injective n⟩ (fun k => pre k.2) jobs unique
  obtain ⟨leave,leaveTapes,cost,exitRow,off⟩ := compilePortsSized ⟨targetOwner n,targetOwner_injective n⟩ (fun k => post k.2) jobs unique
  refine ⟨enter,leave,by simpa only [enterTapes,preFixed,total] using le_max_left (total preSize) (total postSize),
    by simpa only [leaveTapes,postFixed,total] using le_max_right (total preSize) (total postSize),?_,fun x i away => keep x i (fun k _ => away k),
    fun y i away => off y i (fun k _ => away k),?_⟩
  · rw [paid,cost,count]
    have total := congrArg (fun f : ((Fin 32 × Fin 5) × Fin 111 → ℕ) => (jobs.map f).sum)
      (funext fun k => price k.2)
    simp only [List.sum_map_add,List.sum_map_mul_right,List.map_const',List.sum_replicate,
      nsmul_eq_mul,count] at total
    have exactCost : ((jobs.map fun k => (pre k.2).cost).sum+17760) +
        ((jobs.map fun k => (post k.2).cost).sum+17760) = base*V+17760*(2*LeafCore.coreCost V w+14) := by
      dsimp only [base,V,K] at total ⊢
      omega
    rw [exactCost]
    let power := (w : ℝ)^M8.Machine.BudgetBound.tau
    have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ w from hw))
      M8.Machine.BudgetBound.exponent_range.1.le
    have volume : 1 ≤ V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW
    have core := RevBudget.coreCost_le V w (L := power) (by rw [max_eq_right hw])
    have joins : 1 ≤ power*(V : ℝ) := one_le_mul_of_one_le_of_one_le one (by exact_mod_cast volume)
    have linear := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (Nat.cast_nonneg V (α := ℝ)) one)
      (Nat.cast_nonneg base (α := ℝ))
    change _ ≤ (_+17760*(2*|LeafCore.C|+14))*power*V
    push_cast
    linarith only [linear,core,joins]
  · intro x y step k b s j cell L frame P src dst
    let row := fun (bank : OwnerArray w B W) i (l : Fin K) (v : Swap.Shear.State (Fin 8) (ZMod (prime^w))) =>
      bank i (index (embed v) (finProdFinEquiv (b,l)))
    apply activePort_window n k.2 (row x src) (row x dst) (row (leave.transform y) src)
      (row (leave.transform y) dst) _ s j
    intro l v
    let z : LabelEntry.Cell (copyLabelLayout w B K) B :=
      ⟨⟨0,pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _⟩,⟨0,Nat.zero_lt_one⟩,b,
        ⟨0,by simp [copyLabelLayout,ActualAffineScaling.modulus]⟩,⟨0,Nat.zero_lt_one⟩,
        ⟨0,by simp [copyLabelLayout,ActualAffineScaling.modulus]⟩,l⟩
    have result := correct k.2 n k.1 x (enter.transform x) y (entry x k (mem k))
      (keep x dst (fun l _ => source_ne_target n l k)) step z v
    constructor
    · exact (congrFun (off y src (fun l _ => (source_ne_target n k l).symm)) _).trans result.1
    · exact (congrFun (exitRow y k (mem k)) _).trans result.2

end IntegerMultBounds.MathlibTM2.M6.BitNode
