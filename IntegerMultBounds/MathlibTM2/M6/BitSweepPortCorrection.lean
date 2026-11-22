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

/-- All 17,760 source/target pairs receive their two corrections.
Other owners are preserved by each pass. -/
theorem sweepPortCorrections [M8.Machine.Net] :
    ∃ C : ℝ, ∀ (n : Fin 9) (w B W : ℕ), 0 < w → 0 < B*((prime^w)^112*W) →
      let K := (prime^w)^112*W
      let V := (prime^w)^16*(B*K)
      ∃ enter leave : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        ((enter.cost+leave.cost : ℕ) : ℝ) ≤ C*(w : ℝ)^M8.Machine.BudgetBound.tau*V ∧
        (∀ x i, (∀ k, sourceOwner n k ≠ i) → enter.transform x i = x i) ∧
        (∀ y i, (∀ k, targetOwner n k ≠ i) → leave.transform y i = y i) ∧
        ∀ x y, sweepEffect n w B W (enter.transform x) y →
          ∀ (k : (Fin 32 × Fin 5) × Fin 111) (z : LabelEntry.Cell (copyLabelLayout w B K) B) s,
            let cell := fun v => index (embed v) (@finProdFinEquiv B K (z.b,z.after))
            let P := translatedPortProjector (ZMod (prime^w)) (4 : ZMod (prime^w))⁻¹ k.2
            let src := sourceOwner n k
            let dst := targetOwner n k
            leave.transform y src (cell s) = x src (cell (M8.Exchange.exchange P s.swap)) ∧
            leave.transform y dst (cell s) =
              x dst (cell (M8.Exchange.exchange (1-P) s)) + x src (cell s.swap) := by
  classical
  choose c build using sweepEffect_correctedPort
  let jobs := stageRuns.product (List.finRange 111)
  have unique := stageRuns_nodup.product (List.nodup_finRange 111)
  have mem (k : (Fin 32 × Fin 5) × Fin 111) : k ∈ jobs :=
    List.mem_flatMap.mpr ⟨k.1,mem_stageRuns _,List.mem_map.mpr ⟨k.2,List.mem_finRange _,rfl⟩⟩
  have count : jobs.length = 17760 := by
    exact (List.length_product stageRuns (List.finRange 111)).trans (by rw [stageRuns_length,List.length_finRange])
  let base := (jobs.map fun k => c k.2).sum
  refine ⟨(base : ℝ)+17760*(2*|LeafCore.C|+14),?_⟩
  intro n w B W hw hW K V
  choose pre post price correct using fun t => build t w B W hw hW
  obtain ⟨enter,paid,entry,keep⟩ := compilePorts ⟨sourceOwner n,source_injective n⟩ (fun k => pre k.2) jobs unique
  obtain ⟨leave,cost,exitRow,off⟩ := compilePorts ⟨targetOwner n,targetOwner_injective n⟩ (fun k => post k.2) jobs unique
  refine ⟨enter,leave,?_,fun x i away => keep x i (fun k _ => away k),
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
  · intro x y step k z s cell P src dst
    have result := correct k.2 n k.1 x (enter.transform x) y (entry x k (mem k))
      (keep x dst (fun l _ => source_ne_target n l k)) step z s
    constructor
    · exact (congrFun (off y src (fun l _ => (source_ne_target n k l).symm)) _).trans result.1
    · exact (congrFun (exitRow y k (mem k)) _).trans result.2

end IntegerMultBounds.MathlibTM2.M6.BitNode
