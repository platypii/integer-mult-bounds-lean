module

public import IntegerMultBounds.MathlibTM2.M6.BitHelperChartRun

/-! Read the remainder child directly in the certified forward and return owner charts. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589.Nine
open Cover RecursiveInterchangeLayout M8.RevMachine
open Shared50ModularControl (prime)
open Matrix IntegerMultBounds.Swap.Modular
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

private theorem helperField_halves {w : ℕ} (c : PortCertificate) (s : Swap.Shear.State Axis (ZMod (prime^w))) :
    let field := fun v (i : Fin 64) => ((reduce (prime^w) c.fullChart).transpose *ᵥ v) (remainderAxis i)
    helperSlotField c none w s = Fin.addCases (motive := fun _ => ZMod (prime^w)) (field s.1) (field s.2) := by
  intro field
  funext i
  refine Fin.addCases (m := 64) (n := 64) (fun j => ?_) (fun j => ?_) i
  all_goals simp only [helperSlotField,helperFieldOrder,field,Function.comp_apply,Equiv.trans_apply,
    @finSumFinEquiv_symm_apply_castAdd 64 64,@finSumFinEquiv_symm_apply_natAdd 64 64,
    Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,Sum.elim_inl,Sum.elim_inr,
    Fin.addCases_left,Fin.addCases_right]

theorem helperInterval_read {w W lo hi : ℕ} (c : PortCertificate) (hc : c.Checked)
    (ordered : lo ≤ hi) (fits : hi ≤ 63)
    (x : Fin (volume prime (phaseIntervalChild lo hi w W 64)) → ZMod 2)
    (s : Swap.Shear.State Axis (ZMod (prime^w))) (j : Fin W) :
    let y := M8.Exchange.exchange (reduce (prime^w) (c.span lo hi)) s
    let cell := fun a => FlatCoordinateLayout.index (helperSlotField c none w a) j
    ext (Shared50RecursiveNodeRows.transpose (one_dvd _) x) (cell y).val = ext x (cell s).val := by
  intro y cell
  let field := fun v (i : Fin 64) => ((reduce (prime^w) c.fullChart).transpose *ᵥ v) (remainderAxis i)
  let swap := fun (a b : Fin 64 → ZMod (prime^w)) (i : Fin 64) =>
    if lo ≤ i.val ∧ i.val < hi then b i else a i
  have pair := remainderExchange_tapeDigits c hc lo hi w fits s
  have halves : field y.1 = swap (field s.1) (field s.2) ∧ field y.2 = swap (field s.2) (field s.1) := by
    constructor <;> funext i
    all_goals have h := pair i
    all_goals by_cases hit : lo ≤ i.val ∧ i.val < hi
    all_goals simp only [hit,and_self,ite_true,ite_false] at h
    all_goals first | simpa only [swap,hit,and_self,ite_true,ite_false] using congrArg Prod.fst h
                    | simpa only [swap,hit,and_self,ite_true,ite_false] using congrArg Prod.snd h
  dsimp only [cell]
  rw [helperField_halves c y,helperField_halves c s]
  change ext _ (FlatCoordinateLayout.index (Fin.addCases (field y.1) (field y.2)) j).val = _
  rw [halves.1,halves.2]
  exact remainderInterval_fullRead ordered (by omega) x (field s.1) (field s.2) j

/-- The two physical charts around one recursive transpose return the port
exchange in parent order. Both chart costs are independent of the child bill. -/
theorem flatIdleChild_charts [M8.Machine.Net] (c : PortCertificate) (hc : c.Checked)
    (lo hi : ℕ) (ordered : lo ≤ hi) (fits : hi ≤ 63) :
    ∃ (a k : ℕ) (entry exit : SharedBankSkeleton.Skeleton 1 prime), ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^128*W
      let child := phaseIntervalChild lo hi w W 64
      let size : volume prime child = V := intervalChild_volume ordered (by omega) w W
      ∃ A B : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage A = entry ∧ SharedBankSkeleton.ofStage B = exit ∧
        HasStackSeed A.metadata ∧ HasStackSeed B.metadata ∧
        A.cost+B.cost = a*V+k*(3808274*V+LeafCore.coreCost V w+1)+4 ∧
        ∀ x y, (∀ i, y (i.cast size) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows)
          (fun u => A.transform x (u.cast size)) i) →
          ∀ s j, let z := M8.Exchange.exchange (reduce (prime^w) (c.span lo hi)) s
            let cell := fun (u : Swap.Shear.State Axis (ZMod (prime^w))) => FlatCoordinateLayout.index (Sum.elim u.1 u.2 ∘ flatParentOrder) j
            B.transform y (cell z) = x (cell s) := by
  obtain ⟨a,k,m,enter⟩ := helperChart_owner c hc none false
  obtain ⟨b,l,p,leave⟩ := helperChart_owner c hc none true
  refine ⟨a+b,k+l,m,p,?_⟩
  intro w W hw hW V child size
  obtain ⟨A,fa,ca,sa,ra⟩ := enter w W hw hW
  obtain ⟨B,fb,cb,sb,rb⟩ := leave w W hw hW
  refine ⟨A,B,fa,fb,sa,sb,by rw [ca,cb]; dsimp only [V]; ring,?_⟩
  intro x y trans s j z cell
  let src := FlatCoordinateLayout.index (helperSlotField c none w s) j
  let dst := FlatCoordinateLayout.index (helperSlotField c none w z) j
  let input := fun u => A.transform x (Fin.cast size u)
  have result := helperInterval_read c hc ordered fits input s j
  have move := (ext_apply (Shared50RecursiveNodeRows.transpose (one_dvd child.rows) input)
    (dst.cast size.symm)).symm.trans (result.trans (ext_apply input (src.cast size.symm)))
  have cross := trans (dst.cast size.symm)
  simp only [Fin.cast_cast,Fin.cast_eq_self] at cross
  simp only [input,Fin.cast_cast,Fin.cast_eq_self] at move
  exact (rb y z j).trans (cross.trans (move.trans (ra x s j)))

end IntegerMultBounds.MathlibTM2.M6.BitNode
