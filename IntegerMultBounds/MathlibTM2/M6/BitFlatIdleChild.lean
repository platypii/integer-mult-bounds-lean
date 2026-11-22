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

/-- On the actual parent word the scheduled exchange swaps the shifted
interval in both halves, leaving the spectator in place. -/
theorem parentInterval_read {w W : ℕ} (c : PortCertificate) (e : ℕ × ℕ)
    (member : e ∈ BitHosting.remainderIntervals)
    (x : Fin (volume prime (phaseIntervalChild (e.1+1) (e.2+1) w W 64)) → ZMod 2)
    (s : Swap.Shear.State Axis (ZMod (prime^w))) (j : Fin W) :
    let y := M8.Exchange.exchange (reduce (prime^w) (c.span e.1 e.2)) s
    let cell := fun (v : Swap.Shear.State Axis (ZMod (prime^w))) =>
      FlatCoordinateLayout.index (Fin.addCases (v.1 ∘ stageAxis.symm) (v.2 ∘ stageAxis.symm)) j
    ext (Shared50RecursiveNodeRows.transpose (one_dvd _) x) (cell y).val = ext x (cell s).val := by
  intro y cell
  let hit := fun a => e.1+1 ≤ axisIndex a ∧ axisIndex a < e.2+1
  have reduced : reduce (prime^w) (c.span e.1 e.2) =
      diagonal (fun a => if hit a then (1 : ZMod (prime^w)) else 0) := by
    rw [BitHosting.remainder_parent_span c e member]
    ext a b
    simp only [reduce, Matrix.map_apply, diagonal_apply, hit]
    split_ifs <;> simp [ratMod_zero, ratMod_one]
  have index : ∀ a : Axis, (stageAxis a).val = axisIndex a := by decide +kernel
  have pair (i : Fin 64) :
      (y.1 (stageAxis.symm i), y.2 (stageAxis.symm i)) =
      if e.1+1 ≤ i.val ∧ i.val < e.2+1 then (s.2 (stageAxis.symm i), s.1 (stageAxis.symm i))
      else (s.1 (stageAxis.symm i), s.2 (stageAxis.symm i)) := by
    have idx := index (stageAxis.symm i)
    rw [Equiv.apply_symm_apply] at idx
    by_cases h : e.1 < i.val ∧ i.val ≤ e.2 <;>
      simp [y, M8.Exchange.exchange, reduced, Matrix.sub_mulVec, Matrix.mulVec_diagonal, hit, ← idx, h]
  obtain ⟨ordered,fits,_⟩ := BitHosting.remainder_counts e member
  have read := remainderInterval_fullRead (Nat.succ_le_succ ordered) (Nat.succ_le_succ fits) x
    (s.1 ∘ stageAxis.symm) (s.2 ∘ stageAxis.symm) j
  let swap := fun (a b : Axis → ZMod (prime^w)) (i : Fin 64) =>
    if e.1+1 ≤ i.val ∧ i.val < e.2+1 then b (stageAxis.symm i) else a (stageAxis.symm i)
  have halves : y.1 ∘ stageAxis.symm = swap s.1 s.2 ∧ y.2 ∘ stageAxis.symm = swap s.2 s.1 := by
    constructor <;> funext i
    all_goals have eq := pair i
    all_goals by_cases h : e.1+1 ≤ i.val ∧ i.val < e.2+1
    all_goals simp only [h,and_self,ite_true,ite_false] at eq
    all_goals first | simpa only [swap,h,and_self,ite_true,ite_false,Function.comp_apply] using congrArg Prod.fst eq
                    | simpa only [swap,h,and_self,ite_true,ite_false,Function.comp_apply] using congrArg Prod.snd eq
  dsimp only [cell]
  rw [halves.1,halves.2]
  exact read

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
