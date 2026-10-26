module

public import IntegerMultBounds.NLogN.SchurBlockError
public import IntegerMultBounds.NLogN.SchurPerturbSolve

/-! Convert computed Schur residuals to boundary accuracy on the stated principal system. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.SchurDominance

open scoped BigOperators
open Finset

variable {ι : Type*} [DecidableEq ι]

theorem schur_residual_error (A : Matrix ι ι ℝ) (I B : Finset ι) (hIB : Disjoint I B)
    (μ : ℝ) (hμ : 0 < μ) (hA : DominatesOn A (I∪B) μ)
    (R : (ι → ℝ) → ι → ℝ) (hR : ∀ c, Solves A I (R c) c)
    (b x r X : ι → ℝ) (hx : Solves A (I∪B) x b)
    (E δ : ℝ) (hE : 0 ≤ E) (hδ : 0 ≤ δ)
    (hr : ∀ i ∈ B, |r i-residual A I R b i| ≤ E)
    (hX : ∀ i ∈ B, |schurOp A I B R X i-r i| ≤ δ) :
    ∀ i ∈ B, |X i-x i| ≤ (δ+E)/μ := by
  have hAI := dominates_mono A _ I μ subset_union_left hA
  have hxS := (exact_schur A I B hIB μ hμ hA R hR b x hx).2
  let v := fun i => schurOp A I B R X i-residual A I R b i
  have hv : ∀ i ∈ B, |v i| ≤ δ+E := by
    intro i hi
    calc
      _ = |(schurOp A I B R X i-r i)+(r i-residual A I R b i)| := by dsimp [v]; congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add (hX i hi) (hr i hi))
  have hdiff : ∀ i ∈ B, schurOp A I B R (X-x) i = v i := by
    intro i hi
    rw [schurOp_sub A I B μ hμ hAI R hR,hxS i hi]
  intro i hi
  exact schur_bound A I B hIB μ hμ hA R hR v (X-x) hdiff (δ+E) (by positivity) hv i hi

theorem approximate_solves_bound (A : Matrix ι ι ℝ) (S : Finset ι) (μ : ℝ) (hμ : 0 < μ)
    (hA : DominatesOn A S μ) (X r : ι → ℝ) (ρ δ : ℝ)
    (hr : ∀ i ∈ S, |r i| ≤ ρ) (hX : ∀ i ∈ S, |(∑ j ∈ S, A i j*X j)-r i| ≤ δ) :
    ∀ i ∈ S, |X i| ≤ (ρ+δ)/μ := by
  apply solves_bound A S μ hμ hA X (fun i => ∑ j ∈ S, A i j*X j) (fun _ _ => rfl) (ρ+δ)
  intro i hi
  calc
    _ = |((∑ j ∈ S, A i j*X j)-r i)+r i| := by congr 1; ring
    _ ≤ δ+ρ := (abs_add_le _ _).trans (add_le_add (hX i hi) (hr i hi))
    _ = _ := by ring

theorem computed_schur_error (A : Matrix ι ι ℝ) (I B : Finset ι) (hIB : Disjoint I B)
    (μ m : ℝ) (hμ : 0 < μ) (hA : DominatesOn A (I∪B) μ)
    (R : (ι → ℝ) → ι → ℝ) (hR : ∀ c, Solves A I (R c) c)
    (hS : StageInv (run A (I∪B) I.toList).1 B μ m)
    (Sh : Matrix ι ι ℝ) (εA : ℝ) (hεA : 0 ≤ εA) (hsmall : εA < μ)
    (hSh : ∀ i ∈ B, ∑ j ∈ B, |Sh i j-(run A (I∪B) I.toList).1 i j| ≤ εA)
    (b x r X : ι → ℝ) (hx : Solves A (I∪B) x b)
    (ρ δ E : ℝ) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) (hE : 0 ≤ E)
    (hr : ∀ i ∈ B, |r i| ≤ ρ) (hrE : ∀ i ∈ B, |r i-residual A I R b i| ≤ E)
    (hX : ∀ i ∈ B, |(∑ j ∈ B, Sh i j*X j)-r i| ≤ δ) :
    (∀ i ∈ B, |X i| ≤ (ρ+δ)/(μ-εA)) ∧
      ∀ i ∈ B, |X i-x i| ≤ (δ+εA*((ρ+δ)/(μ-εA))+E)/μ := by
  have hμ' : 0 < μ-εA := by linarith
  have hShInv := stageInv_perturb _ Sh B μ m εA hS hSh
  have hbound := approximate_solves_bound Sh B (μ-εA) hμ' hShInv.1 X r ρ δ hr hX
  refine ⟨hbound,?_⟩
  apply schur_residual_error A I B hIB μ hμ hA R hR b x r X hx E
    (δ+εA*((ρ+δ)/(μ-εA))) hE (by positivity) hrE
  intro i hi
  have hrow := row_bound (fun i j => Sh i j-(run A (I∪B) I.toList).1 i j) B X i εA
    ((ρ+δ)/(μ-εA)) (hSh i hi) (by positivity) hbound
  have hident := schurOp_eq_run A I B hIB μ hμ hA R hR I.toList (toList_toFinset I) X i hi
  simp only [sub_mul,sum_sub_distrib] at hrow
  rw [hident]
  calc
    _ = |((∑ j ∈ B, (run A (I∪B) I.toList).1 i j*X j)-(∑ j ∈ B, Sh i j*X j))+
        ((∑ j ∈ B, Sh i j*X j)-r i)| := by congr 1; ring
    _ ≤ εA*((ρ+δ)/(μ-εA))+δ := (abs_add_le _ _).trans
      (add_le_add (by simpa only [abs_sub_comm] using hrow) (hX i hi))
    _ = _ := by ring

end IntegerMultBounds.NLogN.SchurDominance
