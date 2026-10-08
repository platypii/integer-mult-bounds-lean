import IntegerMultBounds.Networks.AffineFieldProgram
import IntegerMultBounds.Networks.Shared50FiniteInterchange

/-! The actual complete shared interchange compiled to scalar ordered-affine
control. Its fixed rational schedule specializes at every prime-power width;
all diagonal scalings remain units because the same prime protects factor
inverses. The exact recursive interchange count remains s. No tape time claim. -/

namespace IntegerMultBounds.Networks.Shared50AffineControl

noncomputable section
open Swap.Shear
open ModularFrameSchedule
open AffineFieldProgram (Valid)
open Shared50ModularSchedule (Index)
open Shared50ModularControl (prime)

section Generic
variable {ι R : Type*} [Fintype ι] [LinearOrder ι] [CommRing R]

private theorem pivots_valid (L : List (ι × ι)) :
    ∀ op ∈ pivotsProgram (R := R) L, Valid op := by
  induction L with
  | nil => simp [pivotsProgram]
  | cons p rest ih => simpa [pivotsProgram,pivotProgram,Valid] using ih

private theorem shear_valid (E₁ E₁' E₂ E₂' : Matrix ι ι R) (L : List (ι × ι))
    (h₁ : LowerTriangular E₁) (h₁' : LowerTriangular E₁')
    (h₂ : LowerTriangular E₂) (h₂' : LowerTriangular E₂')
    (hu₁ : IsUnit E₁) (hu₁' : IsUnit E₁') (hu₂ : IsUnit E₂) (hu₂' : IsUnit E₂') :
    ∀ op ∈ shearProgram E₁ E₁' E₂ E₂' L, Valid op := by
  intro op hop
  simp only [shearProgram,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hop
  rcases hop with (h | h) | h
  · rcases h with rfl | rfl
    · exact ⟨h₂,hu₂⟩
    · exact ⟨h₁',hu₁'⟩
  · exact pivots_valid L op h
  · rcases h with rfl | rfl
    · exact ⟨h₁,hu₁⟩
    · exact ⟨h₂',hu₂'⟩

private theorem post_valid :
    ∀ op ∈ Shared50FiniteInterchange.postFields (ι := ι) (R := R), Valid op := by
  intro op hop
  obtain ⟨_,_,rfl⟩ := List.mem_map.mp hop
  trivial

private theorem pre_valid :
    ∀ op ∈ Shared50FiniteInterchange.preFields (ι := ι) (R := R), Valid op := by
  intro op hop
  simp only [Shared50FiniteInterchange.preFields,List.mem_append,List.mem_singleton] at hop
  rcases hop with h | rfl
  · exact post_valid op h
  · refine ⟨?_,by simp⟩
    intro i j hij
    simp [hij.ne]

omit [CommRing R] in
/-- Rational factor inverses prove invertibility of every actual transform. -/
theorem rational_factor_valid (e : Edge ι) :
    ∀ op ∈ ModularProgramShape.rationalProgram e, Valid op := by
  exact shear_valid _ _ _ _ _ (factors e).lower₁ (factors e).lower₁'
    (factors e).lower₂ (factors e).lower₂'
    (isUnit_iff_exists_inv.mpr ⟨_,(factors e).inv₁⟩)
    (isUnit_iff_exists_inv.mpr ⟨_,(factors e).inv₁'⟩)
    (isUnit_iff_exists_inv.mpr ⟨_,(factors e).inv₂⟩)
    (isUnit_iff_exists_inv.mpr ⟨_,(factors e).inv₂'⟩)

omit [CommRing R] in
/-- Protected inverse denominators make the reduced transforms invertible too. -/
theorem modular_factor_valid (e : Edge ι) {q : ℕ} (hq : q.Prime)
    (hd : ∀ d ∈ edgeDenominators e, d < q) (b : ℕ) :
    ∀ op ∈ ModularFrameSchedule.program (q ^ b) e, Valid op := by
  have hf : ∀ d ∈ Swap.Modular.factorizationDenominators (factors e), d < q :=
    fun d h => hd d (Finset.mem_union_right _ h)
  obtain ⟨_,h₁,h₁',h₂,h₂',hi₁,hi₁',hi₂,hi₂',_⟩ :=
    Swap.Modular.reduce_factorization_of_prime (factors e) hq hf b
  exact shear_valid _ _ _ _ _ h₁ h₁' h₂ h₂'
    (isUnit_iff_exists_inv.mpr ⟨_,hi₁⟩) (isUnit_iff_exists_inv.mpr ⟨_,hi₁'⟩)
    (isUnit_iff_exists_inv.mpr ⟨_,hi₂⟩) (isUnit_iff_exists_inv.mpr ⟨_,hi₂'⟩)

end Generic

/-- Every whole-group operation in the exact rational complete schedule is valid. -/
theorem rational_valid : ∀ p ∈ Shared50FiniteInterchange.rationalFieldPrograms, ∀ op ∈ p, Valid op := by
  intro p hp
  simp only [Shared50FiniteInterchange.rationalFieldPrograms,List.mem_append] at hp
  rcases hp with (hp | hp) | hp
  · obtain ⟨_,_,rfl⟩ := List.mem_map.mp hp
    exact pre_valid
  · obtain ⟨e,_,rfl⟩ := List.mem_map.mp hp
    exact rational_factor_valid e
  · obtain ⟨_,_,rfl⟩ := List.mem_map.mp hp
    exact post_valid

/-- All actual modular scalings have unit diagonals, including the negative
identity preceding the network; there is no additional unit hypothesis. -/
theorem modular_valid (b : ℕ) :
    ∀ p ∈ Shared50FiniteInterchange.fieldPrograms (prime ^ b), ∀ op ∈ p, Valid op := by
  intro p hp
  simp only [Shared50FiniteInterchange.fieldPrograms,List.mem_append] at hp
  rcases hp with (hp | hp) | hp
  · obtain ⟨_,_,rfl⟩ := List.mem_map.mp hp
    exact pre_valid
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
    exact modular_factor_valid e Shared50ModularControl.prime_prime
      (Shared50ModularControl.edge_bound Shared50ModularControl.prime_bound he) b
  · obtain ⟨_,_,rfl⟩ := List.mem_map.mp hp
    exact post_valid

/-- One fixed rational scalar schedule for each actual physical edge. -/
def rationalSchedules : List (List (AffineFieldProgram.Op Index ℚ)) :=
  Shared50FiniteInterchange.rationalFieldPrograms.map AffineFieldProgram.compile

/-- The identical compilation of the actual field programs at a chosen modulus. -/
def schedules (m : ℕ) : List (List (AffineFieldProgram.Op Index (ZMod m))) :=
  (Shared50FiniteInterchange.fieldPrograms m).map AffineFieldProgram.compile

/-- Targets, control indices, operation kinds, and list order are width-independent. -/
theorem schedules_eq_map (m : ℕ) :
    schedules m = rationalSchedules.map (List.map (AffineFieldProgram.mapOp (Swap.Modular.ratMod m))) := by
  simp only [schedules,rationalSchedules,Shared50FiniteInterchange.fieldPrograms_eq_map,List.map_map]
  apply List.map_congr_left
  intro p _
  have hm : ModularProgramShape.reduceOp (ι := Index) m = AffineFieldProgram.mapShear (Swap.Modular.ratMod m) := by
    funext op
    cases op <;> rfl
  simp only [Function.comp_def,hm]
  exact AffineFieldProgram.compile_map (Swap.Modular.ratMod m) p

theorem rational_schedules_legal :
    ∀ p ∈ rationalSchedules, ∀ op ∈ p, AffineFieldProgram.Legal op := by
  intro p hp
  obtain ⟨src,hsrc,rfl⟩ := List.mem_map.mp hp
  exact AffineFieldProgram.compile_legal src (rational_valid src hsrc)

theorem schedules_legal (b : ℕ) :
    ∀ p ∈ schedules (prime ^ b), ∀ op ∈ p, AffineFieldProgram.Legal op := by
  intro p hp
  obtain ⟨src,hsrc,rfl⟩ := List.mem_map.mp hp
  exact AffineFieldProgram.compile_legal src (modular_valid b src hsrc)

/-- Refinement preserves every actual edge's full address semantics. -/
theorem schedule_run (b : ℕ) (p : List (Swap.Shear.Op Index (ZMod (prime ^ b))))
    (hp : p ∈ Shared50FiniteInterchange.fieldPrograms (prime ^ b)) (s : State Index (ZMod (prime ^ b))) :
    AffineFieldProgram.run (AffineFieldProgram.compile p) s = Swap.Shear.run p s :=
  AffineFieldProgram.compile_run p (fun op hop => (modular_valid b p hp op hop).triangular) s

/-- The recursive interchange budget is unchanged by all scalar expansions. -/
theorem interchanges_exact (m : ℕ) :
    ((schedules m).map AffineFieldProgram.interchanges).sum = Shared50Parameters.s := by
  simp only [schedules,List.map_map,Function.comp_def,AffineFieldProgram.compile_interchanges]
  exact Shared50FiniteInterchange.interchanges_exact m

private theorem map_right_mem {α β γ : Type*} {R : α → β → Prop} {S : α → γ → Prop}
    {as : List α} {bs : List β} (h : List.Forall₂ R as bs) (f : β → γ)
    (hf : ∀ b ∈ bs, ∀ a, R a b → S a (f b)) : List.Forall₂ S as (bs.map f) := by
  induction h with
  | nil => exact .nil
  | @cons a b as bs hab hrest ih =>
    exact .cons (hf b (by simp) a hab) (ih (fun b hb => hf b (by simp [hb])))

/-- Refined scalar-address programs realize the same physical array edge. -/
def EdgeRealizes (m : ℕ)
    (edge : FramedCircuit.Frame (ZMod 2) (Shared50ModularExecution.Arrays m) ×
      FramedCircuit.Frame (ZMod 2) (Shared50ModularExecution.Arrays m))
    (p : List (AffineFieldProgram.Op Index (ZMod m))) : Prop :=
  ∃ move : Shared50ModularExecution.Address m ≃ Shared50ModularExecution.Address m,
    (∀ a, AffineFieldProgram.run p a = move a) ∧
    ∀ f, edge.2 (edge.1.symm f) = fun a => f (move.symm a)

/-- The complete actual physical trace is implemented by the refined schedules
in precisely the original edge order, with no assumed implementation contract. -/
theorem physical_realizes (b : ℕ) :
    List.Forall₂ (EdgeRealizes (prime ^ b))
      (FramedEdgeTrace.pairs (Shared50FiniteInterchange.program (prime ^ b)))
      (schedules (prime ^ b)) := by
  apply map_right_mem (Shared50FiniteInterchange.physical_realizes b) AffineFieldProgram.compile
  intro p hp edge hedge
  obtain ⟨move,hr,hframe⟩ := hedge
  exact ⟨move,fun s => (schedule_run b p hp s).trans (hr s),hframe⟩

end
end IntegerMultBounds.Networks.Shared50AffineControl
