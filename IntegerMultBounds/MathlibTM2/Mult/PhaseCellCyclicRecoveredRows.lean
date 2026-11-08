module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicNormalizedRecoveryAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTargetOwnedRecoveryJob

/-! Diagonal dominance supplies the principal reference rows for actual recovered
fields. Reverse chronological storage preserves their structural correspondence. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem cyclicRecoveredRows {s t p u l q a n : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2)
    (fields : Fin Fs.length → ZMod s → GaussianInt) (e : ℝ)
    (haccuracy : ∀ j : Fin Fs.length, ∀ x : ZMod s → ℝ,
      SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalVertices s a n) x
        (fun i => (value q (Fs.getD j.val (fun _ => 0) i)).re) →
      PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
        (fun i => (value q (fields j i)).re) x e) :
    ∃ xs : List (ZMod s → ℝ), xs.length = Fs.length ∧
      List.Forall₂ (fun F x => SchurDominance.Solves (realMatrix s t p u)
        (cyclicPrincipalVertices s a n) x (fun i => (value q (F i)).re)) Fs.reverse xs ∧
      (∀ x ∈ xs, ∀ i ∈ cyclicPrincipalVertices s a n, ‖x i‖ ≤ 4*(2 : ℝ)^(p+8)) ∧
      List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
        (fun i => (value q (D i)).re) x e) xs (List.ofFn fields).reverse := by
  have hp : 0 < p := by have h := axis.hp; omega
  have hμ : (0 : ℝ) < 1/(8*(p : ℝ)) := by positivity
  have hex (j : Fin Fs.length) : ∃ x, SchurDominance.Solves (realMatrix s t p u)
      (cyclicPrincipalVertices s a n) x (fun i => (value q (Fs.getD j.val (fun _ => 0) i)).re) :=
    SchurDominance.solves_exists _ _ _ hμ
      (SchurDominance.dominates_mono _ Finset.univ _ _ (Finset.subset_univ _) axis.hdom) _
  let refs := fun j : Fin Fs.length => Classical.choose (hex j)
  have hsol (j : Fin Fs.length) := Classical.choose_spec (hex j)
  have ofFnRel {β γ : Type} (R : β → γ → Prop) (f : Fin Fs.length → β) (g : Fin Fs.length → γ)
      (h : ∀ j, R (f j) (g j)) : List.Forall₂ R (List.ofFn f) (List.ofFn g) := by
    apply List.forall₂_of_length_eq_of_get (by simp)
    intro i hi hj
    have hi' : i < Fs.length := by simpa only [List.length_ofFn] using hi
    simpa only [List.get_eq_getElem,List.getElem_ofFn] using h ⟨i,hi'⟩
  refine ⟨(List.ofFn refs).reverse,by simp,?_,?_,?_⟩
  · apply List.forall₂_reverse_iff.mpr
    suffices hrows : List.Forall₂ (fun F x => SchurDominance.Solves (realMatrix s t p u)
        (cyclicPrincipalVertices s a n) x (fun i => (value q (F i)).re))
        (List.ofFn Fs.get) (List.ofFn refs) by
      simpa only [List.ofFn_get] using hrows
    apply ofFnRel
    intro j
    simpa only [refs,List.getD_eq_getElem _ _ j.isLt,List.get_eq_getElem] using hsol j
  · intro x hx i hi
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hx)
    apply cyclicPrincipal_round_magnitude hp axis.hdom (Fs.getD j.val (fun _ => 0)) ?_ (refs j) (hsol j) i hi
    intro k
    rw [List.getD_eq_getElem _ _ j.isLt]
    exact hF _ (List.getElem_mem j.isLt) k
  · apply List.forall₂_reverse_iff.mpr
    exact ofFnRel _ refs fields (fun j => haccuracy j (refs j) (hsol j))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
