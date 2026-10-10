import IntegerMultBounds.Machine.CompactComplexSourceReadySinkCorrections
import IntegerMultBounds.Machine.NativeUniformPolynomialRotationPath

/-! The literal physical sink-correction family preserves the original common
signed widths and numerical grid. Every signed guard comes from the genuine
recursive dependency Path; the corrections consume no denominator growth. -/
namespace IntegerMultBounds.Machine.CompactComplexSinkCorrectionGrid
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Width Grid)
open CompactComplexEndpointRoleExchange (Wire)
open CompactComplexSourceReadySinkCorrections (signed phased negated data)
variable {sh : Shape} {rows ell q left k levels frames returned : ℕ}

theorem signed_width (v : Stage sh) (hslots : v.slots=NativeEndpointCharacterRoles.arity)
    (p : ℕ) (before : Wire → Array sh rows ell) (hw : ∀ a,Width sh rows ell q (before a)) :
    ∀ a,Width sh rows ell q (signed v hslots ell p before a) := by
  intro a i
  rcases a with a | a | a
  · exact hw _ _
  · exact NativeEndpointCharacterPath.width true v hslots ell p before a _ (hw _) i
  · exact hw _ _

theorem uniform_width (negative : Bool) (v : Stage sh)
    (before : Wire → Array sh rows ell) (hw : ∀ a,Width sh rows ell q (before a)) :
    ∀ a,Width sh rows ell q (NativeUniformPolynomialRotationNamedBank.data negative v before a) := by
  intro a i
  cases negative <;> rcases a with a | a | a
  all_goals first | exact hw _ _ | exact UnitPhasePolynomialArray.result_width _ _ _ (hw _) i

theorem signed_grid (v : Stage sh) (hslots : v.slots=NativeEndpointCharacterRoles.arity)
    (metadataP : ℕ) (before : Wire → Array sh rows ell)
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (p C n : ℕ) (hp : p≤q)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (hw : ∀ a,Width sh rows ell q (before a))
    (hg : ∀ a,Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) (before a)) :
    ∀ a,Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned))
      (signed v hslots ell metadataP before a) := by
  intro a
  rcases a with a | a | a
  · exact hg _
  · exact NativeEndpointCharacterPath.grid_from_path true v hslots ell metadataP before a
      path p C n hp hchunk (hw _) (hg _)
  · exact hg _

theorem uniform_grid (negative : Bool) (v : Stage sh) (before : Wire → Array sh rows ell)
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (p C n : ℕ) (hp : p≤q)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (hw : ∀ a,Width sh rows ell q (before a))
    (hg : ∀ a,Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) (before a)) :
    ∀ a,Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned))
      (NativeUniformPolynomialRotationNamedBank.data negative v before a) := by
  intro a
  cases negative
  · rcases a with a | a | a
    · exact hg _
    · exact NativeUniformPolynomialRotationPath.rotation_grid v.f path p C n hp hchunk
        (before (Sum.inr (Sum.inl a))) (hw _) (hg _)
    · exact hg _
  · rcases a with a | a | a
    · exact NativeUniformPolynomialRotationPath.negative_grid path p C n hp hchunk
        (before (Sum.inl a)) (hw _) (hg _)
    · exact hg _
    · exact hg _

/-- The exact family returned by the physical sequence retains all widths. -/
theorem width (v : Stage sh) (hslots : v.slots=NativeEndpointCharacterRoles.arity)
    (p : ℕ) (before : Wire → Array sh rows ell) (hw : ∀ a,Width sh rows ell q (before a)) :
    ∀ a,Width sh rows ell q (data v hslots ell p before a) := by
  have hw1 := signed_width v hslots p before hw
  have hw2 := uniform_width false v (signed v hslots ell p before) hw1
  have hw3 := uniform_width true v (phased v hslots ell p before) hw2
  exact fun a => hw3 (Networks.ComplexFramedExecution.route a)

/-- Sink signs, runtime Y phase, X negation and full exchange preserve the
same original Path grid, without a new reserve or numerical safety premise. -/
theorem grid (v : Stage sh) (hslots : v.slots=NativeEndpointCharacterRoles.arity)
    (metadataP : ℕ) (before : Wire → Array sh rows ell)
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (p C n : ℕ) (hp : p≤q)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (hw : ∀ a,Width sh rows ell q (before a))
    (hg : ∀ a,Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) (before a)) :
    ∀ a,Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned))
      (data v hslots ell metadataP before a) := by
  have hw1 := signed_width v hslots metadataP before hw
  have hg1 := signed_grid v hslots metadataP before path p C n hp hchunk hw hg
  have hw2 := uniform_width false v (signed v hslots ell metadataP before) hw1
  have hg2 := uniform_grid false v (signed v hslots ell metadataP before)
    path p C n hp hchunk hw1 hg1
  have hg3 := uniform_grid true v (phased v hslots ell metadataP before)
    path p C n hp hchunk hw2 hg2
  exact fun a => hg3 (Networks.ComplexFramedExecution.route a)

/-- A genuine coarser target-grid certificate survives signs even when the
stored words still use the larger current denominator. -/
theorem signed_coarse_grid (v : Stage sh) (hslots : v.slots=NativeEndpointCharacterRoles.arity)
    (metadataP : ℕ) (before : Wire → Array sh rows ell)
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (p C n target M : ℕ) (hp : p≤q)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (hw : ∀ a,Width sh rows ell q (before a))
    (hg : ∀ a,Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) (before a))
    (hc : ∀ a i,Networks.GaussianPrecision.BoundedGrid target M
      (CompactSpectatorInheritedGrid.decoded sh rows ell q n (before a) i)) :
    ∀ a i,Networks.GaussianPrecision.BoundedGrid target M
      (CompactSpectatorInheritedGrid.decoded sh rows ell q n
        (signed v hslots ell metadataP before a) i) := by
  intro a i
  rcases a with a | a | a
  · exact hc _ _
  · change Networks.GaussianPrecision.BoundedGrid target M
      (CompactSpectatorInheritedGrid.decoded sh rows ell q n
        (NativeEndpointCharacterNamedBank.result true v hslots ell metadataP before a) i)
    rw [NativeEndpointCharacterPath.decoded_from_path true v hslots ell metadataP before a
      path p C n hp hchunk (hw _) (hg _)]
    exact Networks.GaussianPrecision.bounded_I_pow_mul _ (hc _ _)
  · exact hc _ _

theorem uniform_coarse_grid (negative : Bool) (v : Stage sh)
    (before : Wire → Array sh rows ell)
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (p C n target M : ℕ) (hp : p≤q)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (hw : ∀ a,Width sh rows ell q (before a))
    (hg : ∀ a,Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) (before a))
    (hc : ∀ a i,Networks.GaussianPrecision.BoundedGrid target M
      (CompactSpectatorInheritedGrid.decoded sh rows ell q n (before a) i)) :
    ∀ a i,Networks.GaussianPrecision.BoundedGrid target M
      (CompactSpectatorInheritedGrid.decoded sh rows ell q n
        (NativeUniformPolynomialRotationNamedBank.data negative v before a) i) := by
  intro a i
  cases negative
  · rcases a with a | a | a
    · exact hc _ _
    · change Networks.GaussianPrecision.BoundedGrid target M
        (CompactSpectatorInheritedGrid.decoded sh rows ell q n
          (NativeUniformPolynomialRotationSemantics.array v.f (before (Sum.inr (Sum.inl a)))) i)
      rw [NativeUniformPolynomialRotationPath.rotation_decoded v.f path p C n hp hchunk
        (before (Sum.inr (Sum.inl a))) (hw _) (hg _)]
      exact Networks.GaussianPrecision.bounded_I_pow_mul _ (hc _ _)
    · exact hc _ _
  · rcases a with a | a | a
    · change Networks.GaussianPrecision.BoundedGrid target M
        (CompactSpectatorInheritedGrid.decoded sh rows ell q n
          (UnitPhasePolynomialArray.result 2 (before (Sum.inl a))) i)
      rw [NativeUniformPolynomialRotationPath.negative_decoded path p C n hp hchunk
        (before (Sum.inl a)) (hw _) (hg _)]
      exact Networks.GaussianPrecision.bounded_neg (hc _ _)
    · exact hc _ _
    · exact hc _ _

/-- The exact physical output retains the coarser certificate required by
actual signed contraction; the stored live denominator is unchanged. -/
theorem coarse_grid (v : Stage sh) (hslots : v.slots=NativeEndpointCharacterRoles.arity)
    (metadataP : ℕ) (before : Wire → Array sh rows ell)
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (p C n target M : ℕ) (hp : p≤q)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (hw : ∀ a,Width sh rows ell q (before a))
    (hg : ∀ a,Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) (before a))
    (hc : ∀ a i,Networks.GaussianPrecision.BoundedGrid target M
      (CompactSpectatorInheritedGrid.decoded sh rows ell q n (before a) i)) :
    ∀ a i,Networks.GaussianPrecision.BoundedGrid target M
      (CompactSpectatorInheritedGrid.decoded sh rows ell q n
        (data v hslots ell metadataP before a) i) := by
  have hw1 := signed_width v hslots metadataP before hw
  have hg1 := signed_grid v hslots metadataP before path p C n hp hchunk hw hg
  have hc1 := signed_coarse_grid v hslots metadataP before path p C n target M hp hchunk hw hg hc
  have hw2 := uniform_width false v (signed v hslots ell metadataP before) hw1
  have hg2 := uniform_grid false v (signed v hslots ell metadataP before)
    path p C n hp hchunk hw1 hg1
  have hc2 := uniform_coarse_grid false v (signed v hslots ell metadataP before)
    path p C n target M hp hchunk hw1 hg1 hc1
  have hc3 := uniform_coarse_grid true v (phased v hslots ell metadataP before)
    path p C n target M hp hchunk hw2 hg2 hc2
  exact fun a i => hc3 (Networks.ComplexFramedExecution.route a) i

end
end IntegerMultBounds.Machine.CompactComplexSinkCorrectionGrid
