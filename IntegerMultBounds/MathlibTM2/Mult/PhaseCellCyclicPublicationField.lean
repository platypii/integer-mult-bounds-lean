module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComponentInputs
public import IntegerMultBounds.NLogN.PhaseCellCyclicPrincipalGeometry
public import IntegerMultBounds.NLogN.SchurBlockSolve

/-! Two existing publication merges assemble the cyclic recovery field. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

noncomputable def cyclicPublicationField {s : ℕ} [NeZero s] (t band a n : ℕ)
    (D E Y : ZMod s → GaussianInt) (i : ZMod s) : GaussianInt :=
  realPartWord (publicationField t band a (a+min n (s-a)) D
    (fun j => realPartWord (publicationField t band 0 (n-min n (s-a)) E Y j)) i)

theorem cyclicPublicationField_value {s : ℕ} [NeZero s] (q t band a n : ℕ)
    (D E Y : ZMod s → GaussianInt) (i : ZMod s) :
    (value q (cyclicPublicationField t band a n D E Y i)).re =
      SchurDominance.glue (cyclicPrincipalInterior s t band a n)
        (fun j => if j ∈ haloInterior s t band a (a+min n (s-a)) then (value q (D j)).re else (value q (E j)).re)
        (fun j => (value q (Y j)).re) i := by
  by_cases hleft : i ∈ haloInterior s t band a (a+min n (s-a)) <;>
    by_cases hright : i ∈ haloInterior s t band 0 (n-min n (s-a)) <;>
    simp [cyclicPublicationField,publicationField,SchurDominance.glue,
      cyclicPrincipalInterior,hleft,hright,value_realPartWord_re]

theorem cyclicPublicationField_accuracy {s : ℕ} [NeZero s] (q t band a n : ℕ)
    (D E Y : ZMod s → GaussianInt) (x : ZMod s → ℝ) (epsilon : ℝ)
    (h : PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
      (SchurDominance.glue (cyclicPrincipalInterior s t band a n)
        (fun i => if i ∈ haloInterior s t band a (a+min n (s-a)) then (value q (D i)).re else (value q (E i)).re)
        (fun i => (value q (Y i)).re)) x epsilon) :
    PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
      (fun i => (value q (cyclicPublicationField t band a n D E Y i)).re) x epsilon := by
  intro i hi
  dsimp only
  rw [cyclicPublicationField_value]
  exact h i hi

@[simp] theorem cyclicPublicationField_im {s : ℕ} [NeZero s] (t band a n : ℕ)
    (D E Y : ZMod s → GaussianInt) (i : ZMod s) :
    (cyclicPublicationField t band a n D E Y i).im = 0 := rfl

theorem cyclicPublicationField_off {s : ℕ} [NeZero s] (t band a n : ℕ)
    (D E Y : ZMod s → GaussianInt)
    (hY : ∀ i ∉ cyclicPrincipalVertices s a n, Y i = 0)
    (i : ZMod s) (hi : i ∉ cyclicPrincipalVertices s a n) :
    cyclicPublicationField t band a n D E Y i = 0 := by
  have hleft : i ∉ haloInterior s t band a (a+min n (s-a)) :=
    fun h => hi (Finset.mem_union_left _ (haloInterior_subset s t band a _ h))
  have hright : i ∉ haloInterior s t band 0 (n-min n (s-a)) :=
    fun h => hi (Finset.mem_union_right _ (haloInterior_subset s t band 0 _ h))
  apply Zsqrtd.ext <;> simp [cyclicPublicationField,publicationField,hleft,hright,hY i hi,realPartWord]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
