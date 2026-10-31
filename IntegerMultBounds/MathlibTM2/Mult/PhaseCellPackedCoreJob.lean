module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedJob
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedWindowGeometry
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDerivedInverseRoundBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientAccuracy

/-! Construct a proper-core job from mathematical factory bounds. Scalar sizing,
coefficient fits, crop geometry and exact reference solutions are derived. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
namespace PackedNormalizedJob
variable {A s : ℕ} [NeZero s]

noncomputable def ofCore (p u l targetOut t width k V W : ℕ) (α gap : ℝ)
    (C : ZMod s → GaussianInt) (Fs : List (ZMod s → GaussianInt))
    (bounds : PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u)
      (target := targetOut+1) (rhsExp := 2)
      (a := (coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p targetOut)).1)
      (b := (coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p targetOut)).2) (V := V) α gap C)
    (hW : 2*(executionPrecision p l (boundaryHaloTarget p u (boundaryRecoveryTarget p (targetOut+1)) 2
      (haloBoundary s t (PhaseCellBand.width p u)
        (coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p targetOut)).1
        (coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p targetOut)).2).card) 2)+8 ≤ W)
    (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1) : PackedNormalizedJob A s := by
  let endpoints := coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p targetOut)
  let q := executionPrecision p l (boundaryHaloTarget p u (boundaryRecoveryTarget p (targetOut+1)) 2
    (haloBoundary s t (PhaseCellBand.width p u) endpoints.1 endpoints.2).card) 2
  have hne : coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p targetOut) ≠ (0,s) := by
    intro he
    have hsep := bounds.hsep
    rw [he] at hsep
    simp only [Nat.sub_zero] at hsep
    have hband := PhaseCellBand.width_pos p u
    omega
  have hp : 0 < p := by have := bounds.hp; omega
  have hμ : 0 < 1/(8*(p : ℝ)) := by positivity
  let Y : (ZMod s → GaussianInt) → ZMod s → ℝ := fun F => Classical.choose
    (SchurDominance.solves_exists (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))) hμ bounds.hdom
      (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re))
  have hY (F : ZMod s → GaussianInt) : SchurDominance.Solves (realMatrix s t p u) Finset.univ (Y F)
      (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re) := by
    exact Classical.choose_spec (SchurDominance.solves_exists (realMatrix s t p u) Finset.univ
      (1/(8*(p : ℝ))) hμ bounds.hdom (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re))
  have hq : p+1 ≤ q := by
    dsimp [q,executionPrecision,executionExponent,inputExponent,sourceExponent]
    omega
  have hcoeffWidth : q+(8*p+1)+2 ≤ 2*q+8 := by
    dsimp [q,executionPrecision,executionExponent,inputExponent,sourceExponent]
    omega
  have hθ : 0 < (t : ℝ)/s-1 := lt_of_lt_of_le (by positivity : (0 : ℝ) < 1/(4*(p : ℝ))) bounds.hθ
  have hgeometry := PhaseCellInterface.generatedWindow_interval_geometry (s := s) width p u targetOut k hne
  have ha := hgeometry.1
  have hb := hgeometry.2.1
  have hl := hgeometry.2.2.1
  have hr := hgeometry.2.2.2.1
  have hhalo := hgeometry.2.2.2.2
  have hrooms := inverseCallerWordWidth_fits_cuts p u l targetOut s t endpoints.1 endpoints.2
  have hbandRoom := hrooms.1
  have hgeometryRoom := hrooms.2.1
  have hprecisionRoom := hrooms.2.2
  have hsFit : s < 2^inverseCallerWordWidth p u l targetOut s t := by
    have htFit : t < 2^inverseCallerWordWidth p u l targetOut s t := by
      nlinarith only [hgeometryRoom,Nat.zero_le (t*t)]
    exact bounds.hst.trans htFit
  have hscalars := inverseInputScalars_fit (A := A) bounds.hst bounds.has bounds.hbs
    hbandRoom hgeometryRoom hprecisionRoom
  refine {
    p := p
    u := u
    l := l
    targetOut := targetOut
    t := t
    a := endpoints.1
    b := endpoints.2
    V := V
    Bcore := inverseCallerWordWidth p u l targetOut s t
    q := q
    W := W
    coreWidth := width
    k := k
    radius := localityDepth p targetOut*PhaseCellBand.width p u
    localityTarget := targetOut
    α := α
    gap := gap
    C := C
    Fs := Fs
    Y := Y
    bounds := bounds
    hsCore := hsFit
    hqSizing := rfl
    hpq := hq
    hW := hW
    hF := hF
    haEq := ha
    hbEq := hb
    hleft := hl
    hright := hr
    hcoeff := ?_
    hvaluesFit := ?_
    hbandRoom := hbandRoom
    hgeometryRoom := hgeometryRoom
    hprecisionRoom := hprecisionRoom
    hhalo := hhalo
    hY := fun F _ => hY F }
  · intro j _
    exact couplingCoefficientWords_fits hp (NeZero.pos s) bounds.hst bounds.hαu hθ bounds.hgap bounds.hbudget hcoeffWidth
  · intro i
    have hval : ![p,u,l,targetOut,s,t,endpoints.1,endpoints.2] i =
        (inverseInputScalars (A := A) p u l targetOut s t endpoints.1 endpoints.2).val (Fin.castLE (by decide : 8 ≤ 25) i) := by
      fin_cases i <;> rfl
    rw [hval]
    exact hscalars _
theorem ofCore_fields (p u l targetOut t width k V W : ℕ) (α gap : ℝ)
    (C : ZMod s → GaussianInt) (Fs : List (ZMod s → GaussianInt))
    (bounds : PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u)
      (target := targetOut+1) (rhsExp := 2)
      (a := (coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p targetOut)).1)
      (b := (coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p targetOut)).2) (V := V) α gap C)
    (hW : 2*(executionPrecision p l (boundaryHaloTarget p u (boundaryRecoveryTarget p (targetOut+1)) 2
      (haloBoundary s t (PhaseCellBand.width p u)
        (coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p targetOut)).1
        (coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p targetOut)).2).card) 2)+8 ≤ W)
    (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1) :
    let r := ofCore (A := A) p u l targetOut t width k V W α gap C Fs bounds hW hF
    r.coreWidth = width ∧ r.k = k ∧ r.radius = localityDepth p targetOut*PhaseCellBand.width p u ∧
      r.W = W ∧ r.Fs = Fs ∧ r.localityTarget = targetOut := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end PackedNormalizedJob
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
