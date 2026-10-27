module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilySolveHaloInterior
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundedAmbient

/-! The executed interior result has a bounded integer field and exact normalized readout. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 151 Q A U}

theorem familySolveHaloInterior_bounded_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l s t p u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (v : HS 151 Q A U) (S : Stacks 151 A) (borrowed outputTail familyTail : List (Fin (A+4)))
    (E₀ : ZMod s → GaussianInt)
    (hE₀ : ∀ k, ‖value (executionPrecision p l target rhsExp) (E₀ k)‖ ≤
      (2 : ℝ)^interiorOutputExponent p l target rhsExp)
    (hdst : S.R 132 = cstream A (executionWidth p l target rhsExp) (chirpLine s E₀)++outputTail)
    (h127 : S.R 127 = []) (h138 : S.R 138 = [])
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l target rhsExp) (chirpLine s C)++borrowed) (weightFamilyLegacyBank S))
    (hfamily : S.R 148 = weightKeyFamily (haloWeightKeyPages A (executionWidth p l target rhsExp)
      (executionPrecision p l target rhsExp) (2^15*p) s t u (PhaseCellBand.width p u) a b
      (haloLengthKeys s t (PhaseCellBand.width p u) a b))++familyTail)
    (hcache : ∀ i ∈ ([(144 : Fin 151),145,146,147,149] : List (Fin 151)), S.R i = [])
    (h150 : S.R 150 = []) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    ∃ v' n, ∃ D : ZMod s → GaussianInt, v'.user = v.user ∧
      n ≤ familySolveHaloInteriorCost A p l s t u target rhsExp a b ∧ (cstream A w (chirpLine s D)).length = s*w ∧
      Exec body (familySolveHaloInterior hR hQ) (mk v S) n
        (mk v' { S with R := Function.update S.R 132 (cstream A w (chirpLine s D)++outputTail) }) ∧
      (∀ k, ‖value q (D k)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
        (fun k => (value q (D k)).re) x (1/(2 : ℝ)^target) := by
  dsimp only
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  obtain ⟨v',n,E',hu,hn,hE',he,herror,hbounded⟩ := familySolveHaloInterior_spec (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hband has hbs hpad C hC x hx v S
    borrowed (cstream A w (chirpLine s E₀)) outputTail familyTail (by simp [w]) hdst
    h127 h138 haMaster hbMaster hready hfamily hcache h150
  have hE₀' : EncodedRange A w q (interiorOutputExponent p l target rhsExp) (cstream A w (chirpLine s E₀)) := by
    refine ⟨chirpLine s E₀,rfl,?_⟩
    intro z hz
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp hz
    exact hE₀ (k : ZMod s)
  have hw : 0 < w := by dsimp [w,executionWidth]; omega
  obtain ⟨D,hD,hDnorm⟩ := encodedRange_ambient (s := s) hw E' hE' (hbounded hE₀')
  have hfit : ∀ k, Fits w (D k) := fun k =>
    fits_of_value_power (interiorOutput_width p l target rhsExp) (D k) (hDnorm k)
  refine ⟨v',n,D,hu,hn,by simp,?_,hDnorm,?_⟩
  · simpa only [hD] using he
  · intro k hk
    have hh := herror k hk
    rw [hD,publishedCellRead_encodedField (by omega) hw D outputTail hfit k] at hh
    exact hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
