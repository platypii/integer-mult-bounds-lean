module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyInverseWorkspace

/-! Execute the retained-family interior backend alongside the complete inverse
bank. All coupling caches and factor data remain outside its owned workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 263 Q A U}

noncomputable def placedFamilyInitializedInterior (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 263 Q A U :=
  embProg familyInverseReg Empty.elim (familyInitializedInterior (P₀ := Empty) hR hQ)

theorem placedFamilyInitializedInterior_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (v : HS 263 Q A U) (S : Stacks 263 A) (borrowed familyTail : List (Fin (A+4)))
    (h127 : (embStk couplingSourceReg (embStk familyInverseLegacyReg S)).R 127 = []) (h138 : (embStk couplingSourceReg (embStk familyInverseLegacyReg S)).R 138 = [])
    (ha : ((embStk couplingSourceReg (embStk familyInverseLegacyReg S)).R 141).length = a) (hb : ((embStk couplingSourceReg (embStk familyInverseLegacyReg S)).R 142).length = b)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l target rhsExp) (chirpLine s C)++borrowed) (embStk couplingSourceReg (embStk familyInverseLegacyReg S)))
    (hfamily : S.R 260 = weightKeyFamily (haloWeightKeyPages A (executionWidth p l target rhsExp)
      (executionPrecision p l target rhsExp) (2^15*p) s t u (PhaseCellBand.width p u) a b
      (haloLengthKeys s t (PhaseCellBand.width p u) a b))++familyTail)
    (hcache : ∀ i ∈ ([(256 : Fin 263),257,258,259,261,262] : List (Fin 263)), S.R i = [])
    :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    ∃ v' n, ∃ D : ZMod s → GaussianInt, v'.user = v.user ∧
      n ≤ familyInitializedInteriorCost A p l s t u target rhsExp a b ∧ (cstream A w (chirpLine s D)).length = s*w ∧
      Exec body (placedFamilyInitializedInterior hR hQ) (mk v S) n
        (mk v' {S with R := Function.update S.R 132 (cstream A w (chirpLine s D)++S.R 132)}) ∧
      (∀ k, ‖value q (D k)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
        (fun k => (value q (D k)).re) x (1/(2 : ℝ)^target) := by
  dsimp only
  obtain ⟨vi,n,D,hui,hn,hlen,hei,hnorm,herror⟩ := familyInitializedInterior_spec
    (body := fun p : Empty => nomatch p) hR hQ hA hp hst hu hαu hθ hgap hbudget hband has hbs hpad
    C hC x hx (embDn familyInverseReg v) (embStk familyInverseReg S) borrowed familyTail h127 h138 ha hb
    (by rw [familyInverse_legacy_view]; exact hready) hfamily (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact hcache 256 (by simp)
        | exact hcache 257 (by simp)
        | exact hcache 258 (by simp)
        | exact hcache 259 (by simp)
        | exact hcache 261 (by simp)) (hcache 262 (by simp))
  obtain ⟨v',hv,hu',he⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    familyInverseReg_injective (fun p => nomatch p) hei v rfl S rfl
  refine ⟨v',n,D,hu'.trans hui,hn,hlen,he.cast rfl ?_,hnorm,herror⟩
  apply congrArg (mk v')
  rw [embOvr_updR familyInverseReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
