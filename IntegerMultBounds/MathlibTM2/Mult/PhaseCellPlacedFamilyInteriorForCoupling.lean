module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedFamilyInitializedInterior
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallCouplingHeaders

/-! The retained-family interior pass produces the ordinary cached-coupling
ABI while keeping both coupling pages and the numerical weight family disjoint. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 263 Q A U}

def familyCouplingSourceReg (i : Fin 144) : Fin 263 := familyInverseLegacyReg (couplingSourceReg i)

theorem familyCouplingSourceReg_injective : Function.Injective familyCouplingSourceReg :=
  familyInverseLegacyReg_injective.comp couplingSourceReg_injective

theorem familyCouplingSourceReg_off (i : Fin 7) : ∀ j, familyCouplingSourceReg j ≠ familyInversePort i :=
  fun j => familyInverseLegacyReg_off i (couplingSourceReg j)

noncomputable def placedFamilyInteriorForCoupling (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 263 Q A U :=
  .seq (placedFamilyInitializedInterior hR hQ)
    (embProg familyCouplingSourceReg Empty.elim (installCouplingHeaders (P₀ := Empty)))

theorem placedFamilyInteriorForCoupling_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (h127 : (embStk familyCouplingSourceReg S).R 127 = []) (h138 : (embStk familyCouplingSourceReg S).R 138 = [])
    (ha : ((embStk familyCouplingSourceReg S).R 141).length = a)
    (hb : ((embStk familyCouplingSourceReg S).R 142).length = b)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l target rhsExp) (chirpLine s C)++borrowed) (embStk familyCouplingSourceReg S))
    (hfamily : S.R 260 = weightKeyFamily (haloWeightKeyPages A (executionWidth p l target rhsExp)
      (executionPrecision p l target rhsExp) (2^15*p) s t u (PhaseCellBand.width p u) a b
      (haloLengthKeys s t (PhaseCellBand.width p u) a b))++familyTail)
    (hcache : ∀ i ∈ ([(256 : Fin 263),257,258,259,261,262] : List (Fin 263)), S.R i = []) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let band := PhaseCellBand.width p u
    ∃ v' n, ∃ D : ZMod s → GaussianInt,
      let T : Stacks 263 A := {S with R := Function.update S.R 132 (cstream A w (chirpLine s D)++S.R 132)}
      let H : Stacks 144 A := {embStk familyCouplingSourceReg T with R :=
        (couplingHeadersR (2^15*p) q s t u band a b (embStk familyCouplingSourceReg T).R)}
      let G := embOvr familyCouplingSourceReg H.get T
      v'.user = v.user ∧ n ≤ familyInitializedInteriorCost A p l s t u target rhsExp a b+
        installCouplingHeadersCost (2^15*p) q s t u band a b ∧
      Exec body (placedFamilyInteriorForCoupling hR hQ) (mk v S) n (mk v' G) ∧
      CouplingReady (2^15*p) q w s t u band a b (cstream A w (chirpLine s C)++borrowed)
        (embStk groupReg (embStk familyCouplingSourceReg G)) ∧
      (∀ i : Fin 7, G.L (familyInversePort i) = S.L (familyInversePort i) ∧
        G.R (familyInversePort i) = S.R (familyInversePort i)) ∧
      (∀ k, ‖value q (D k)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t band a b)
        (fun k => (value q (D k)).re) x (1/(2 : ℝ)^target) := by
  dsimp only
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  obtain ⟨v₁,n₁,D,hu₁,hn₁,hlen,he₁,hnorm,herror⟩ := placedFamilyInitializedInterior_spec (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hband has hbs hpad C hC x hx v S borrowed familyTail
    h127 h138 ha hb hready hfamily hcache
  let output := cstream A w (chirpLine s D)++S.R 132
  let T : Stacks 263 A := {S with R := Function.update S.R 132 output}
  have hT : embStk familyCouplingSourceReg T =
      {embStk familyCouplingSourceReg S with R := Function.update (embStk familyCouplingSourceReg S).R 132 output} := by
    change embStk familyCouplingSourceReg {S with R := Function.update S.R (familyCouplingSourceReg 132) output} = _
    rw [embStk_updateR_inner familyCouplingSourceReg familyCouplingSourceReg_injective]
  have hr : LengthKeyReady (2^15*p) (executionStagePrecision p l target rhsExp+1) q l s t u band 0 0
      (cstream A w (chirpLine s C)++borrowed) (embStk familyCouplingSourceReg T) := by
    rw [hT]
    exact hready.update_output output
  obtain ⟨vi,hui,hei,hcoupling⟩ := installCouplingHeaders_exec
    (body := fun p : Empty => nomatch p) (2^15*p) (executionStagePrecision p l target rhsExp+1) q l s t u band a b
    (cstream A w (chirpLine s C)++borrowed) (embDn familyCouplingSourceReg v₁) (embStk familyCouplingSourceReg T) hr
    (by rw [hT]; simpa using ha) (by rw [hT]; simpa using hb)
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    familyCouplingSourceReg_injective (fun p => nomatch p) hei v₁ rfl T rfl
  let H : Stacks 144 A := {embStk familyCouplingSourceReg T with R := couplingHeadersR (2^15*p) q s t u band a b (embStk familyCouplingSourceReg T).R}
  let G := embOvr familyCouplingSourceReg H.get T
  have hw : 2*q+8 = w := by dsimp [q,w,executionPrecision,executionWidth]; omega
  refine ⟨v₂,n₁+installCouplingHeadersCost (2^15*p) q s t u band a b,D,
    hu₂.trans (hui.trans hu₁),Nat.add_le_add_right hn₁ _,Exec.seq he₁ he₂,?_,?_,hnorm,herror⟩
  · rw [embStk_ovr familyCouplingSourceReg_injective]
    simpa only [hw] using hcoupling
  · intro i
    have hh := embOvr_off (e := familyCouplingSourceReg) H.get T (familyCouplingSourceReg_off i)
    refine ⟨hh.1,hh.2.trans ?_⟩
    have hi132 : familyInversePort i ≠ 132 := by
      intro he
      have hv := congrArg (fun j : Fin 263 => j.val) he
      dsimp [familyInversePort] at hv
      omega
    simp [T,hi132]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
