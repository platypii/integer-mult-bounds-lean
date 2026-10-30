module

public import IntegerMultBounds.MathlibTM2.StackLifecycleResources
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryFactoryBetween
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloNumericalBatch

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {Q A : ℕ} {P U : Type}

noncomputable def packedHaloBatchSetup (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 249 Q A U :=
  embProg packedHaloBatchReg id (embProg packedBoundaryRecoveryBase id (packedBoundaryFactoryGeometry hR hQ))

noncomputable def packedHaloInitializedBatch (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 249 Q A U :=
  .seq (packedHaloBatchSetup hR hQ) (packedHaloBatch hR hQ)

variable {body : P → Pr P 242 Q A U} {body' : P → Pr P 248 Q A U} {body'' : P → Pr P 249 Q A U}

/-- Setup is independent of the external replica counter. -/
theorem packedHaloBatchSetup_exec
    (hbody : ∀ f, body' f = embProg packedBoundaryRecoveryBase id (body f))
    (hbody' : ∀ f, body'' f = embProg packedHaloBatchReg id (body' f))
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    {vi vf : HS 242 Q A U} {S F : Stacks 242 A} {n : ℕ}
    (he : Exec body (packedBoundaryFactoryGeometry hR hQ) (mk vi S) n (mk vf F))
    (v : HS 249 Q A U) (S₀ : Stacks 249 A)
    (hv : embDn packedBoundaryRecoveryBase (embDn packedHaloBatchReg v) = vi)
    (hview : embStk packedHaloBatchReg S₀ = extendStacks (by decide) S) :
    ∃ v₁ S₁, v₁.user = vf.user ∧
      Exec body'' (packedHaloBatchSetup hR hQ) (mk v S₀) n (mk v₁ S₁) ∧
      embStk packedHaloBatchReg S₁ = extendStacks (by decide) F ∧ S₁.R 248 = S₀.R 248 := by
  obtain ⟨v',hv',hu',he'⟩ := exec_extendStacks (by decide : 242 ≤ 248) hbody he
    (embDn packedHaloBatchReg v) hv
  have hinj : Function.Injective packedHaloBatchReg := by
    intro i j hij; exact Fin.ext (congrArg (fun k : Fin 249 => k.val) hij)
  obtain ⟨v₁,S₁,he₁,hv₁,hu₁,hview₁,hframe⟩ := exec_emb hinj hbody' he' v rfl S₀ hview
  have hc := hframe 248 (by
    intro i hi
    have hh := congrArg (fun k : Fin 249 => k.val) hi
    have hb := i.isLt
    change i.val = 248 at hh
    omega)
  exact ⟨v₁,S₁,hu₁.trans hu',he₁,hview₁,hc.2⟩

theorem packedHaloInitializedBatch_exec
    (hbody : ∀ f, body' f = embProg packedBoundaryRecoveryBase id (body f))
    (hbody' : ∀ f, body'' f = embProg packedHaloBatchReg id (body' f))
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u boundaryTarget target finalTarget rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (inputs : List ((ZMod s → GaussianInt) × (ZMod s → ℝ)))
    (tail : List (Fin (A+4))) (v : HS 249 Q A U) (S₀ : Stacks 249 A) (S : Stacks 242 A)
    (hview : embStk packedHaloBatchReg S₀ = extendStacks (by decide) S)
    (hcount : (S₀.R 248).length = inputs.length)
    (h109 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 109 = []) (h115 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 115 = []) (h116 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 116 = [])
    (hleft : ∀ i : Fin 224, (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).L (preparedBoundaryCoreReg i) = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u
      (boundaryTableBits p boundaryTarget rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u
        (boundaryTableBits p boundaryTarget rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
      l s t u (PhaseCellBand.width p u) 0 0 ((inputs.map (fun x => cstream A (executionWidth p l target rhsExp)
        (packedInterval a (b-a) x.1))).flatten++tail)
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S))))))))
    (haMaster : ((embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 141).length = a) (hbMaster : ((embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 142).length = b)
    (h0 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 0 = []) (h139 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 139 = []) (h127 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 127 = []) (h138 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 138 = [])
    (h143 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 143 = []) (h147 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 147 = []) (h151 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 151 = []) (h153 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 153 = [])
    (h152 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 152 = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R (preparedBoundaryCoreReg i) = []) (h132left : S.L 132 = [])
    (hV : (S.R 163).length = V)
    (h155 : S.R 155 = binSyms V a) (h165 : S.R 165 = binSyms V (b-a))
    (hfitV : a+((b-a)+2*PhaseCellBand.width p u)+s < 2^V)
    (hgeometryBlank : ∀ k ∈ [(145 : Fin 242),146,147,148,149,151,154,156,164], S.R k = [])
    (h239 : S.R 239 = []) (h157 : (S.R 157).length ≤ V)
    (hscratch : ∀ k ∈ ([125,127,128,129,130,131,133,134,135,136,138,139,140,143,153,158,166,167] : List (Fin 242)), S.R k = [])
    (hab : a ≤ b) (haLt : a < s) (hsep : b-a+PhaseCellBand.width p u ≤ s)
    (hwide : 8*(t+1)^2+4*PhaseCellBand.width p u+8 < 2^V)
    (hVeq : V = weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (2*executionPrecision p l target rhsExp+8) t u)
    (hwV : executionWidth p l target rhsExp < 2^V)
    (hcoords : b < 2^V) (hunits : b*executionWidth p l target rhsExp < 2^V)
    (hC : ∀ x ∈ inputs, ∀ k, ‖value (executionPrecision p l target rhsExp) (x.1 k)‖ ≤ (2 : ℝ)^rhsExp)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (hcell : target = boundaryHaloTarget p u boundaryTarget rhsExp
      (haloBoundary s t (PhaseCellBand.width p u) a b).card)
    (hboundary : boundaryTarget = boundaryRecoveryTarget p finalTarget) :
    let band := PhaseCellBand.width p u
    let B := haloBoundary s t band a b
    let bits := boundaryTableBits p boundaryTarget rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let W := 12*band+1
    (∀ x ∈ inputs, SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x.2
      (fun k => (value q (x.1 k)).re)) →
    (∀ j < b-a, ∀ z ∈ couplingCoefficientWords (2^15*p) q s t u band (a+j), Fits w z ∧ z.im = 0) →
    ∃ v' F n, v'.user = v.user ∧
      n ≤ constructedBoundaryFactorCost p u l s t a b boundaryTarget rhsExp+
        (2*(B.card*publicationGeometryWidth t band+publicationGeometryWidth t band+B.card)+7)+
        ((s+t+band+a+b)*(4*V+10)+56*V+77)+
        packedHaloBatchCost inputs.length
          (packedFreshOutputCost V (b-a) w+packedHaloPreparedInputCost p u l finalTarget rhsExp s t a b V) ∧
      Exec body'' (packedHaloInitializedBatch hR hQ) (mk v S₀) n (mk v' F) ∧
      F.inp = S₀.inp ∧ F.out = S₀.out ∧
      F.R 248 = [] ∧
      ((embStk packedHaloBatchReg F).R 132).length = inputs.length*((b-a)*w)+(S.R 132).length ∧
      (embStk packedHaloBatchReg F).R 110 = tail ∧
      PackedHaloBetweenInputs (2^15*p) (executionStagePrecision p l target rhsExp+1)
        q l s t u band a b V w W B.card (embStk packedHaloBatchReg F) ∧
      ∃ columns : List (ZMod s → GaussianInt), columns.length = B.card ∧
        (embStk packedHaloBatchReg F).R 220 = bandTableWords A w B W columns 0++S.R 220 ∧
        BoundaryFactorStock (embStk preparedBoundaryCoreReg
          (embStk packedBoundaryFactorReg (embStk packedBoundaryRecoveryBase (embStk packedHaloBatchReg F))))
          (boundaryFactorStockBound q w band B.card) ∧
      ∃ M : Stacks 242 A, M.R 132 = S.R 132 ∧
        PackedHaloInputTrace (fun x S F => ∃ D : ZMod s → GaussianInt,
          F.R 132 = cstream A w (packedInterval a (b-a) D)++S.R 132 ∧
          PhaseCellInterface.ErrorOn (haloVertices s a b)
            (fun i => (packedIntervalRead q w a (F.R 132) i).re) x.2 (1/(2 : ℝ)^finalTarget))
          inputs (extendStacks (by decide) M) (embStk packedHaloBatchReg F) ∧
        IntegerMultBounds.MathlibTM2.Fast.Main.mnSize
          (mk (embDn packedHaloBatchReg v') (embStk packedHaloBatchReg F)) ≤
        IntegerMultBounds.MathlibTM2.Fast.Main.mnSize
          (mk (embDn packedHaloBatchReg v) (extendStacks (by decide : 242 ≤ 248) M))+
            inputs.length*((b-a)*w)+V ∧
        ∀ c, mnProgPush (packedHaloInitializedBatch (P := P) (U := U) (A := A) hR hQ) ≤ c →
          (∀ f, mnProgPush (body'' f) ≤ c) → ∀ depth,
          ExecWithin body'' (fun d z => mnSize z+d ≤ mnSize (mk v S₀)+
            (inputs.length*((b-a)*w)+V)+depth+(c+1)*
              (constructedBoundaryFactorCost p u l s t a b boundaryTarget rhsExp+
                (2*(B.card*publicationGeometryWidth t band+publicationGeometryWidth t band+B.card)+7)+
                ((s+t+band+a+b)*(4*V+10)+56*V+77)+
                (packedFreshOutputCost V (b-a) w+packedHaloPreparedInputCost p u l finalTarget rhsExp s t a b V)))
            depth (packedHaloInitializedBatch hR hQ) (mk v S₀) n (mk v' F) := by
  dsimp only
  intro hy hcoeff
  obtain ⟨hq,hstage,hw⟩ := boundaryHaloTarget_sizing p u l boundaryTarget rhsExp
    (haloBoundary s t (PhaseCellBand.width p u) a b).card
  rw [←hcell] at hq hstage hw
  obtain ⟨vf,M,n₁,columns,hu₁,hn₁,he₁,hinputFrame,houtputFrame,hsrc,hout,hcolumns,htable,hpages,hbetween,hraw,hstock⟩ :=
    packedBoundaryFactoryGeometry_between_exec (body := body) hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget
      hband has hbs hpad (embDn packedBoundaryRecoveryBase (embDn packedHaloBatchReg v)) S
      ((inputs.map (fun x => cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) x.1))).flatten++tail)
      h109 h115 h116 hleft hready haMaster hbMaster h0 h139 h127 h138 h143 h147 h151 h153 h152 hnew
      h132left hV h155 h165 hfitV hgeometryBlank h239 h157 hscratch
  obtain ⟨v₁,S₁,hu₁',he₁',hview₁,hcount₁⟩ := packedHaloBatchSetup_exec hbody hbody' hR hQ he₁ v S₀ rfl hview
  have hsource₁ : (embStk packedHaloBatchReg S₁).R 110 =
      (inputs.map (fun x => cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) x.1))).flatten++tail := by
    rw [hview₁]; simpa [extendStacks] using hsrc
  have hbetween₁ := hbetween
  rw [←hstage] at hbetween₁
  rw [←hview₁] at hbetween₁
  have hpages₁ := hpages
  have hproject : embStk packedBoundaryRecoveryBase (embStk packedHaloBatchReg S₁) = M := by
    rw [hview₁]; exact embStk_extendStacks (by decide) M
  rw [←hproject] at hpages₁
  obtain ⟨v₂,F,n₂,hu₂,hn₂,he₂,hcounter,hlength,hsrc₂,hbetween₂,hpages₂,htrace,hsetup₂,hbatchFrame⟩ :=
    packedHaloNumericalBatch_exec hbody hbody' hR hQ hA hp hα hwidth hst hu hαu hθ hgap hbudget hpad
      inputs hC hab hbs hband hwide hVeq hwV hcoords hunits tail v₁ S₁
      (by rw [hcount₁]; exact hcount) hsource₁ haLt hfitV hsep hdom hq
      hbetween₁ columns hcolumns hcell htable hpages₁ hboundary hy hcoeff
  have hinput : F.inp = S₀.inp := by
    have h₁ := congrArg (fun B : Stacks 248 A => B.inp) hview₁
    have h₀ := congrArg (fun B : Stacks 248 A => B.inp) hview
    exact hbatchFrame.1.2.1.trans (h₁.trans (hinputFrame.trans h₀.symm))
  have houtput : F.out = S₀.out := by
    have h₁ := congrArg (fun B : Stacks 248 A => B.out) hview₁
    have h₀ := congrArg (fun B : Stacks 248 A => B.out) hview
    exact hbatchFrame.1.2.2.1.trans (h₁.trans (houtputFrame.trans h₀.symm))
  have hsetup : ∀ k : Fin 242, 168 ≤ k.val → k ≠ 238 →
      (embStk packedBoundaryRecoveryBase (embStk packedHaloBatchReg F)).R k = M.R k := by
    intro k hk hne
    rw [hsetup₂ k hk hne,hproject]
  have hstock₂ := packedBoundaryFactorStock_of_solution_frame hstock hsetup
  have hraw₂ : (embStk packedHaloBatchReg F).R 220 = _ :=
    (hsetup 220 (by decide) (by decide)).trans hraw
  refine ⟨v₂,F,n₁+n₂,hu₂.trans (hu₁'.trans hu₁),Nat.add_le_add hn₁ hn₂,
    Exec.seq he₁' he₂,hinput,houtput,hcounter,?_,hsrc₂,hbetween₂,columns,hcolumns.length,hraw₂,hstock₂,M,hout,?_,?_,?_⟩
  · rw [hview₁] at hlength
    simpa [extendStacks,hout] using hlength
  · simpa only [hview₁] using htrace

  · have hs := hbatchFrame.2.1
    rw [hview₁] at hs
    simpa only [IntegerMultBounds.MathlibTM2.Fast.Main.mnSize,mk] using hs

  · intro c hp hb depth
    change max (mnProgPush (packedHaloBatchSetup hR hQ)) (mnProgPush (packedHaloBatch hR hQ)) ≤ c at hp
    obtain ⟨hpSetup,hpLoop⟩ := max_le_iff.mp hp
    have hpStep : mnProgPush (packedHaloBatchStep (P := P) (U := U) (A := A) hR hQ) ≤ c := by
      simpa [packedHaloBatch,countedLoop,countedLoopBody,mnProgPush,mnActPush,peekR] using hpLoop
    apply mn_setup_exec_within_stock he₁' hn₁ hpSetup hb
    have ht := hbatchFrame.2.2.2.2 c hpStep hb depth
    simpa only [Nat.add_assoc] using ht

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
