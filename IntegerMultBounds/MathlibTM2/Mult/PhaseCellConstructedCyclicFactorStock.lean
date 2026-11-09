module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConstructedCyclicFactor
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCyclicFactorPageStock
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScaledInitializedBoundaryFactor


/-! Construct the accurate Schur input page, generate complete physical setup, and execute its full factorization. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def constructedCyclicFactorWorkspace (hQ : SS.states ≤ Q)
    (J ringPush batchPush rowPush p u l s t a n target rhsExp : ℕ) [NeZero s] : ℕ :=
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  preparedCyclicFactorPageWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
    J ringPush batchPush rowPush p l s t u bits a n+
  scaledInitializedBoundaryFactorWorkspace (P := P₀) (A := A) (U := U)
    2 hQ p q (PhaseCellBand.width p u) B.card

theorem constructedCyclicFactor_spec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a n : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (has : a < s) (hbs : n ≤ s)
    (J ringPush batchPush : ℕ)
    (hpushJ : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ J)
    (hpushR : mnProgPush (rpProg (P := P₀) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ ringPush)
    (hpushK : mnProgPush (cmulBlock cr
      (rmulOne (P := P₀) (Q := Q) (A := A) (U := U) mul mul_injective (by decide) hQ cr)) ≤ batchPush)
    (rowPush : ℕ) (hrowPush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ rowPush)
    (v : HS 224 Q A U) (S : Stacks 224 A) (tail : List (Fin (A+4)))
    (pageTail : List (Fin (A+4)))
    (hrows : (S.R 116).length = (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card)
    (hpageWidth : (S.R 115).length = publicationGeometryWidth t (PhaseCellBand.width p u))
    (hpage : S.R 109 = cstream A (publicationGeometryWidth t (PhaseCellBand.width p u))
      ((bFoldOrder s (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n)).map
        (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u (boundaryTableBits p target rhsExp (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target rhsExp (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) l s t u (PhaseCellBand.width p u) 0 0 tail (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))))
    (haSrc : (S.R 144).length = a) (hleftEnd : (S.R 145).length = a+min n (s-a))
    (hrightEnd : (S.R 146).length = n-min n (s-a))
    (h141 : S.R 141 = []) (h142 : S.R 142 = [])
    (h0 : S.R 0 = [])
    (h139 : S.R 139 = [])
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) (h147 : S.R 147 = [])
    (h151 : S.R 151 = []) (h152 : S.R 152 = []) (h153 : S.R 153 = [])
    (hleft : ∀ i : Fin 224, S.L i = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → S.R i = []) :
    let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
    let bits := boundaryTableBits p target rhsExp B.card
    let band := PhaseCellBand.width p u
    let W := 24*band+1
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    ∃ v' S' steps, ∃ columns : List (ZMod s → GaussianInt),
      let E := embStk boundaryFactorLegacyReg S
      let inputPage := cstream A w ((factorWindowValues B W columns).flatten++(factorInputValues B W B.card columns).flatten)
      let E₁ : Stacks 154 A := {E with R := (Function.update (Function.update E.R
        132 (bandTableWords A w B W columns 0++E.R 132)) 140 (inputPage++E.R 140))}
      let S₁ := embOvr boundaryFactorLegacyReg E₁.get S
      let σ := boundaryFactorState {S₁ with R := scaledFactorSetupR 24 p q S₁.R}
      let rows := factorIntegerRows (factorWindowValues B W columns)
      let inputs := factorIntegerRows (factorInputValues B W B.card columns)
      v'.user = v.user ∧ steps ≤ constructedCyclicFactorCost p u l s t a n target rhsExp ∧
      ExecWithin (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))))
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
          constructedCyclicFactorWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
            hQ J ringPush batchPush rowPush p u l s t a n target rhsExp)
        0 (constructedCyclicFactor hR hQ) (mk v S) steps (mk v' S') ∧
      columns.length = B.card ∧
      ColumnFamilyAccurate A q w B
        (SchurDominance.run (realMatrix s t p u) (cyclicPrincipalVertices s a n)
          (cyclicPrincipalInterior s t band a n).toList).1 (1/(2 : ℝ)^bits) columns ∧ ColumnFamilyFormat w columns ∧
      PreparedBoundaryColumns A p bits q w W B columns ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ i : Fin 154, i ≠ 140 → S'.R (boundaryFactorLegacyReg i) = E₁.R i) ∧
      (∀ i : Fin 64, S'.R (boundaryFactorMulReg i) = []) ∧ S'.R 106 = [] ∧ S'.R 139 = [] ∧
      S'.R 184 = [] ∧ S'.R 223 = [] ∧ S'.R 220 = [] ∧ S'.R 221 = [] ∧
      (S'.R 119).length = q ∧
      BoundarySolveReady (boundaryFactorState S') q w (W) B.card ∧
      (boundaryFactorState S') .bo = cstream A w ((facLf q K rows inputs B.card).map fun x => (⟨x, 0⟩ : GaussianInt)) ∧
      (boundaryFactorState S') .hf = cstream A w ((List.range B.card).reverse.map fun m =>
        colC (Mult.BandFactor.ucolZ (W) (facUr q K rows inputs B.card) m)).flatten ∧
      (boundaryFactorState S') .df = cstream A w ((List.range B.card).reverse.map fun j =>
        (⟨Mult.BandFactor.newtonZ q (facPiv (facState q K rows inputs j)) K, 0⟩ : GaussianInt)) ∧
      (boundaryFactorState S') .src = S.R 140 ∧ ((boundaryFactorState S') .m2n).length = W ∧ ((boundaryFactorState S') .mwn).length = (W) * w ∧
      ((boundaryFactorState S') .sn).length = B.card ∧ (boundaryFactorState S') .dout = [] ∧ (boundaryFactorState S') .vk = [] ∧ (boundaryFactorState S') .ef = [] ∧ (boundaryFactorState S') .xs = [] ∧
      ((boundaryFactorState S') .kn).length = B.card * (W) ∧ (boundaryFactorState S') .ms = σ .dst ∧ (boundaryFactorState S') .m2n = σ .ms ∧
      (boundaryFactorState S') .kn = (List.replicate B.card (σ .ms)).flatten ∧ (boundaryFactorState S') .mwn = σ (.cm .wn) ++ σ .m2wn ∧
      RsbReady (boundaryFactorState S') w q ∧
      boundaryUnfoldHeaderVolume (boundaryFactorState S') ≤ 24*band*w+B.card*W ∧
      BoundaryPermanentBound (boundaryFactorState S') (boundaryPermanentSizeBound q (2*band) B.card) ∧
      ∀ r, r ∉ ([.src, .hf, .df, .dout, .bo, .vk, .m2n, .kn, .ms, .mwn, .ef, .xs] : List RsbR) →
        (boundaryFactorState S') r = σ r := by
  dsimp only
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let bits := boundaryTableBits p target rhsExp B.card
  let W := 24*PhaseCellBand.width p u+1
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let E := embStk boundaryFactorLegacyReg S
  obtain ⟨v₁,n₁,columns,hu₁,hn₁,he₁,hlen,hcolumns,hformat,hprepared,hready₁⟩ :=
    preparedCyclicFactorPage_spec_within (body := body) (target := bits)
      hR hQ hA axis has hbs J ringPush batchPush hpushJ hpushR hpushK rowPush hrowPush (embDn boundaryFactorLegacyReg v) E tail pageTail
      hrows hpageWidth hpage hready haSrc hleftEnd hrightEnd
      h141 h142 h0 h139 h127 h138 h143 h147 h151 h152 h153
  let inputPage := cstream A w ((factorWindowValues B W columns).flatten++(factorInputValues B W B.card columns).flatten)
  let E₁ : Stacks 154 A := {E with R := (Function.update (Function.update E.R
    132 (bandTableWords A w B W columns 0++E.R 132)) 140 (inputPage++E.R 140))}
  let S₁ := embOvr boundaryFactorLegacyReg E₁.get S
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr_within_stock boundaryFactorLegacyReg (ι := id)
    (body' := embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))))
    boundaryFactorLegacyReg_injective (fun _ => rfl) he₁ v rfl S rfl
  have hproj : embStk boundaryFactorLegacyReg S₁ = E₁ := embStk_ovr boundaryFactorLegacyReg_injective E₁ S
  have he₂' : ExecWithin (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))))
      (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
        preparedCyclicFactorPageWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
          J ringPush batchPush rowPush p l s t u bits a n)
      0 (embProg boundaryFactorLegacyReg id (preparedCyclicFactorPage hR hQ)) (mk v S) n₁ (mk v₂ S₁) := he₂
  have hinput := boundaryFactorLegacy_input
    (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1) q l s t u
    (PhaseCellBand.width p u) 0 0 B.card tail S E₁ hready
    (by intro i h109 h115 h116 h132 h140; simp [E₁,E,embStk,h132,h140])
    (by simpa [E₁,E,embStk,boundaryFactorLegacyReg] using hrows) rfl hleft hnew
  have hsrc : S₁.R 140 = cstream A w
      ((factorWindowValues B W columns).flatten++(factorInputValues B W B.card columns).flatten)++S.R 140 := by
    have hh := congrArg (fun X : Stacks 154 A => X.R 140) hproj
    simpa [E₁,E,inputPage,embStk,boundaryFactorLegacyReg] using hh
  have hscale : 12*(2*PhaseCellBand.width p u) = 24*PhaseCellBand.width p u := by omega
  obtain ⟨v₃,S₃,n₃,hu₃,hn₃,he₃,hinp,hout,hL,hlegacy,hpost⟩ := scaledInitializedBoundaryFactor_exec
    (body := embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))))
    2 hQ hA p u l target rhsExp B (PhaseCellBand.width p u) columns axis.hp hlen hformat
      (by simpa only [hscale] using hprepared.stage) v₂ S₁
    hinput.left hinput.clean hinput.fresh hinput.masterP hinput.masterQ hinput.band hinput.card (S.R 140) (by simpa only [hscale] using hsrc)
  rw [hscale] at hn₃ hpost
  have hmul' (i : Fin 64) : S₃.R (boundaryFactorMulReg i) = [] := by
    let j : Fin 154 := ⟨i.val,by omega⟩
    have hj : boundaryFactorLegacyReg j = boundaryFactorMulReg i := Fin.ext rfl
    have hh := hlegacy j (by intro h; have hv := congrArg (fun k : Fin 154 => k.val) h; have := i.isLt; change i.val = 140 at hv; omega)
    rw [hj] at hh
    exact hh.trans (hinput.clean (boundaryFactorMulReg i) i.isLt)
  have h106orig : S.R 106 = [] := by
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using
      hready.blank 106 (by decide) (by decide) (by decide)
  have h106' : S₃.R 106 = [] := by
    have hh := congrArg (fun X : Stacks 154 A => X.R 106) hproj
    exact (hlegacy 106 (by decide)).trans (hh.trans (by simp [E₁,E,embStk,boundaryFactorLegacyReg,h106orig]))
  have h139' : S₃.R 139 = [] := by
    have hh := congrArg (fun X : Stacks 154 A => X.R 139) hproj
    exact (hlegacy 139 (by decide)).trans (hh.trans (by simp [E₁,E,embStk,boundaryFactorLegacyReg,h139]))
  have hL₁ : S₁.L = S.L := funext (fun i => (hinput.left i).trans (hleft i).symm)
  refine ⟨v₃,S₃,n₁+n₃,columns,hu₃.trans (hu₂.trans hu₁),Nat.add_le_add hn₁ hn₃,
    ?_,hlen,hcolumns,hformat,hprepared,hinp,hout,hL.trans hL₁,?_,hmul',h106',h139',hpost⟩
  · simpa only [constructedCyclicFactor,constructedCyclicFactorWorkspace] using
      mn_seq_within_add he₂' he₃
  intro i hi
  have hh := congrArg (fun X : Stacks 154 A => X.R i) hproj
  exact (hlegacy i hi).trans hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
