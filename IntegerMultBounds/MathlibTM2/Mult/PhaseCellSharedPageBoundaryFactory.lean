module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryFactory
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRecoveryReady

/-! Generate the computed shared page with the ordinary arithmetic frame and geometry needed by the complete complex driver. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 240 Q A U}

noncomputable def sharedPageBoundaryFactory (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 240 Q A U :=
  embProg sharedPageRecoveryReg Empty.elim (constructedBoundaryFactor (P₀ := Empty) hR hQ)

theorem sharedPageBoundaryFactory_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (v : HS 240 Q A U) (S : Stacks 240 A) (tail : List (Fin (A+4)))
    (h109 : S.R 109 = []) (h115 : S.R 115 = []) (h116 : S.R 116 = [])
    (hleft : ∀ i : Fin 240, S.L i = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u
      (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u
        (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
      l s t u (PhaseCellBand.width p u) 0 0 tail
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk sharedPageRecoveryReg S))))))
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (h0 : S.R 0 = []) (h139 : S.R 139 = []) (h127 : S.R 127 = []) (h138 : S.R 138 = [])
    (h143 : S.R 143 = []) (h147 : S.R 147 = []) (h151 : S.R 151 = []) (h153 : S.R 153 = [])
    (h152 : S.R 152 = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → S.R (sharedPageRecoveryReg i) = []) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let bits := boundaryTableBits p target rhsExp B.card
    let band := PhaseCellBand.width p u
    let W := 12*band+1
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    ∃ v' S' n, ∃ columns : List (ZMod s → GaussianInt),
      let σ := boundaryFactorState (embStk sharedPageRecoveryReg S')
      let AZ := factorRankIntegerMatrix B W columns
      v'.user = v.user ∧ n ≤ constructedBoundaryFactorCost p u l s t a b target rhsExp ∧
      Exec body (sharedPageBoundaryFactory hR hQ) (mk v S) n (mk v' S') ∧
      columns.length = B.card ∧ ColumnFamilyFormat w columns ∧
      ColumnFamilyAccurate A q w B
        (SchurDominance.run (realMatrix s t p u) (haloVertices s a b) (haloInterior s t band a b).toList).1
        (1/(2 : ℝ)^bits) columns ∧
      SchurDominance.StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
        (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits)) (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) ∧
      BoundarySolveReady σ q w W B.card ∧
      σ .bo = cstream A w ((naturalLineLc q K W B.card AZ).map colC).flatten ∧
      σ .hf = cstream A w ((naturalLineUc q K W B.card AZ).map colC).flatten ∧
      σ .df = cstream A w ((naturalLineRcs q K W B.card AZ).map fun x => (⟨x,0⟩ : GaussianInt)) ∧
      S'.R 206 = [] ∧ S'.R 224 = S.R 224 ∧ S'.R 225 = S.R 225 ∧
      (∀ i : Fin 224, S'.L (sharedPageRecoveryReg i) = []) ∧
      (∀ i : Fin 64, S'.R (sharedPageRecoveryReg (boundaryFactorMulReg i)) = []) ∧
      (S'.R 119).length = q ∧ S'.R 223 = [] ∧ S'.R 184 = [] ∧ S'.R 220 = [] ∧ S'.R 221 = [] ∧
      (∀ i ∈ B, ∀ j ∈ B,
        |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-
          (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
            (haloInterior s t band a b).toList).1 i j| ≤ 1/(2 : ℝ)^bits) ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
        q l s t u band 0 0 tail (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
          (embStk boundaryFactorLegacyReg (embStk sharedPageRecoveryReg S'))))) ∧
      S'.R 109 = cstream A (publicationGeometryWidth t band) ((bFoldOrder s B).map
        (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt))) ∧
      S'.R 115 = List.replicate (publicationGeometryWidth t band) tick ∧
      S'.R 116 = List.replicate B.card tick ∧ S'.R 132 = bandTableWords A w B W columns 0++S.R 132 ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ i : Fin 154, i ≠ 109 → i ≠ 115 → i ≠ 116 → i ≠ 132 →
        S'.R (sharedPageRecoveryReg (boundaryFactorLegacyReg i)) = S.R (sharedPageRecoveryReg (boundaryFactorLegacyReg i))) ∧
      (∀ i : Fin 240, 224 ≤ i.val → S'.R i = S.R i) ∧
      (bandTableWords A w B W columns 0).length ≤ B.card*(2*W+1)*w ∧
      boundaryUnfoldHeaderVolume σ ≤ 12*band*w+B.card*W ∧
      BoundaryPermanentBound σ (boundaryPermanentSizeBound q band B.card) := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let bits := boundaryTableBits p target rhsExp B.card
  let band := PhaseCellBand.width p u
  let W := 12*band+1
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let K := factorNewtonSteps p q
  let T := embStk sharedPageRecoveryReg S
  obtain ⟨v₁,T₁,n,columns,hu₁,hn,he,hlen,hcolumns,hformat,hstorage,herror,hstage,hinp,hout,hL,hlegacy,
    hmul,h106,h139',h184,h223,h220,h221,h119,hsolve,hbo,hhf,hdf,hsrc,hm2n,hmwn,hsn,hdout,hvk,
    hef,hxs,hkn,hms,hm2nVal,hknVal,hmwnVal,hrsb,hheaders,hperm,hrest⟩ := constructedBoundaryFactor_spec
    (body := fun p : Empty => nomatch p) hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
    (embDn sharedPageRecoveryReg v) T tail h109 h115 h116 (fun i => hleft _) hready haMaster hbMaster
    h0 h139 h127 h138 h143 h147 h151 h153 h152 hnew
  have hframe : ∀ i : Fin 154, i ≠ 109 → i ≠ 115 → i ≠ 116 → i ≠ 132 →
      T₁.R (boundaryFactorLegacyReg i) = T.R (boundaryFactorLegacyReg i) := by
    intro i hi109 hi115 hi116 hi132
    by_cases hi140 : i = 140
    · subst i; exact hsrc
    have hh := hlegacy i hi140
    simpa only [Function.update_of_ne hi140,Function.update_of_ne hi132,Function.update_of_ne hi109,
      Function.update_of_ne hi116,Function.update_of_ne hi115,embStk,Function.comp_def] using hh
  have hready₁ := boundaryRecoveryReady_of_frame hready hinp hout hL
    (fun i hi109 hi110 hi115 hi116 hi132 => hframe i hi109 hi115 hi116 hi132)
  have hsource : T₁.R 110 = T.R 110 := hframe 110 (by decide) (by decide) (by decide) (by decide)
  have hready₁' : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band 0 0 tail (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg T₁)))) := by
    have hsource₀ : T.R 110 = tail := hready.source
    simpa only [hsource,hsource₀] using hready₁
  have hc : T₁.R 109 = cstream A (publicationGeometryWidth t band) ((bFoldOrder s B).map
      (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt))) := by
    simpa [boundaryFactorLegacyReg,B,band] using hlegacy 109 (by decide)
  have hV : T₁.R 115 = List.replicate (publicationGeometryWidth t band) tick := by
    simpa [boundaryFactorLegacyReg,B,band] using hlegacy 115 (by decide)
  have hN : T₁.R 116 = List.replicate B.card tick := by simpa [boundaryFactorLegacyReg,B,band] using hlegacy 116 (by decide)
  have htable : T₁.R 132 = bandTableWords A w B W columns 0++T.R 132 := by
    simpa [boundaryFactorLegacyReg,B,band,w,W,bits,embStk] using hlegacy 132 (by decide)
  obtain ⟨hbo',hhf',hdf'⟩ := boundaryFactor_solve_tables q w K B W columns (boundaryFactorState T₁) hbo hhf hdf
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    sharedPageRecoveryReg_injective (fun p => nomatch p) he v rfl S rfl
  let S₁ := embOvr sharedPageRecoveryReg T₁.get S
  have hproj : embStk sharedPageRecoveryReg S₁ = T₁ := embStk_ovr sharedPageRecoveryReg_injective T₁ S
  have hprivate (i : Fin 240) (hi : 224 ≤ i.val) : S₁.R i = S.R i :=
    (embOvr_off (e := sharedPageRecoveryReg) T₁.get S (fun j => by
      intro he
      have hh := congrArg (fun k : Fin 240 => k.val) he
      have hj := j.isLt
      change j.val = i.val at hh
      omega)).2
  have hL' : S₁.L = S.L := by
    funext i
    by_cases hi : i.val < 224
    · let j : Fin 224 := ⟨i.val,hi⟩
      have hj : sharedPageRecoveryReg j = i := Fin.ext rfl
      rw [← hj]
      exact (congrArg (fun R : Stacks 224 A => R.L j) hproj).trans (congrFun hL j)
    · exact (embOvr_off (e := sharedPageRecoveryReg) T₁.get S (fun j => by
        intro he
        have hh := congrArg (fun k : Fin 240 => k.val) he
        have hj := j.isLt
        change j.val = i.val at hh
        omega)).1
  refine ⟨v₂,S₁,n,columns,hu₂.trans hu₁,hn,he₂,hlen,hformat,hcolumns,hstage,?_,?_,?_,?_,?_,
    hprivate 224 (by decide),hprivate 225 (by decide),?_,?_,?_,?_,?_,?_,?_,herror,?_,?_,?_,?_,?_,?_,?_,hL',?_,hprivate,hstorage,?_,?_⟩
  · rw [hproj]; exact hsolve
  · rw [hproj]; exact hbo'
  · rw [hproj]; exact hhf'
  · rw [hproj]; exact hdf'
  · exact (congrArg (fun R : Stacks 224 A => R.R 206) hproj).trans hvk
  · intro i
    rw [hL']
    exact hleft _
  · intro i
    exact (congrArg (fun R : Stacks 224 A => R.R (boundaryFactorMulReg i)) hproj).trans (hmul i)
  · exact (congrArg (fun R : Stacks 224 A => (R.R 119).length) hproj).trans h119
  · exact (congrArg (fun R : Stacks 224 A => R.R 223) hproj).trans h223
  · exact (congrArg (fun R : Stacks 224 A => R.R 184) hproj).trans h184
  · exact (congrArg (fun R : Stacks 224 A => R.R 220) hproj).trans h220
  · exact (congrArg (fun R : Stacks 224 A => R.R 221) hproj).trans h221
  · rw [hproj]; exact hready₁'
  · exact (congrArg (fun R : Stacks 224 A => R.R 109) hproj).trans hc
  · exact (congrArg (fun R : Stacks 224 A => R.R 115) hproj).trans hV
  · exact (congrArg (fun R : Stacks 224 A => R.R 116) hproj).trans hN
  · exact (congrArg (fun R : Stacks 224 A => R.R 132) hproj).trans htable
  · exact hinp
  · exact hout
  · intro i hi109 hi115 hi116 hi132
    exact (congrArg (fun R : Stacks 224 A => R.R (boundaryFactorLegacyReg i)) hproj).trans
      (hframe i hi109 hi115 hi116 hi132)
  · rw [hproj]; exact hheaders
  · rw [hproj]; exact hperm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
