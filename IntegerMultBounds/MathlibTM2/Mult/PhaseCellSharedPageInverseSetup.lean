module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageBoundaryFactory
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPagePublicationSetup

/-! Execute factor construction and reusable publication-control setup once for a shared inverse key. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 240 Q A U}

noncomputable def sharedPageInverseSetup (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 240 Q A U :=
  .seq (sharedPageBoundaryFactory hR hQ) sharedPagePublicationSetup

theorem sharedPageInverseSetup_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (h152 : S.R 152 = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → S.R (sharedPageRecoveryReg i) = []) (hprivateFresh : ∀ i : Fin 240, 224 ≤ i.val → S.R i = []) :
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
      v'.user = v.user ∧ n ≤ constructedBoundaryFactorCost p u l s t a b target rhsExp+
        sharedPagePublicationSetupCost B.card (publicationGeometryWidth t band) w s ∧
      Exec body (sharedPageInverseSetup hR hQ) (mk v S) n (mk v' S') ∧
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
      (∀ i : Fin 240, 224 ≤ i.val → i ≠ 239 → S'.R i = S.R i) ∧
      (bandTableWords A w B W columns 0).length ≤ B.card*(2*W+1)*w ∧
      boundaryUnfoldHeaderVolume σ ≤ 12*band*w+B.card*W ∧
      BoundaryPermanentBound σ (boundaryPermanentSizeBound q band B.card) ∧
      S'.R 239 = gatherControls A (originAdvances w 0 (boundaryScatterOrigins s B)++[0]) := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let bits := boundaryTableBits p target rhsExp B.card
  let band := PhaseCellBand.width p u
  let W := 12*band+1
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let V := publicationGeometryWidth t band
  obtain ⟨v₁,S₁,n₁,columns,hu₁,hn₁,he₁,hlen,hformat,hcolumns,hstage,hsolve,hbo,hhf,hdf,h206,h224,h225,
    hleft₁,hmul,h119,h223,h184,h220,h221,herror,hready₁,hcoords,hV,hN,h132,hinp,hout,hL,hframe,hprivate,
    hstorage,hheaders,hperm⟩ := sharedPageBoundaryFactory_spec (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad v S tail h109 h115 h116 hleft
    hready haMaster hbMaster h0 h139 h127 h138 h143 h147 h151 h153 h152 hnew
  have hsV : s ≤ 2^V := by
    have hfit : 8*(t+1)^2+2*band+8 < 2^V := publicationGeometryWidth_fits t band
    nlinarith only [hfit,hst]
  have hm : ∀ i : Fin 64, (embStk sharedPageCoordinateReg S₁).R (boundaryFactorMulReg i) = [] := by
    intro i
    have hr : sharedPageCoordinateReg (boundaryFactorMulReg i) = sharedPageRecoveryReg (boundaryFactorMulReg i) := by
      apply Fin.ext
      have hi := i.isLt
      dsimp [sharedPageCoordinateReg,sharedPageRecoveryReg,boundaryFactorMulReg]
      split_ifs <;> omega
    simpa only [embStk,Function.comp_def,hr] using hmul i
  have hz : ∀ i ∈ ([0,1,2,3,4,5,6,7,8,9,234,235,184,223,238,208,211,236,201,215,239,231,232,233] : List (Fin 240)), S₁.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact hmul 0
      | exact hmul 1
      | exact hmul 2
      | exact hmul 3
      | exact hmul 4
      | exact hmul 5
      | exact hmul 6
      | exact hmul 7
      | exact hmul 8
      | exact hmul 9
      | exact h184
      | exact h223
      | exact hsolve.empty .ya (by simp [boundarySolveScratch])
      | exact hsolve.empty .xs (by simp [boundarySolveScratch])
      | exact hsolve.empty .tC (by simp [boundarySolveScratch])
      | exact hsolve.empty .ac2 (by simp [boundarySolveScratch])
      | exact (hprivate _ (by decide)).trans (hprivateFresh _ (by decide))
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := sharedPagePublicationSetup_exec (body := body)
    (Nat.le_trans (by decide : 4 ≤ 96) hA) s B V w hsV v₁ S₁ (by intro i; rw [hL]; exact hleft i)
    hm hN (by rw [hV]; simp only [List.length_replicate]; rfl) hsolve.ready.wn hcoords hz
  let advances := gatherControls A (originAdvances w 0 (boundaryScatterOrigins s B)++[0])
  let S₂ : Stacks 240 A := {S₁ with R := Function.update S₁.R 239 advances}
  have hproj : embStk sharedPageRecoveryReg S₂ = embStk sharedPageRecoveryReg S₁ := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    have h239 : sharedPageRecoveryReg i ≠ 239 := by
      intro he
      have hh := congrArg (fun k : Fin 240 => k.val) he
      have hi := i.isLt
      change i.val = 239 at hh
      omega
    simp only [S₂,embStk,Function.comp_def,Function.update_of_ne h239]
  refine ⟨v₂,S₂,n₁+n₂,columns,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,hlen,hformat,hcolumns,hstage,
    ?_,?_,?_,?_,?_,?_,?_,hleft₁,?_,?_,?_,?_,?_,?_,herror,?_,?_,?_,?_,?_,hinp,hout,hL,?_,?_,hstorage,?_,?_,rfl⟩
  · rw [hproj]; exact hsolve
  · rw [hproj]; exact hbo
  · rw [hproj]; exact hhf
  · rw [hproj]; exact hdf
  · simpa [S₂] using h206
  · simpa [S₂] using h224
  · simpa [S₂] using h225
  · intro i
    have hh := hmul i
    have hi : sharedPageRecoveryReg (boundaryFactorMulReg i) ≠ 239 := by
      intro he
      have hv := congrArg (fun k : Fin 240 => k.val) he
      have hi := i.isLt
      change i.val = 239 at hv
      omega
    simpa only [S₂,Function.update_of_ne hi] using hh
  · simpa [S₂] using h119
  · simpa [S₂] using h223
  · simpa [S₂] using h184
  · simpa [S₂] using h220
  · simpa [S₂] using h221
  · rw [hproj]; exact hready₁
  · simpa [S₂] using hcoords
  · simpa [S₂] using hV
  · simpa [S₂] using hN
  · simpa [S₂] using h132
  · intro i hi109 hi115 hi116 hi132
    have hi : sharedPageRecoveryReg (boundaryFactorLegacyReg i) ≠ 239 := by
      intro he
      have hv := congrArg (fun k : Fin 240 => k.val) he
      have hi := i.isLt
      change i.val = 239 at hv
      omega
    simpa only [S₂,Function.update_of_ne hi] using hframe i hi109 hi115 hi116 hi132
  · intro i hi hi239
    simpa only [S₂,Function.update_of_ne hi239] using hprivate i hi
  · rw [hproj]; exact hheaders
  · rw [hproj]; exact hperm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
