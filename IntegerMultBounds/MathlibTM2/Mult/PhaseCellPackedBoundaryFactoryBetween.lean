module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloNextInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryFactoryGeometry
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedRetainedCouplingIntervalMetadata

/-! Execute the factor supplier, native cleanup and canonical geometry setup in
one machine. The caller's packed publication buffer is retained throughout. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 242 Q A U}

theorem packedBoundaryFactoryGeometry_between_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (v : HS 242 Q A U) (S : Stacks 242 A) (tail : List (Fin (A+4)))
    (h109 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 109 = []) (h115 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 115 = []) (h116 : (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 116 = [])
    (hleft : ∀ i : Fin 224, (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).L (preparedBoundaryCoreReg i) = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u
      (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u
        (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
      l s t u (PhaseCellBand.width p u) 0 0 tail
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
    (hscratch : ∀ k ∈ ([125,127,128,129,130,131,133,134,135,136,138,139,140,143,153,158,166,167] : List (Fin 242)), S.R k = []) :
    let band := PhaseCellBand.width p u
    let B := haloBoundary s t band a b
    let bits := boundaryTableBits p target rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let W := 12*band+1
    ∃ v' F n, ∃ columns : List (ZMod s → GaussianInt),
      v'.user = v.user ∧ n ≤ constructedBoundaryFactorCost p u l s t a b target rhsExp+
        (2*(B.card*publicationGeometryWidth t band+publicationGeometryWidth t band+B.card)+7)+
        ((s+t+band+a+b)*(4*V+10)+56*V+77) ∧
      Exec body (packedBoundaryFactoryGeometry hR hQ) (mk v S) n (mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧
      F.R 110 = tail ∧ F.R 132 = S.R 132 ∧
      PreparedBoundaryColumns A p bits q w W B columns ∧
      (∀ i ∈ B, ∀ j ∈ B, |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-
        (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
          (haloInterior s t band a b).toList).1 i j| ≤ 1/(2 : ℝ)^bits) ∧
      PackedBoundaryFactorPages
        (cstream A w ((naturalLineLc q (factorNewtonSteps p q) W B.card (factorRankIntegerMatrix B W columns)).map colC).flatten)
        (cstream A w ((naturalLineUc q (factorNewtonSteps p q) W B.card (factorRankIntegerMatrix B W columns)).map colC).flatten)
        (cstream A w ((naturalLineRcs q (factorNewtonSteps p q) W B.card (factorRankIntegerMatrix B W columns)).map fun z => (⟨z,0⟩ : GaussianInt))) F ∧
      PackedHaloBetweenInputs (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
        q l s t u band a b V w W B.card (extendStacks (by decide) F) ∧
      F.R 220 = bandTableWords A w B W columns 0++S.R 220 ∧
      BoundaryFactorStock (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg F))
        (boundaryFactorStockBound q w band B.card) := by
  dsimp only
  obtain ⟨v',F,n,columns,hu',hn,he,hinp,hout,hraw,hstock,hlen,hformat,haccuracy,hstage,
    hsolve,hbo,hhf,hdf,hvk,h224,h225,hleft',hmul,hmaster,h223,h184,h220,h221,
    herror,hnative,hmeta,hbuffer,h93,hheader⟩ :=
    packedBoundaryFactoryGeometry_spec (body := body) hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget
      hband has hbs hpad v S tail h109 h115 h116 hleft hready haMaster hbMaster h0 h139 h127 h138
      h143 h147 h151 h153 h152 hnew h132left hV h155 h165 hfitV hgeometryBlank
  have hcarry (k : Fin 242) (hk : 117 ≤ k.val) (hlt : k.val < 168) (hne : k ≠ 143)
      (hnot : k ∉ packedBoundaryGeometryPorts) : F.R k = S.R k := hheader k hk hlt hne hnot
  have hscratch' : ∀ k ∈ ([125,127,128,129,130,131,133,134,135,136,138,139,140,143,153,158,166,167] : List (Fin 242)), F.R k = [] := by
    intro k hk
    have h143' : F.R 143 = [] := by
      simpa [embStk,packedBoundaryFactorReg,packedBoundaryTableRouting,Equiv.swap_apply_def] using hvk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact h143' | exact (hcarry _ (by decide) (by decide) (by decide) (by decide)).trans (hscratch _ (by decide))
  have hmasters : ∀ r ∈ groupHeaderCopies, ((embStk packedHaloRuntimeReg F).R (packedHeaderReg r.1)).length =
      groupHeaderValue (2^15*p) (executionStagePrecision p l (initialSchurTarget p u
        (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
        (executionPrecision p l (initialSchurTarget p u
        (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
        l s t u (PhaseCellBand.width p u) 0 r.1 := by
    intro r hr
    have hh := hready.masters r hr
    simp only [groupHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      change (F.R _).length = _
      rw [hcarry _ (by decide) (by decide) (by decide) (by decide)]
      simpa [embStk,packedHaloRuntimeReg,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,
        preparedBoundaryCoreReg,packedBoundaryFactorReg,packedBoundaryTableRouting,
        Equiv.swap_apply_def,packedHeaderReg,groupHeaderValue] using hh
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  have hbank : PackedPreparedBank q w (12*PhaseCellBand.width p u+1) B.card F := by
    refine ⟨hsolve,?_⟩
    constructor
    · exact hleft'
    · intro i
      have hi := i.isLt
      simpa [embStk,preparedBoundaryCoreReg,packedBoundaryFactorReg,packedBoundaryTableRouting,
        Equiv.swap_apply_def,boundaryFactorMulReg,Fin.ext_iff,
        show i.val ≠ 140 by omega,show i.val ≠ 143 by omega,
        show i.val ≠ 206 by omega,show i.val < 154 by omega,
        show i.val ≠ 220 by omega,show i.val ≠ 241 by omega,show i.val ≠ 132 by omega] using hmul i
    · simpa [embStk,packedBoundaryFactorReg,packedBoundaryTableRouting,Equiv.swap_apply_def] using hmaster
    · simpa [embStk,packedBoundaryFactorReg,packedBoundaryTableRouting,Equiv.swap_apply_def] using h223
    · simpa [embStk,packedBoundaryFactorReg,packedBoundaryTableRouting,Equiv.swap_apply_def] using h184
    · simpa [embStk,packedBoundaryFactorReg,packedBoundaryTableRouting,Equiv.swap_apply_def] using h220
    · simpa [embStk,packedBoundaryFactorReg,packedBoundaryTableRouting,Equiv.swap_apply_def] using h221
    · simpa [embStk,packedBoundaryFactorReg,packedBoundaryTableRouting,Equiv.swap_apply_def,h239] using h225
  have hsrc : F.R 110 = tail := by
    have hh := congrArg (fun T : Stacks 117 A => T.R 110) hnative
    simpa [embStk,packedCellCoreReg,packedHaloRuntimeReg,releasedCellBank,List.nil_append] using hh
  have hview : embStk packedRecoveryRuntimeReg (extendStacks (by decide : 242 ≤ 248) F) =
      embStk packedHaloRuntimeReg F := by
    refine Stacks.ext rfl rfl ?_ ?_
    all_goals
      funext i
      have hi := i.isLt
      simp [embStk,packedRecoveryRuntimeReg,packedHaloRuntimeReg,extendStacks,
        show i.val < 242 by omega]
  refine ⟨v',F,n,columns,hu',hn,he,hinp,hout,hsrc,hbuffer,⟨hlen,hformat,hstage⟩,herror,⟨hbo,hhf,hdf⟩,?_,hraw,hstock⟩
  constructor
  · simpa only [packedBoundaryRecoveryBase,embStk_extendStacks] using hbank
  · constructor
    · constructor
      · simpa [embStk,packedRecoveryRuntimeReg,extendStacks,packedHaloRuntimeReg,packedHeaderReg,groupHeaderValue] using hmasters (117,114) (by decide)
      · simpa [embStk,packedRecoveryRuntimeReg,extendStacks,packedHaloRuntimeReg,packedHeaderReg,groupHeaderValue] using hmasters (119,112) (by decide)
      · simpa [embStk,packedRecoveryRuntimeReg,extendStacks,packedHaloRuntimeReg,packedHeaderReg,groupHeaderValue] using hmasters (121,97) (by decide)
      · simpa [embStk,packedRecoveryRuntimeReg,extendStacks,packedHaloRuntimeReg,packedHeaderReg,groupHeaderValue] using hmasters (122,98) (by decide)
      · simpa [embStk,packedRecoveryRuntimeReg,extendStacks,packedHaloRuntimeReg,packedHeaderReg,groupHeaderValue] using hmasters (123,99) (by decide)
      · simpa [embStk,packedRecoveryRuntimeReg,extendStacks,packedHaloRuntimeReg,packedHeaderReg,groupHeaderValue] using hmasters (124,100) (by decide)
      · change (F.R 141).length = _
        rw [hcarry 141 (by decide) (by decide) (by decide) (by decide)]
        simpa [embStk,packedBoundaryFactorReg,packedBoundaryTableRouting,Equiv.swap_apply_def] using haMaster
      · change (F.R 142).length = _
        rw [hcarry 142 (by decide) (by decide) (by decide) (by decide)]
        simpa [embStk,packedBoundaryFactorReg,packedBoundaryTableRouting,Equiv.swap_apply_def] using hbMaster
      · change (F.R 130).length = 0
        rw [hscratch' 130 (by decide)]; rfl
    · simpa only [hview] using hmeta
    · simpa [embStk,packedRecoveryRuntimeReg,extendStacks,packedHaloRuntimeReg,packedHeaderReg,groupHeaderValue] using hmasters (118,101) (by decide)
    · simpa [embStk,packedRecoveryRuntimeReg,extendStacks,packedHaloRuntimeReg,packedHeaderReg,groupHeaderValue] using hmasters (120,109) (by decide)
  · intro i hi93 hi110
    have hh := congrArg (fun T : Stacks 117 A => T.R i) hnative
    have hi := i.isLt
    simpa [embStk,packedCellCoreReg,packedHaloRuntimeReg,packedBoundaryTableRouting,extendStacks,releasedCellBank,
      Equiv.swap_apply_def,show i.val < 242 by omega,show i.val ≠ 93 from fun h => hi93 (Fin.ext h),
      show i.val ≠ 110 from fun h => hi110 (Fin.ext h)] using hh
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simpa [extendStacks] using hscratch' _ (by decide)
  · change (F.R 157).length ≤ V
    rw [hcarry 157 (by decide) (by decide) (by decide) (by decide)]
    exact h157
  · intro k hk
    exact extendStacks_fresh (by decide) F k hk

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
