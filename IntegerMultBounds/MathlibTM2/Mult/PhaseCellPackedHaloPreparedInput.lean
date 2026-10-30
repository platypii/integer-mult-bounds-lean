module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloPreparedRecovery

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedPreparedReleaseReady

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloPreparedBoundaryExtended
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRecoveryBuffers

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloPreparedBoundary
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRecoveryUnfold

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 242 Q A U} {body' : P → Pr P 248 Q A U}

theorem packedHaloPreparedInput_exec (hbody : ∀ f, body' f = embProg packedBoundaryRecoveryBase id (body f))
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l s t p u target finalTarget rhsExp a b V boundaryTarget : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hα : 0 < α) (hwidth : 8*p ≤ 2^u) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (hab : a ≤ b) (hb : b ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (hwide : 8*(t+1)^2+4*PhaseCellBand.width p u+8 < 2^V)
    (hVeq : V = weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (2*executionPrecision p l target rhsExp+8) t u)
    (hwV : executionWidth p l target rhsExp < 2^V)
    (hcoords : b < 2^V) (hunits : b*executionWidth p l target rhsExp < 2^V)
    (tail E outputTail : List (Fin (A+4)))
    (v : HS 248 Q A U) (S : Stacks 242 A)
    (hnative : embStk packedCellCoreReg (embStk packedHaloRuntimeReg S) = releasedCellBank []
      (cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C)++tail) ((embStk packedHaloRuntimeReg S).R 93) (embStk packedHaloRuntimeReg S).inp (embStk packedHaloRuntimeReg S).out)
    (hmasters : ∀ r ∈ groupHeaderCopies, ((embStk packedHaloRuntimeReg S).R (packedHeaderReg r.1)).length =
      groupHeaderValue (2^15*p) (executionStagePrecision p l target rhsExp+1)
        (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) 0 r.1)
    (ha : ((embStk packedHaloRuntimeReg S).R 141).length = a) (hb' : ((embStk packedHaloRuntimeReg S).R 142).length = b)
    (hmeta : CouplingIntervalMetadata V s t (PhaseCellBand.width p u) a b a (b-a) (embStk packedHaloRuntimeReg S))
    (h157 : ((embStk packedHaloRuntimeReg S).R 157).length ≤ V)
    (houtput : (embStk packedHaloRuntimeReg S).R 132 = E++outputTail) (hE : E.length = (b-a)*executionWidth p l target rhsExp)
    (hfresh : ∀ k ∈ [(125 : Fin 168),127,130,133,138,129,131,134,135,136,140,153,166], (embStk packedHaloRuntimeReg S).R k = [])
    (haLt : a < s) (hfitV : a+((b-a)+2*PhaseCellBand.width p u)+s < 2^V)
    (h139 : (embStk packedHaloRuntimeReg S).R 139 = []) (h143 : (embStk packedHaloRuntimeReg S).R 143 = [])
    (hleft : ∀ k ∈ [(121 : Fin 168),122,123,124], (embStk packedHaloRuntimeReg S).L k = [])
    (hsep : b-a+PhaseCellBand.width p u ≤ s) (h158 : (embStk packedHaloRuntimeReg S).R 158 = []) (h167 : (embStk packedHaloRuntimeReg S).R 167 = [])
    (hrange : EncodedRange A (executionWidth p l target rhsExp) (executionPrecision p l target rhsExp)
      (interiorOutputExponent p l target rhsExp) E)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (hq : executionPrecision p l target rhsExp = executionPrecision p l
      (initialSchurTarget p u (boundaryTableBits p boundaryTarget rhsExp
        (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
 :
    let band := PhaseCellBand.width p u
    let B := haloBoundary s t band a b
    let bits := boundaryTableBits p boundaryTarget rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let W := 12*PhaseCellBand.width p u+1
    ∀ columns : List (ZMod s → GaussianInt),
    PreparedBoundaryColumns A p bits q w W B columns →
    target = boundaryHaloTarget p u boundaryTarget rhsExp B.card →
    (∀ i ∈ B, ∀ j ∈ B, |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-
      (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
        (haloInterior s t band a b).toList).1 i j| ≤ 1/(2 : ℝ)^bits) →
    PackedPreparedBank q w W B.card S →
    let AZ := factorRankIntegerMatrix B W columns
    let K := factorNewtonSteps p q
    let Lc := naturalLineLc q K W B.card AZ
    let Uc := naturalLineUc q K W B.card AZ
    let rcs := naturalLineRcs q K W B.card AZ
    PackedBoundaryFactorPages (cstream A w (Lc.map colC).flatten)
      (cstream A w (Uc.map colC).flatten)
      (cstream A w (rcs.map fun z => (⟨z,0⟩ : GaussianInt))) S →
    boundaryTarget = boundaryRecoveryTarget p finalTarget →
    ∀ y : ZMod s → ℝ,
    SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) y
      (fun k => (value q (C k)).re) →
    (∀ j < b-a, ∀ z ∈ couplingCoefficientWords (2^15*p) q s t u band (a+j), Fits w z ∧ z.im = 0) →
    ∃ v' F n, ∃ D : ZMod s → GaussianInt,
      v'.user = v.user ∧ n ≤ packedHaloPreparedInputCost p u l finalTarget rhsExp s t a b V ∧
      Exec body' (packedHaloPreparedInput hR hQ) (mk v (extendStacks (by decide) S)) n (mk v' F) ∧
      F.R 132 = cstream A w (packedInterval a (b-a) D)++outputTail ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b)
        (fun i => (packedIntervalRead q w a (F.R 132) i).re) y (1/(2 : ℝ)^finalTarget) ∧
      PackedPreparedBank q w W B.card (embStk packedBoundaryRecoveryBase F) ∧
      F.R 110 = tail ∧ F.R 130 = [] ∧ F.R 138 = [] ∧ F.R 139 = [] ∧ F.R 140 = [] ∧
      (∀ i : Fin 117, i ≠ 93 → i ≠ 110 → F.R ⟨i.val,by omega⟩ = []) ∧
      (∀ bo hf df, PackedBoundaryFactorPages bo hf df S →
        PackedBoundaryFactorPages bo hf df (embStk packedBoundaryRecoveryBase F)) ∧
      (∀ k : Fin 248, 242 ≤ k.val → F.L k = [] ∧ F.R k = []) ∧
      PackedHaloRetainedHeaders (2^15*p) (executionStagePrecision p l target rhsExp+1)
        q l s t u band a b V 0 (embStk packedRecoveryRuntimeReg F) ∧
      F.R 127 = [] ∧ F.R 143 = [] ∧ F.R 158 = [] ∧ F.R 167 = [] ∧
      (∀ k ∈ ([129,131,133,134,135,136,153,166] : List (Fin 248)), F.R k = []) ∧
      F.R 125 = [] ∧ F.R 128 = [] ∧ (F.R 157).length ≤ V ∧
      (∀ k : Fin 242, 168 ≤ k.val → k ≠ 238 →
        (embStk packedBoundaryRecoveryBase F).R k = S.R k) := by
  dsimp only
  intro columns hcolumns hcell htable hbank hpages hboundary y hy hcoeff
  let band := PhaseCellBand.width p u
  let B := haloBoundary s t band a b
  let bits := boundaryTableBits p boundaryTarget rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let W := 12*band+1
  obtain ⟨v₁,F,n₁,D,hu₁,hn₁,he₁,hout,herror,hbank₁,hrelease,hnative₁,hprivate₁,hfactorCarry,hheadersFinal,h127Recovery,h143Recovery,h158Recovery,h167Recovery,hscratchRecovery,h125Recovery,h128Recovery,h157Recovery,hsetupRecovery,hleftRecovery⟩ :=
    packedHaloPreparedRecovery_exec (body := body) (body' := body') hbody hR hQ hA hp hα hwidth hst hu hαu hθ hgap
      hbudget hpad C hC hab hb hband hwide hVeq hwV hcoords hunits tail E outputTail
      v S hnative hmasters ha hb' hmeta h157 houtput hE hfresh haLt hfitV h139 h143 hleft
      hsep h158 h167 hrange hdom hq columns hcolumns hcell htable hbank hpages hboundary y hy hcoeff
  have hNV : b-a < 2^V := by omega
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂,hbank₂,hpages₂⟩ := packedPreparedInputRelease_ready_exec
    (body := body') V (b-a) w q W B.card (2*band+1) hNV
    (couplingCoefficientPageInterval (2^15*p) q s t u band a b a (b-a))
    (cstream A w (packedInterval a (b-a) C)) tail v₁ F hrelease hbank₁
  change n₁ ≤ packedHaloPreparedBoundaryCost p u l target boundaryTarget rhsExp s t a b V+
    packedBoundaryRecoveryCost p u l finalTarget rhsExp s t a b V q w at hn₁
  have h132 := packedPreparedInputReleased_frame F tail 132 (by decide)
  refine ⟨v₂,packedPreparedInputReleased F tail,n₁+n₂,D,hu₂.trans hu₁,?_,Exec.seq he₁ he₂,?_,?_,hbank₂,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hn := Nat.add_le_add hn₁ hn₂
    dsimp only [packedHaloPreparedInputCost]
    rw [← hboundary]
    change target = boundaryHaloTarget p u boundaryTarget rhsExp B.card at hcell
    rw [← hcell]
    dsimp only [q,w,bits,B,band] at hn₁ hn₂ ⊢
    omega
  · rw [h132]; exact hout
  · simpa only [h132] using herror
  · simp [packedPreparedInputReleased,packedInputFinished]
  · simp [packedPreparedInputReleased,packedInputFinished]
  · simp [packedPreparedInputReleased,packedInputFinished]
  · simp [packedPreparedInputReleased,packedInputFinished]
  · simp [packedPreparedInputReleased,packedInputFinished]
  · intro i hi93 hi110
    have hi := i.isLt
    have h110 : i.val ≠ 110 := fun he => hi110 (Fin.ext he)
    rw [packedPreparedInputReleased_right]
    simp only [Fin.ext_iff]
    simp [h110,show i.val ≠ 130 by omega,show i.val ≠ 138 by omega,
      show i.val ≠ 139 by omega,show i.val ≠ 140 by omega,hnative₁ i hi93 hi110]
  · intro bo hf df hpages₀
    exact hpages₂ bo hf df (hfactorCarry bo hf df hpages₀)
  · intro k hk
    refine ⟨(hprivate₁ k hk).1,?_⟩
    rw [packedPreparedInputReleased_frame F tail k (by
      simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff]
      omega)]
    exact (hprivate₁ k hk).2
  · apply hheadersFinal.of_frame_except_width
    · simp [embStk,packedRecoveryRuntimeReg,packedPreparedInputReleased,packedInputFinished]
    · intro k hk hne
      simp only [haloRetainedHeaderPorts,couplingMasterPorts,couplingIntervalPorts,
        List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals first
        | exact False.elim (hne rfl)
        | (simp only [embStk,Function.comp_apply]; apply packedPreparedInputReleased_frame; decide)
  · rw [packedPreparedInputReleased_frame F tail 127 (by decide)]; exact h127Recovery
  · rw [packedPreparedInputReleased_frame F tail 143 (by decide)]; exact h143Recovery
  · rw [packedPreparedInputReleased_frame F tail 158 (by decide)]; exact h158Recovery
  · rw [packedPreparedInputReleased_frame F tail 167 (by decide)]; exact h167Recovery
  · intro k hk
    have hnot : k ∉ ([110,130,138,139,140] : List (Fin 248)) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [packedPreparedInputReleased_frame F tail k hnot]
    exact hscratchRecovery k hk
  · rw [packedPreparedInputReleased_frame F tail 125 (by decide)]; exact h125Recovery
  · rw [packedPreparedInputReleased_frame F tail 128 (by decide)]; exact h128Recovery
  · rw [packedPreparedInputReleased_frame F tail 157 (by decide)]; exact h157Recovery

  · intro k hk hne
    change (packedPreparedInputReleased F tail).R (packedBoundaryRecoveryBase k) = S.R k
    rw [packedPreparedInputReleased_frame F tail _ (by
      simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,packedBoundaryRecoveryBase,Fin.val_castLE]
      omega)]
    exact hsetupRecovery k hk hne

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
