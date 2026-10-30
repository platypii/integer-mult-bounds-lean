module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedPackedHaloRealBoundaryData

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryFinish
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryReadAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloRecoveryBoundaryFormat
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleasePackedRecoveryHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryFactorFrame

/-! Complete local recovery from the actual folded boundary solution. Numerical
stability, physical execution and final tape reads meet at one shared format. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

theorem packedBoundaryRecovery_buffers_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p u l target rhsExp s t a b V q w W : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hu : 1 ≤ u) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t)
    (hαu : α^2 = (u : ℝ)) (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (hab : a ≤ b) (hb : b ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (hsep : b-a+PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (hq : q = executionPrecision p l (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp
        (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
    (hw : w = executionWidth p l (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp
        (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
    (C : ZMod s → GaussianInt) (solution : List GaussianInt) (x : ZMod s → ℝ)
    (hC : ∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^rhsExp)
    (hlen : solution.length = (haloBoundary s t (PhaseCellBand.width p u) a b).card)
    (hfits : ∀ z ∈ solution, Fits w z)
    (hsolution : ∀ i < (haloBoundary s t (PhaseCellBand.width p u) a b).card,
      ‖value q (solution.getD i 0)-(x (bFoldAt s (haloBoundary s t (PhaseCellBand.width p u) a b) i) : ℂ)‖ ≤
        3/(2 : ℝ)^boundaryRecoveryTarget p target ∧
      ‖value q (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p rhsExp)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x (fun i => (value q (C i)).re))
    (D₀ : ZMod s → GaussianInt)
    (solutionTail outputTail rhsTail : List (Fin (A+4)))
     
    (v : HS 248 Q A U) (S : Stacks 248 A)
    (hbank : PackedPreparedBank q w W (haloBoundary s t (PhaseCellBand.width p u) a b).card
      (embStk packedBoundaryRecoveryBase S))
    (hbuffers : PackedHaloRecoveryBuffers p s t u a b q w C D₀ rhsTail outputTail
      (embStk packedBoundaryRecoveryBase S))
    
    
    (h143 : S.R 143 = []) 
    (hsrc : S.R 238 = cstream A w solution++solutionTail) (hN : S.R 165 = binSyms V (b-a))
    
    
    
    (hfreshL : ∀ i : Fin 248, 242 ≤ i.val → S.L i = [])
    (hfreshR : ∀ i : Fin 248, 242 ≤ i.val → S.R i = [])
    (hheaders : CouplingMasterHeaders (2^15*p) q w s t u (PhaseCellBand.width p u) a b (embStk packedRecoveryRuntimeReg S))
    (hstage : (S.R 118).length = executionStagePrecision p l (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp
        (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
    (hlevel : (S.R 120).length = l)
    (hnative : ∀ i : Fin 117, i ≠ 93 → i ≠ 110 → i ≠ 116 → S.R ⟨i.val,by omega⟩ = [])
    (hclean : ∀ k ∈ ([127,129,131,133,134,135,136,153,158,166] : List (Fin 248)), S.R k = [])
    
    
    
    (has : ∀ j < b-a, ∀ z ∈ couplingCoefficientWords (2^15*p) q s t u (PhaseCellBand.width p u) (a+j), Fits w z ∧ z.im = 0)
    (hwide : 8*(t+1)^2+4*PhaseCellBand.width p u+8 < 2^V)
    (hfitV : a+((b-a)+2*PhaseCellBand.width p u)+s < 2^V)
    (hVeq : V = weightWorkspaceWidth (2^15*p) q (2*q+8) t u)
    (hwV : w < 2^V) (hcoords : b < 2^V) (hunits : b*w < 2^V)
    (hgeometry : CouplingIntervalMetadata V s t (PhaseCellBand.width p u) a b a (b-a) (embStk packedRecoveryRuntimeReg S)) :
    ∃ v' F n, ∃ D : ZMod s → GaussianInt, v'.user = v.user ∧
      n ≤ packedBoundaryRecoveryCost p u l target rhsExp s t a b V q w ∧
      Exec body (packedBoundaryRecovery hR hQ) (mk v S) n (mk v' F) ∧
      F.R 93 = S.R 93 ∧ F.R 139 = S.R 139 ∧ F.R 238 = solutionTail ∧ F.inp = S.inp ∧ F.out = S.out ∧
      F.R 132 = cstream A w (packedInterval a (b-a) D)++outputTail ∧ (∀ i, Fits w (D i)) ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b) (fun i => (packedIntervalRead q w a (F.R 132) i).re) x (1/(2 : ℝ)^target) ∧
      (∃ residual : List (Fin (A+4)), residual.length = (b-a)*w ∧
        F.R 110 = residual++(cstream A w (packedInterval a (b-a) C)++rhsTail)) ∧
      (∀ i : Fin 117, i ≠ 93 → i ≠ 110 → F.R ⟨i.val,by omega⟩ = []) ∧
      F.L = S.L ∧ (∀ k ∈ packedRecoveryRetainedPorts, F.R k = S.R k) ∧
      PackedBoundarySolveWorkspace q (embStk packedBoundaryRecoveryBase F) ∧
      BoundarySolveReady (boundaryFactorState (embStk preparedBoundaryCoreReg
        (embStk packedBoundaryFactorReg (embStk packedBoundaryRecoveryBase F)))) q w W
        (haloBoundary s t (PhaseCellBand.width p u) a b).card ∧
      (∀ k : Fin 248, 242 ≤ k.val → F.L k = [] ∧ F.R k = []) ∧
      (∀ k : Fin 248, 168 ≤ k.val → k.val < 242 → k ≠ 238 → F.R k = S.R k) ∧
      (∀ bo hf df, PackedBoundaryFactorPages bo hf df (embStk packedBoundaryRecoveryBase S) →
        PackedBoundaryFactorPages bo hf df (embStk packedBoundaryRecoveryBase F)) ∧
      F.R 127 = [] ∧ F.R 143 = [] ∧ F.R 158 = [] ∧ F.R 167 = [] ∧
      (∀ k ∈ ([129,131,133,134,135,136,153,166] : List (Fin 248)), F.R k = []) := by
  have hlocal : a+(b-a) ≤ s := by omega
  exact packedBoundaryRecovery_spec hR hQ hA hp hu hwidth hα hst hαu hθ hgap hbudget hdom
    hab hb hband hsep hpad hq hw C solution x hC hlen hfits hsolution hx solutionTail
    (cstream A w (packedInterval a (b-a) D₀)) outputTail
    (cstream A w (packedInterval a (b-a)
      (guardedCouplingRowField (2^15*p) q t u (PhaseCellBand.width p u) a b false D₀ C))) rhsTail
    (by simp only [length_cstream,packedInterval_length _ hlocal])
    (by simp only [length_cstream,packedInterval_length _ hlocal]) v S
    hbank.workspace hbank.ready h143 hbuffers.boundaryCount hsrc hN hbuffers.mask
    hbuffers.interior hbuffers.source hfreshL hfreshR hheaders hstage hlevel hnative hclean
    (by change ((embStk packedBoundaryRecoveryBase S).R 140).length = _
        rw [hbuffers.rowCount]; simp) hbuffers.page
    (by change ((embStk packedBoundaryRecoveryBase S).R 139).length = _
        rw [hbuffers.pageCount]; simp)
    has hwide hfitV hVeq hwV hcoords hunits hgeometry

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
