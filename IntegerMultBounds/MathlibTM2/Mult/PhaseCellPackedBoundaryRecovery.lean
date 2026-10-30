module

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

noncomputable def packedBoundaryRecovery (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 248 Q A U :=
  .seq (packedRecoveryFinish hR hQ) releasePackedRecoveryHeaders

def packedBoundaryRecoveryCost (p u l target rhsExp s t a b V q w : ℕ) [NeZero s] : ℕ :=
  let band := PhaseCellBand.width p u
  let n := (haloBoundary s t band a b).card
  let k := boundaryHaloRecoveryTarget p (boundaryRecoveryTarget p target) n
  let e := recoveryRhsExponent p rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)
  packedBoundaryRecoveryInputsCost V (b-a) n w+
    preparedSharedLocalFeedCouplingIntervalCost true (2^15*p) q w s t u band a b a (b-a) V+
    (initializeHaloLengthKeysCost (2^15*p) (executionStagePrecision p l k e+1)
      (executionPrecision p l k e) l s t u band a b+
      packedHaloKeyLoopCost p l s t u k e a b V (haloLengthKeys s t band a b)+1)+
    (2*(2*V+((s/(t-s)+1)-2*band)+w)+9)

theorem packedBoundaryRecovery_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (solutionTail words outputTail residual rhsTail : List (Fin (A+4)))
    (hwords : words.length = (b-a)*w) (hresidual : residual.length = (b-a)*w)
    (v : HS 248 Q A U) (S : Stacks 248 A)
    (hwork : PackedBoundarySolveWorkspace q (embStk packedBoundaryRecoveryBase S))
    (hready : BoundarySolveReady (boundaryFactorState (embStk preparedBoundaryCoreReg
      (embStk packedBoundaryFactorReg (embStk packedBoundaryRecoveryBase S)))) q w W
      (haloBoundary s t (PhaseCellBand.width p u) a b).card)
    (h143 : S.R 143 = []) (hcount : S.R 116 = List.replicate (haloBoundary s t (PhaseCellBand.width p u) a b).card tick)
    (hsrc : S.R 238 = cstream A w solution++solutionTail) (hN : S.R 165 = binSyms V (b-a))
    (hmask : S.R 167 = couplingSourceIntervalMaskSymbols true A s t (PhaseCellBand.width p u) a b a (b-a))
    (houtput : S.R 132 = words++outputTail)
    (hrhsSource : S.R 110 = residual++(cstream A w (packedInterval a (b-a) C)++rhsTail))
    (hfreshL : ∀ i : Fin 248, 242 ≤ i.val → S.L i = [])
    (hfreshR : ∀ i : Fin 248, 242 ≤ i.val → S.R i = [])
    (hheaders : CouplingMasterHeaders (2^15*p) q w s t u (PhaseCellBand.width p u) a b (embStk packedRecoveryRuntimeReg S))
    (hstage : (S.R 118).length = executionStagePrecision p l (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp
        (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
    (hlevel : (S.R 120).length = l)
    (hnative : ∀ i : Fin 117, i ≠ 93 → i ≠ 110 → i ≠ 116 → S.R ⟨i.val,by omega⟩ = [])
    (hclean : ∀ k ∈ ([127,129,131,133,134,135,136,153,158,166] : List (Fin 248)), S.R k = [])
    (hrows : (S.R 140).length = 2*PhaseCellBand.width p u+1)
    (hpage : S.R 138 = cstream A w (couplingCoefficientPageInterval (2^15*p) q s t u (PhaseCellBand.width p u) a b a (b-a)))
    (h139 : (S.R 139).length = (couplingCoefficientPageInterval (2^15*p) q s t u (PhaseCellBand.width p u) a b a (b-a)).length)
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
  let band := PhaseCellBand.width p u
  let B := haloBoundary s t band a b
  let solveTarget := boundaryRecoveryTarget p target
  let T := initialSchurTarget p u (boundaryTableBits p solveTarget rhsExp B.card) 2
  let k := boundaryHaloRecoveryTarget p solveTarget B.card
  let e := recoveryRhsExponent p rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)
  let Y := boundarySolutionField B solution
  let R := guardedCouplingRowField (2^15*p) q t u band a b true Y C
  have hq₀ : q = executionPrecision p l T 2 := hq
  have hw₀ : w = executionWidth p l T 2 := hw
  obtain ⟨hqs,hstages,hws⟩ := boundaryHaloRecoveryTarget_sizing p u l solveTarget rhsExp B.card
  have hq' : q = executionPrecision p l k e := hq₀.trans hqs
  have hw' : w = executionWidth p l k e := hw₀.trans hws
  have hnum := haloRecovery_boundary_format_spec p u l target rhsExp a b hp hwidth hα hst hαu hθ hgap hbudget hb hdom
    C solution x (by simpa only [hq] using hC) (by simpa only [hq] using hsolution)
    (by simpa only [hq] using hx)
  obtain ⟨xI,hxI,haccept⟩ := hnum.2.2
  have hnorm : ∀ i, ‖value q (R i)‖ ≤ (2 : ℝ)^e := by simpa only [← hq,R,Y,B,band] using hnum.1
  have hww : w = 2*q+8 := by rw [hw₀,hq₀]; unfold executionWidth executionPrecision; omega
  have hp0 : 0 < p := by omega
  have hθ0 : 0 < (t : ℝ)/s-1 := lt_of_lt_of_le (by positivity) hθ
  have hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+(b-a) := by
    intro i hi
    have hh := (mem_haloVertices a b i).mp (Finset.mem_sdiff.mp hi).1
    omega
  have hcleanRhs : ∀ i ∈ ([127,135,158,166] : List (Fin 248)), S.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> exact hclean _ (by decide)
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := packedBoundaryRecoveryRhs_exec (body := body) hQ hst hA V band a b (2^15*p) q w W
    (by omega) hb (by omega) hB solution hlen C hfits solutionTail words outputTail hwords
    v S hwork hready h143 hcount hsrc hN hmask houtput residual rhsTail hresidual hrhsSource
    hfreshL hfreshR hheaders hnative hcleanRhs (by omega) (by omega) rfl (by omega) hsep (by omega)
    hband hrows hpage h139 has hwide hfitV hgeometry
  have hex : Exec body (packedBoundaryRecoveryRhs hQ) (mk v S) n₁
      (mk v₁ (packedRecoveryRhsState w a b Y R C solutionTail outputTail rhsTail S)) := by
    simpa only [packedRecoveryRhsState,Y,R,B,band] using he₁
  have hrange := haloRecovery_boundary_range A p u l k rhsExp q w a (b-a) B solution
    (fun i hi => (hsolution i hi).2)
  obtain ⟨v₂,F,n,E',D,hu₂,hn₂,he₂,h93,h139',h238,hi,ho,hrdy,hout,hDnorm,hDfits,herror,hframe,hleft,hretained,h245,h246,hlength,hfactors,h127,h143Final,h158Final,h167Final⟩ :=
    packedRecoveryFinish_exec (body := body) hR hQ hA hp0 hst hu hαu hθ0 hgap hbudget hpad hq' hw'
      Y R C hnorm hab hb hband (by omega) (by simpa only [hq'] using hVeq)
      (by simpa only [← hw'] using hwV) hcoords (by simpa only [← hw'] using hunits)
      solutionTail outputTail rhsTail v v₁ S n₁ hu₁ hex hwork hheaders
      (hstage.trans (congrArg (fun n => n+1) hstages)) hlevel hnative hgeometry hclean hfreshR hrange xI
      (by simpa only [← hq,R,Y,B,band] using hxI)
  have hnativeFinal : ∀ i : Fin 117, i ≠ 93 → i ≠ 110 →
      F.R ⟨i.val,by omega⟩ = [] := by
    intro i hi93 hi110
    have hh := congrArg (fun G : Stacks 117 A => G.R i) hrdy.native
    have hlow := packedRecoveryInteriorReg_low (packedCellCoreReg i)
      (by change i.val < 117; exact i.isLt)
    simp only [embStk,Function.comp_def] at hh
    rw [hlow] at hh
    simpa [packedCellCoreReg,releasedCellBank,
      show i.val ≠ 93 from fun h => hi93 (Fin.ext h),
      show i.val ≠ 110 from fun h => hi110 (Fin.ext h)] using hh
  have hbankFinal : PackedPreparedBank q w W B.card
      (embStk packedBoundaryRecoveryBase F) := by
    apply (PackedPreparedBank.mk hready hwork).of_recovery_frame
    · funext i
      exact congrFun hleft (packedBoundaryRecoveryBase i)
    · intro i
      have hi := i.isLt
      exact hnativeFinal ⟨i.val,by omega⟩
        (by intro he; have hh := congrArg Fin.val he; change i.val = 93 at hh; omega)
        (by intro he; have hh := congrArg Fin.val he; change i.val = 110 at hh; omega)
    · exact hretained 119 (by decide)
    · intro k hk hne
      exact hfactors (packedBoundaryRecoveryBase k) hk k.isLt (by
        intro he
        exact hne (Fin.ext (congrArg (fun i : Fin 248 => i.val) he)))
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := releasePackedRecoveryHeaders_exec (body := body) v₂ F hrdy _ hlength
  have hprefix : embStk packedBoundaryRecoveryBase (releasedPackedRecoveryHeaders F) =
      embStk packedBoundaryRecoveryBase F := releasedPackedRecoveryHeaders_prefix F
  refine ⟨v₃,releasedPackedRecoveryHeaders F,n+n₃,D,hu₃.trans hu₂,?_,
    Exec.seq he₂ he₃,?_,?_,?_,hi,ho,?_,hDfits,?_,?_,?_,hleft,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact Nat.add_le_add (hn₂.trans (Nat.add_le_add_right hn₁ _)) hn₃
  · exact (releasedPackedRecoveryHeaders_low F 93 (by decide)).trans h93
  · exact (releasedPackedRecoveryHeaders_low F 139 (by decide)).trans h139'
  · exact (releasedPackedRecoveryHeaders_low F 238 (by decide)).trans h238
  · exact (releasedPackedRecoveryHeaders_low F 132 (by decide)).trans hout
  · exact packedRecovery_read_error (by omega) (by omega) hab hb Y D
      (boundarySolutionField_fits w B solution hlen hfits) hDfits outputTail (F.R 132) hout hframe x _
      (by simpa only [← hq,Y,B,band] using haccept D (by simpa only [hq] using herror))

  · refine ⟨cstream A w (packedInterval a (b-a) R),?_,?_⟩
    · rw [length_cstream,packedInterval_length R (by omega)]
    · have hh := congrArg (fun G : Stacks 117 A => G.R 110) hrdy.native
      simp only [embStk,Function.comp_def] at hh
      rw [packedRecoveryInteriorReg_low (packedCellCoreReg 110) (by decide)] at hh
      simpa [packedCellCoreReg,releasedCellBank,releasedPackedRecoveryHeaders,packedRecoveryHeaderPorts] using hh

  · intro i hi93 hi110
    rw [releasedPackedRecoveryHeaders_low F _ (by have := i.isLt; change i.val < 242; omega)]
    exact hnativeFinal i hi93 hi110
  · intro k hk
    rw [releasedPackedRecoveryHeaders_low F k (by
      have hs : k.val < 168 := (packedRecoveryRetainedPorts_safe k hk).2.1
      omega)]
    exact hretained k hk
  · rw [hprefix]; exact hbankFinal.workspace
  · rw [hprefix]; exact hbankFinal.ready
  · intro k hk
    refine ⟨(congrFun hleft k).trans (hfreshL k hk),?_⟩
    have hi := k.isLt
    by_cases h245k : k = 245
    · subst k; simpa [releasedPackedRecoveryHeaders,packedRecoveryHeaderPorts] using h245
    by_cases h246k : k = 246
    · subst k; simpa [releasedPackedRecoveryHeaders,packedRecoveryHeaderPorts] using h246
    have hm : k ∈ packedRecoveryHeaderPorts := by
      simp only [packedRecoveryHeaderPorts,List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at h245k h246k ⊢
      omega
    simp only [releasedPackedRecoveryHeaders,if_pos hm]
  · intro k hk hk' hne
    rw [releasedPackedRecoveryHeaders_low F k hk']
    exact hfactors k hk hk' hne
  · intro bo hf df hpages
    rw [hprefix]
    apply hpages.of_solution_frame
    intro k hk hne
    exact hfactors (packedBoundaryRecoveryBase k) hk k.isLt (by
      intro he
      exact hne (Fin.ext (congrArg (fun i : Fin 248 => i.val) he)))
  · rw [releasedPackedRecoveryHeaders_low F 127 (by decide)]; exact h127
  · rw [releasedPackedRecoveryHeaders_low F 143 (by decide)]; exact h143Final.trans h143
  · rw [releasedPackedRecoveryHeaders_low F 158 (by decide)]; exact h158Final.trans (hclean 158 (by decide))
  · rw [releasedPackedRecoveryHeaders_low F 167 (by decide)]; exact h167Final
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [releasedPackedRecoveryHeaders_low F 129 (by decide)]
      have hh := hrdy.fresh 129 (by decide)
      simpa [embStk,Function.comp_def,packedRecoveryInteriorReg,packedRecoveryInteriorPerm,
        Equiv.swap_apply_def] using hh
    · rw [releasedPackedRecoveryHeaders_low F 131 (by decide)]
      have hh := hrdy.fresh 131 (by decide)
      simpa [embStk,Function.comp_def,packedRecoveryInteriorReg,packedRecoveryInteriorPerm,
        Equiv.swap_apply_def] using hh
    · rw [releasedPackedRecoveryHeaders_low F 133 (by decide)]
      have hh := hrdy.fresh 133 (by decide)
      simpa [embStk,Function.comp_def,packedRecoveryInteriorReg,packedRecoveryInteriorPerm,
        Equiv.swap_apply_def] using hh
    · rw [releasedPackedRecoveryHeaders_low F 134 (by decide)]
      have hh := hrdy.fresh 134 (by decide)
      simpa [embStk,Function.comp_def,packedRecoveryInteriorReg,packedRecoveryInteriorPerm,
        Equiv.swap_apply_def] using hh
    · rw [releasedPackedRecoveryHeaders_low F 135 (by decide)]
      have hh := hrdy.fresh 135 (by decide)
      simpa [embStk,Function.comp_def,packedRecoveryInteriorReg,packedRecoveryInteriorPerm,
        Equiv.swap_apply_def] using hh
    · rw [releasedPackedRecoveryHeaders_low F 136 (by decide)]
      have hh := hrdy.fresh 136 (by decide)
      simpa [embStk,Function.comp_def,packedRecoveryInteriorReg,packedRecoveryInteriorPerm,
        Equiv.swap_apply_def] using hh
    · rw [releasedPackedRecoveryHeaders_low F 153 (by decide)]
      have hh := hrdy.fresh 153 (by decide)
      simpa [embStk,Function.comp_def,packedRecoveryInteriorReg,packedRecoveryInteriorPerm,
        Equiv.swap_apply_def] using hh
    · rw [releasedPackedRecoveryHeaders_low F 166 (by decide)]
      have hh := hrdy.fresh 166 (by decide)
      simpa [embStk,Function.comp_def,packedRecoveryInteriorReg,packedRecoveryInteriorPerm,
        Equiv.swap_apply_def] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
