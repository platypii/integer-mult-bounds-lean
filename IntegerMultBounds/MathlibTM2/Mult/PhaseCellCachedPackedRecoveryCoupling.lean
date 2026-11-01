module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingMasterHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRecoveryUnfold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedPreparedSharedLocalFeed
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryCoupling
public import IntegerMultBounds.MathlibTM2.Host.EmbedStockTrace

/-! Execute the second Schur coupling pass beside retained factors, reading the
published boundary field locally and reusing the original coefficient page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

noncomputable def cachedPackedRecoveryCoupling (hQ : SS.states ≤ Q) : Pr P 248 Q A U :=
  embProg packedRecoveryRuntimeReg Empty.elim (cachedPreparedSharedLocalFeedCouplingInterval hQ)

theorem cachedPackedRecoveryCoupling_exec_within (hQ : SS.states ≤ Q)
    {precision q w s t u band a b origin N : ℕ} [NeZero s]
    (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w) (hst : s < t)
    (Y C : ZMod s → GaussianInt) (hfit : origin+N ≤ s)
    (outputTail pageTail rhsTail : List (Fin (A+4)))
    (M : ℕ) (hpush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ M) (v : HS 248 Q A U) (S : Stacks 248 A)
    (hwork : PackedBoundarySolveWorkspace q (embStk packedBoundaryRecoveryBase S))
    (hheaders : CouplingMasterHeaders precision q w s t u band a b (embStk packedRecoveryRuntimeReg S))
    (hnative : ∀ i : Fin 117, i ≠ 93 → i ≠ 110 → S.R ⟨i.val,by omega⟩ = [])
    (hlocalOrigin : origin = a) (hlocalEnd : b = a+N) (hsep : N+band ≤ s)
    (hsource : S.R 132 = cstream A w (packedInterval a N Y)++outputTail)
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (couplingCoefficientPageInterval precision q s t u band a b origin N)++pageTail)
    (hrhs : S.R 93 = cstream A w (packedInterval origin N C)++rhsTail)
    (hYfits : ∀ j, Fits w (Y j))
    (has : ∀ j < N, ∀ z ∈ couplingCoefficientWords precision q s t u band (origin+j), Fits w z ∧ z.im = 0)
    (V : ℕ) (hNV : N < 2^V) (h165 : S.R 165 = binSyms V N) (h139 : (S.R 139).length = (couplingCoefficientPageInterval precision q s t u band a b origin N).length)
    (hbS : b ≤ s) (hbandS : band ≤ s)
    (h159 : S.R 159 = (couplingRibbonFlags (s := s) true t band a b origin N).map
      (fun flag => pairSym A flag flag))
    (h161 : S.R 161 = recoveryGuardIntervalSymbols true A s t (2*band) a b origin N)
    (hclean : ∀ k ∈ ([127,143,166,158,135,167] : List (Fin 248)), S.R k = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ cachedPreparedSharedLocalFeedCouplingIntervalCost true precision q w s t u band a b origin N V ∧
      ∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          cachedPreparedSharedLocalFeedCouplingWorkspace (Q := Q) (A := A) (U := U)
            precision M q w s t u band a b origin N V)
        depth (cachedPackedRecoveryCoupling hQ) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 93 rhsTail) 110
          (cstream A w (packedInterval origin N
            (guardedCouplingRowField precision q t u band a b true Y C))++S.R 110))}) := by
  let T := embStk packedRecoveryRuntimeReg S
  have hleft : ∀ i : Fin 117, T.L (packedCellCoreReg i) = [] := by
    intro i
    have hi := i.isLt
    simpa [T,embStk,packedCellCoreReg,packedRecoveryRuntimeReg,packedBoundaryRecoveryBase,preparedBoundaryCoreReg,
      packedBoundaryFactorReg,Fin.ext_iff,show i.val ≠ 140 by omega,
      show i.val ≠ 143 by omega,show i.val ≠ 206 by omega,show i.val < 154 by omega]
      using hwork.left ⟨i.val,by omega⟩
  have hmasterLeft : ∀ k ∈ ([(121 : Fin 168),122,123,124]), T.L k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact hwork.left 121
    · exact hwork.left 122
    · exact hwork.left 123
    · exact hwork.left 124
  have hready := hheaders.ready hleft (fun i h93 h110 => hnative i h93 h110) hmasterLeft
  obtain ⟨v₁,n,hu₁,hn,he⟩ := cachedPreparedSharedLocalFeedCouplingInterval_exec_within
    (body := fun p : Empty => nomatch p) hQ true hA hw5 hqw hst Y C hfit
    outputTail pageTail rhsTail (S.R 110) M hpush (embDn packedRecoveryRuntimeReg v) T hready
    hlocalOrigin hlocalEnd hsep hsource (hclean 127 (by decide)) hrows hpage hrhs
    (hclean 143 (by decide)) hYfits has V hNV h165 (hclean 166 (by decide)) h139
    hbS hbandS h159 h161 (hclean 158 (by decide))
    (hclean 135 (by decide)) (hclean 167 (by decide))
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    packedRecoveryRuntimeReg_injective (fun p => nomatch p) (he 0).toExec v rfl S rfl
  refine ⟨v₂,n,hu₂.trans hu₁,hn,?_⟩
  intro depth
  have ht := exec_emb_within_stock_of_exec (ι := Empty.elim) (body' := body)
    packedRecoveryRuntimeReg_injective (fun p => nomatch p) (he depth) v rfl S rfl he₂
  refine ht.cast rfl ?_
  apply congrArg (mk v₂)
  rw [embOvr_updateR_updateR packedRecoveryRuntimeReg_injective]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
