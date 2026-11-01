module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedLocalFeedCouplingInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedLocalFeedCouplingInterval
public import IntegerMultBounds.MathlibTM2.Host.EmbedStockTrace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedCouplingHeaders

/-! Execute local coupling using the retained master headers in place. Static
register renaming adds no machine steps, and every master is restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 168 Q A U}

noncomputable def cachedSharedLocalFeedCouplingInterval (hQ : SS.states ≤ Q) : Pr P₀ 168 Q A U :=
  embProg sharedCouplingReg Empty.elim (cachedLocalFeedCouplingInterval hQ)

theorem cachedSharedLocalFeedCouplingInterval_exec_within (hQ : SS.states ≤ Q) {P q w s t u band a b origin N : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t)
    (C B : ZMod s → GaussianInt)
    (hfit : origin+N ≤ s)
    (tail pageTail rhsTail raw : List (Fin (A+4)))
    (K : ℕ) (hpush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ K) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hready : RetainedCouplingReady P q w s t u band a b raw (embStk sharedCouplingCoreReg S))
    (hlocalOrigin : origin = a) (hlocalEnd : b = a+N) (hsep : N+band ≤ s)
    (hsource : S.R 132 = cstream A w (packedInterval a N C)++tail) (h127 : S.R 127 = [])
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (couplingCoefficientPageInterval P q s t u band a b origin N)++pageTail)
    (hrhs : S.R 93 = cstream A w (packedInterval origin N B)++rhsTail)
    (h143 : S.R 143 = [])
    (hCfits : ∀ j, Fits w (C j))
    (has : ∀ j < N, ∀ z ∈ couplingCoefficientWords P q s t u band (origin+j), Fits w z ∧ z.im = 0)
    (V : ℕ) (hNV : N < 2^V) (h165 : S.R 165 = binSyms V N) (h166 : S.R 166 = [])
    (h139 : (S.R 139).length = (couplingCoefficientPageInterval P q s t u band a b origin N).length)
    (hbS : b ≤ s) (hbandS : band ≤ s)
    (h159 : S.R 159 = (couplingRibbonFlags (s := s) boundary t band a b origin N).map
      (fun flag => pairSym A flag flag))
    (h161 : S.R 161 = recoveryGuardIntervalSymbols true A s t (2*band) a b origin N)
    (h158 : S.R 158 = []) (h135 : S.R 135 = []) (h167 : S.R 167 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (((16*N*w+21*N+14*band*w+13*band+11*V+46)+cachedGatheredRibbonCost (N+2*band) w+(12*((N+2*band)*w)+11*(N+2*band)+14)) +
        (12*((N+2*band)*w)+17*N+26*band+11*V+24) +
        ((6*N+6)+(6*N+11*V+6+(retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin N+
        (22*N+22*V+22+transferCountedLineCost N w+
          transferCountedLineCost (couplingCoefficientPageInterval P q s t u band a b origin N).length w))))) + (28*N*w+36*N+11*V+26) ∧
      ∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(cachedLocalCouplingWorkspace (Q := Q) (A := A) (U := U) P K q w s t u band a b origin N V+mnProgPush (feedPackedCouplingResult (P₀ := Empty) (Q := Q) (A := A) (U := U))*(28*N*w+36*N+11*V+26)))
        depth (cachedSharedLocalFeedCouplingInterval hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 93 rhsTail) 110
          (cstream A w (packedInterval origin N (guardedCouplingRowField P q t u band a b boundary C B))++S.R 110))}) := by
  let T := embStk sharedCouplingReg S
  have hreadyT : RetainedCouplingReady P q w s t u band a b raw
      (embStk groupReg (embStk intervalPageReg T)) := by
    change RetainedCouplingReady P q w s t u band a b raw
      (embStk groupReg (embStk intervalPageReg (embStk sharedCouplingReg S)))
    rw [sharedCouplingCore_view sharedCouplingReg S]
    exact hready
  obtain ⟨vi,m,hui,hm,hei⟩ := cachedLocalFeedCouplingInterval_exec_within (P := P) (q := q) (w := w) (s := s) (t := t)
    (u := u) (band := band) (a := a) (b := b) (origin := origin) (N := N) (body := fun p : Empty => nomatch p)
    hQ boundary hA hw5 hqw hst C B hfit tail pageTail rhsTail raw K hpush (embDn sharedCouplingReg v) T
    hreadyT hlocalOrigin hlocalEnd hsep
    (by simpa [T,embStk,sharedCouplingReg,Equiv.swap_apply_def] using hsource)
    (by simpa [T,embStk,sharedCouplingReg,Equiv.swap_apply_def] using h127)
    (by simpa [T,embStk,sharedCouplingReg,Equiv.swap_apply_def] using hrows)
    (by simpa [T,embStk,sharedCouplingReg,Equiv.swap_apply_def] using hpage)
    (by simpa [T,embStk,sharedCouplingReg,Equiv.swap_apply_def] using hrhs)
    (by simpa [T,embStk,sharedCouplingReg,Equiv.swap_apply_def] using h143) hCfits has V hNV
    (by simpa [T,embStk,sharedCouplingReg,Equiv.swap_apply_def] using h165)
    (by simpa [T,embStk,sharedCouplingReg,Equiv.swap_apply_def] using h166)
    (by simpa [T,embStk,sharedCouplingReg,Equiv.swap_apply_def] using h139)
    hbS hbandS
    (by simpa [T,embStk,sharedCouplingReg,Equiv.swap_apply_def] using h159)
    (by simpa [T,embStk,sharedCouplingReg,Equiv.swap_apply_def] using h161)
    (by simpa [T,embStk,sharedCouplingReg,Equiv.swap_apply_def] using h158)
    (by simpa [T,embStk,sharedCouplingReg,Equiv.swap_apply_def] using h135)
    (by simpa [T,embStk,sharedCouplingReg,Equiv.swap_apply_def] using h167)
  obtain ⟨v',hv,hu,he⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    sharedCouplingReg_injective (fun p => nomatch p) (hei 0).toExec v rfl S rfl
  refine ⟨v',m,hu.trans hui,hm,?_⟩
  intro depth
  have ht := exec_emb_within_stock_of_exec (ι := Empty.elim) (body' := body)
    sharedCouplingReg_injective (fun p => nomatch p) (hei depth) v rfl S rfl he
  refine ht.cast rfl ?_
  apply congrArg (mk v')
  let T₁ : Stacks 168 A := {T with R := Function.update T.R 93 rhsTail}
  change embOvr sharedCouplingReg
    ({T₁ with R := (Function.update T₁.R 110
      (cstream A w (packedInterval origin N (guardedCouplingRowField P q t u band a b boundary C B))++T.R 110))} : Stacks 168 A).get S = _
  rw [embOvr_updR sharedCouplingReg_injective T₁]
  dsimp only [T₁]
  rw [embOvr_updR sharedCouplingReg_injective T,embOvr_stk]
  simp only [T,embStk,Function.comp_apply,sharedCouplingReg_rhs,sharedCouplingReg_source]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
