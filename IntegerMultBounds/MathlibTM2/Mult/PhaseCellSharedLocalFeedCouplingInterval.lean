module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalFeedCouplingInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedCouplingHeaders

/-! Execute local coupling using the retained master headers in place. Static
register renaming adds no machine steps, and every master is restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 168 Q A U}

noncomputable def sharedLocalFeedCouplingInterval (hQ : SS.states ≤ Q) (boundary : Bool) : Pr P₀ 168 Q A U :=
  embProg sharedCouplingReg Empty.elim (localFeedCouplingInterval (P₀ := Empty) hQ boundary)

theorem sharedCouplingCore_view {A : ℕ} (e : Fin 168 → Fin 168) (S : Stacks 168 A) :
    embStk groupReg (embStk intervalPageReg (embStk e S)) =
      embStk (fun i : Fin 117 => e (packedCellCoreReg i)) S := rfl

theorem sharedLocalFeedCouplingInterval_exec (hQ : SS.states ≤ Q) {P q w s t u band a b origin N : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t)
    (C B : ZMod s → GaussianInt)
    (hfit : origin+N ≤ s)
    (tail pageTail rhsTail raw : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hready : RetainedCouplingReady P q w s t u band a b raw (embStk sharedCouplingCoreReg S))
    (hlocalOrigin : origin = a) (hlocalEnd : b = a+N) (hsep : N+band ≤ s)
    (hsource : S.R 132 = cstream A w (packedInterval a N C)++tail) (h127 : S.R 127 = [])
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (couplingCoefficientPageInterval P q s t u band a b origin N)++pageTail)
    (hrhs : S.R 93 = cstream A w (packedInterval origin N B)++rhsTail)
    (h143 : S.R 143 = [])
    (hCfits : ∀ j, Fits w (C j))
    (has : ∀ j < N, ∀ z ∈ couplingCoefficientWords P q s t u band (origin+j), Fits w z ∧ z.im = 0)
    (V : ℕ) (h166 : S.R 166 = [])
    (h139 : (S.R 139).length = (couplingCoefficientPageInterval P q s t u band a b origin N).length)
    (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (hwide : 8*(t+1)^2+4*band+8 < 2^V)
    (hfitV : origin+(N+2*band)+s < 2^V)
    (hgeometry : CouplingIntervalMetadata V s t band a b origin N S)
    (h158 : S.R 158 = []) (h135 : S.R 135 = []) (h167 : S.R 167 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (((16*N*w+21*N+14*band*w+13*band+11*V+46)+(152*V+153+((32*(N+2*band)+2)*tblC V 1+68*V+2*(N+2*band)+72)+maskCouplingSourceCost (N+2*band) w)+(12*((N+2*band)*w)+11*(N+2*band)+14)) +
        (12*((N+2*band)*w)+17*N+26*band+11*V+24) +
        (144*V+145+((46*N+2)*tblC V 1+66*V+2*N+70)+(6*N+11*V+6+(retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin N+
        (22*N+22*V+22+transferCountedLineCost N w+
          transferCountedLineCost (couplingCoefficientPageInterval P q s t u band a b origin N).length w))))) + (28*N*w+36*N+11*V+26) ∧
      Exec body (sharedLocalFeedCouplingInterval hQ boundary) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 93 rhsTail) 110
          (cstream A w (packedInterval origin N (guardedCouplingRowField P q t u band a b boundary C B))++S.R 110))}) := by
  let T := embStk sharedCouplingReg S
  have hgeometryT : CouplingIntervalMetadata V s t band a b origin N T := by
    constructor
    · simpa [T,embStk,sharedCouplingReg,Equiv.swap_apply_def] using hgeometry.width
    · intro k hk
      have hhigh : 143 ≤ k.val := by
        simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      change S.R (sharedCouplingReg k) = _
      rw [sharedCouplingReg_high k hhigh]
      exact hgeometry.encoded k hk
  have hreadyT : RetainedCouplingReady P q w s t u band a b raw
      (embStk groupReg (embStk intervalPageReg T)) := by
    change RetainedCouplingReady P q w s t u band a b raw
      (embStk groupReg (embStk intervalPageReg (embStk sharedCouplingReg S)))
    rw [sharedCouplingCore_view sharedCouplingReg S]
    exact hready
  obtain ⟨vi,m,hui,hm,hei⟩ := localFeedCouplingInterval_exec (P := P) (q := q) (w := w) (s := s) (t := t)
    (u := u) (band := band) (a := a) (b := b) (origin := origin) (N := N) (body := fun p : Empty => nomatch p)
    hQ boundary hA hw5 hqw hst C B hfit tail pageTail rhsTail raw (embDn sharedCouplingReg v) T
    hreadyT hlocalOrigin hlocalEnd hsep
    (by simpa [T,embStk,sharedCouplingReg,Equiv.swap_apply_def] using hsource)
    (by simpa [T,embStk,sharedCouplingReg,Equiv.swap_apply_def] using h127)
    (by simpa [T,embStk,sharedCouplingReg,Equiv.swap_apply_def] using hrows)
    (by simpa [T,embStk,sharedCouplingReg,Equiv.swap_apply_def] using hpage)
    (by simpa [T,embStk,sharedCouplingReg,Equiv.swap_apply_def] using hrhs)
    (by simpa [T,embStk,sharedCouplingReg,Equiv.swap_apply_def] using h143) hCfits has V
    (by simpa [T,embStk,sharedCouplingReg,Equiv.swap_apply_def] using h166)
    (by simpa [T,embStk,sharedCouplingReg,Equiv.swap_apply_def] using h139)
    haS hbS hbandS hwide hfitV hgeometryT
    (by simpa [T,embStk,sharedCouplingReg,Equiv.swap_apply_def] using h158)
    (by simpa [T,embStk,sharedCouplingReg,Equiv.swap_apply_def] using h135)
    (by simpa [T,embStk,sharedCouplingReg,Equiv.swap_apply_def] using h167)
  obtain ⟨v',hv,hu,he⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    sharedCouplingReg_injective (fun p => nomatch p) hei v rfl S rfl
  refine ⟨v',m,hu.trans hui,hm,he.cast rfl ?_⟩
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
