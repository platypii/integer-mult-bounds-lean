module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalFeedCouplingInterval
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Execute local packed coupling in released numerical storage, retaining the
shared coefficient page and every spectator tape. Only RHS and result change. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

noncomputable def replicaLocalCoupling {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (hQ : SS.states ≤ Q) (boundary : Bool) : Pr P T Q A U :=
  embProg placement.bank Empty.elim (localFeedCouplingInterval (P₀ := Empty) hQ boundary)

def replicaLocalCouplingCost (boundary : Bool) (P q w s t u band a b origin N V : ℕ) :=
  (((16*N*w+21*N+14*band*w+13*band+11*V+46)+(152*V+153+((32*(N+2*band)+2)*tblC V 1+68*V+2*(N+2*band)+72)+maskCouplingSourceCost (N+2*band) w)+(12*((N+2*band)*w)+11*(N+2*band)+14)) +
        (12*((N+2*band)*w)+17*N+26*band+11*V+24) +
        (144*V+145+((46*N+2)*tblC V 1+66*V+2*N+70)+(6*N+11*V+6+(retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin N+
        (22*N+22*V+22+transferCountedLineCost N w+
          transferCountedLineCost (couplingCoefficientPageInterval P q s t u band a b origin N).length w))))) + (28*N*w+36*N+11*V+26)

theorem replicaLocalCoupling_exec {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (hQ : SS.states ≤ Q) {precision q w s t u band a b origin N : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t)
    (C B : ZMod s → GaussianInt)
    (hfit : origin+N ≤ s)
    (tail pageTail rhsTail raw : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hready : RetainedCouplingReady precision q w s t u band a b raw (embStk weightCacheCoreReg (embStk plan.solver S)))
    (hlocalOrigin : origin = a) (hlocalEnd : b = a+N) (hsep : N+band ≤ s)
    (hsource : S.R (placement.bank 132) = cstream A w (packedInterval a N C)++tail) (h127 : S.R (placement.bank 127) = [])
    (hrows : (S.R (placement.bank 140)).length = 2*band+1)
    (hpage : S.R (placement.bank 138) = cstream A w (couplingCoefficientPageInterval precision q s t u band a b origin N)++pageTail)
    (hrhs : S.R (placement.bank 93) = cstream A w (packedInterval origin N B)++rhsTail)
    (h143 : S.R (placement.bank 143) = [])
    (hCfits : ∀ j, Fits w (C j))
    (has : ∀ j < N, ∀ z ∈ couplingCoefficientWords precision q s t u band (origin+j), Fits w z ∧ z.im = 0)
    (V : ℕ) (h166 : S.R (placement.bank 166) = [])
    (h139 : (S.R (placement.bank 139)).length = (couplingCoefficientPageInterval precision q s t u band a b origin N).length)
    (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (hwide : 8*(t+1)^2+4*band+8 < 2^V)
    (hfitV : origin+(N+2*band)+s < 2^V)
    (hgeometry : CouplingIntervalMetadata V s t band a b origin N (embStk placement.bank S))
    (h158 : S.R (placement.bank 158) = []) (h135 : S.R (placement.bank 135) = []) (h167 : S.R (placement.bank 167) = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ replicaLocalCouplingCost boundary precision q w s t u band a b origin N V ∧
      Exec body (replicaLocalCoupling placement hQ boundary) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R (placement.bank 93) rhsTail) (placement.bank 110)
          (cstream A w (packedInterval origin N (guardedCouplingRowField precision q t u band a b boundary C B))++S.R (placement.bank 110)))}) := by
  let J :=  embStk placement.bank S
  have hreadyB : RetainedCouplingReady precision q w s t u band a b raw
      (embStk groupReg (embStk intervalPageReg J)) := by
    exact (placement.native_view S).symm ▸ hready
  obtain ⟨vi,m,hu,hm,he⟩ := localFeedCouplingInterval_exec (body := fun p : Empty => nomatch p)
    hQ boundary hA hw5 hqw hst C B hfit tail pageTail rhsTail raw (embDn placement.bank v) J
    hreadyB hlocalOrigin hlocalEnd hsep hsource h127 hrows hpage hrhs h143 hCfits has V h166 h139
    haS hbS hbandS hwide hfitV hgeometry h158 h135 h167
  obtain ⟨v',_,hu',he'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    placement.bank_injective (fun p : Empty => nomatch p) he v rfl S rfl
  refine ⟨v',m,hu'.trans hu,hm,he'.cast rfl ?_⟩
  apply congrArg (mk v')
  rw [embOvr_updateR_updateR placement.bank_injective]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
