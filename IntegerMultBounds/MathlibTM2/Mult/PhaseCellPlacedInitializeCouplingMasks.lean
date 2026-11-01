module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeRecoveryMasksStock
public import IntegerMultBounds.MathlibTM2.Host.EmbedStockTrace

/-! Shared mask generation in an arbitrary bank. Its exact endpoint makes all
spectator, metadata and native-bank frames independent of the caller layout. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def couplingMasksState (e : Fin 168 → Fin T) (boundary : Bool)
    (s : ℕ) [NeZero s] (t band a b origin N : ℕ) (S : Stacks T A) : Stacks T A :=
  {S with R := (Function.update (Function.update S.R (e 159)
    ((couplingRibbonFlags (s := s) boundary t band a b origin N).map (fun flag => pairSym A flag flag)))
    (e 161) (recoveryGuardIntervalSymbols true A s t (2*band) a b origin N))}

def placedInitializeCouplingMasks (e : Fin 168 → Fin T) (boundary : Bool) : Pr P T Q A U :=
  embProg e Empty.elim (initializeCouplingMasks boundary)

theorem couplingMasksState_frame (e : Fin 168 → Fin T) (boundary : Bool)
    (s : ℕ) [NeZero s] (t band a b origin N : ℕ) (S : Stacks T A) (k : Fin T)
    (h159 : k ≠ e 159) (h161 : k ≠ e 161) :
    (couplingMasksState e boundary s t band a b origin N S).R k = S.R k := by
  simp [couplingMasksState,h159,h161]

theorem placedInitializeCouplingMasks_exec_within (e : Fin 168 → Fin T)
    (he : Function.Injective e) (boundary : Bool) {s t band a b origin N V : ℕ} [NeZero s]
    (hst : s < t) (ha : a ≤ s) (hb : b ≤ s) (hband : band ≤ s) (hfit : origin+N ≤ s)
    (hwide : 8*(t+1)^2+4*band+8 < 2^V) (hfitV : origin+(N+2*band)+s < 2^V)
    (v : HS T Q A U) (S : Stacks T A)
    (hgeometry : CouplingIntervalMetadata V s t band a b origin N (embStk e S))
    (hclean : ∀ k : Fin 168, k.val < 63 → S.R (e k) = [])
    (h136 : S.R (e 136) = []) (h158 : S.R (e 158) = [])
    (h159 : S.R (e 159) = []) (h161 : S.R (e 161) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ initializeRecoveryMasksCost V N band ∧
      ∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          mnProgPush (initializeCouplingMasks boundary (P := Empty) (Q := Q) (A := A) (U := U))*
            initializeRecoveryMasksCost V N band)
        depth (placedInitializeCouplingMasks e boundary) (mk v S) n
          (mk v' (couplingMasksState e boundary s t band a b origin N S)) := by
  obtain ⟨vi,n,hu,hn,hex⟩ := initializeCouplingMasks_exec_within (body := fun z : Empty => nomatch z)
    boundary hst ha hb hband hfit hwide hfitV (embDn e v) (embStk e S)
    hgeometry hclean h136 h158 h159 h161
  obtain ⟨v',hv,hu',hex'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    he (fun z => nomatch z) (hex 0).toExec v rfl S rfl
  have ht : embOvr e
      ({embStk e S with R := (Function.update (Function.update (embStk e S).R 159
        ((couplingRibbonFlags (s := s) boundary t band a b origin N).map (fun flag => pairSym A flag flag)))
        161 (recoveryGuardIntervalSymbols true A s t (2*band) a b origin N))} : Stacks 168 A).get S =
      couplingMasksState e boundary s t band a b origin N S := by
    rw [embOvr_updateR_updateR he]
    rfl
  refine ⟨v',n,hu'.trans hu,hn,?_⟩
  intro depth
  have hb := exec_emb_within_stock_of_exec (ι := Empty.elim) (body' := body)
    he (fun z => nomatch z) (hex depth) v rfl S rfl hex'
  exact hb.cast rfl (congrArg (mk v') ht)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
