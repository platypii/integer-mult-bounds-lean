module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCoreOrigins
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreSupplierQueue
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicClassReady

/-! The existing restoring geometry pass produces the fitting scan's origin
queue and loop count, preserving ordinary numerical-callback readiness. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CyclicComplexCallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem prepareCyclicClassOrigins_exec (ports : CyclicComplexCallerLayout T) (g : CyclicSeedLayout T)
    (e : Fin 117 → Fin T) (he : Function.Injective e)
    (width binary work saved tmp : Fin T)
    (hoff : ∀ r, ports.classProtected g width binary work saved tmp r → r ≠ e 109 ∧ r ≠ e 116)
    {B p u l target s t W V N n radius coreWidth : ℕ}
    (hwidth : 0 < coreWidth) (hwide : s+coreWidth+2*radius < 2^V)
    (hnfit : n < 2^V) (hA : 4 ≤ A) (hV : 0 < V)
    (v : HS T Q A U) (S : Stacks T A)
    (ready : ports.ClassReady g width binary work saved tmp B p u l target s t W V N n radius (n-2*radius) S)
    (h37 : (S.R (e 37)).length = V)
    (hs : S.R (e 32) = binSyms V s) (hw : S.R (e 33) = binSyms V coreWidth)
    (hr : S.R (e 34) = binSyms V radius) (hn : S.R (e 35) = binSyms V n) (hz : S.R (e 36) = [])
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R (e k) = [])
    (h104 : S.R (e 104) = []) (h106 : S.R (e 106) = []) (h116 : S.R (e 116) = []) :
    let jobs := coreGatherIndices s coreWidth radius n
    let E : Stacks T A := {S with R := (Function.update (Function.update S.R (e 109)
      (jobs.attach.flatMap (fun c => binSyms V (coreStart coreWidth c.val-radius))++S.R (e 109)))
      (e 116) (List.replicate jobs.length tick))}
    ∃ v' steps, v'.user = v.user ∧ steps ≤ preparedCoreOriginsCost V s coreWidth radius n ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+0+
        3*preparedCoreOriginsCost V s coreWidth radius n) 0
        (placedCoreOrigins e) (Host.mk v S) steps (Host.mk v' E) ∧
      ports.ClassReady g width binary work saved tmp B p u l target s t W V N n radius (n-2*radius) E ∧
      (E.R (e 116)).length = jobs.attach.length := by
  dsimp only
  obtain ⟨v',steps,hu,ht,heRun⟩ := placedCoreOrigins_exec_within (body := body) e he hwidth hwide hnfit hA hV
    v S h37 hs hw hr hn hz hblank h104 h106 h116 0
  rw [coreOriginQueue_attach] at heRun
  refine ⟨v',steps,hu,ht,heRun,?_,?_⟩
  · apply ClassReady.frame ports g ready
    · rfl
    · intro r hprotected
      obtain ⟨ho,hc⟩ := hoff r hprotected
      simp only [Function.update_of_ne hc,Function.update_of_ne ho]
  · simp only [Function.update_self,List.length_replicate,List.length_attach]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CyclicComplexCallerLayout
