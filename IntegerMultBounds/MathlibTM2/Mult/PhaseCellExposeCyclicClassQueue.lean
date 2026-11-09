module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeometryRealGatherData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreSupplierQueue
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicClassReady

/-! The existing physical exposure and inverse transpose produce the concrete
cyclic scan queue from ambient complex fields, preserving callback readiness. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CyclicComplexCallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q K : ℕ} {P U : Type} {body : P → Pr P T Q (prime+K) U}

theorem exposeCyclicClassQueue_exec (ports : CyclicComplexCallerLayout T) (g : CyclicSeedLayout T)
    {B p u l target s t W V N n radius coreWidth Vg a D : ℕ}
    (width binary work saved tmp : Fin T) (Fs : List (ZMod s → GaussianInt))
    (borrowed : List (Fin (prime+K+4))) (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (gather : GeometryRealGatherData (Q := Q) Vg s coreWidth radius n W a D Fs borrowed S)
    (harchive : gather.route (PackedTranspose.extra 1) = ports.archive)
    (hoff : ∀ r, ports.classProtected g width binary work saved tmp r → r ≠ ports.archive)
    (ready : ports.ClassReady g width binary work saved tmp B p u l target s t W V N n radius (n-2*radius) S) :
    let payload := (coreGatherIndices s coreWidth radius n).attach.flatMap (fun c =>
      cstream (prime+K) W (Fs.reverse.map (packedInterval (coreStart coreWidth c.val-radius) n)).flatten)
    let E : Stacks T (prime+K) := {S with R := Function.update S.R ports.archive payload}
    ∃ v' steps, v'.user = v.user ∧ steps ≤ gather.timeCost ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+0+gather.stockAllowance) 0
        gather.program (Host.mk v S) steps (Host.mk v' E) ∧
      ports.ClassReady g width binary work saved tmp B p u l target s t W V N n radius (n-2*radius) E ∧
      E.R ports.archive = payload := by
  dsimp only
  obtain ⟨v',steps,hu,ht,he⟩ := gather.exec body v 0
  rw [harchive,coreSupplierStream_attach] at he
  refine ⟨v',steps,hu,ht,he,?_,?_⟩
  · apply ClassReady.frame ports g ready
    · rfl
    · intro r hr
      exact Function.update_of_ne (hoff r hr) _ _
  · exact Function.update_self _ _ _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CyclicComplexCallerLayout
