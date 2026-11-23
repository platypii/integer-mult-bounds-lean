module

public import IntegerMultBounds.Networks.Certificates.PR589.DeferredTargets
public import IntegerMultBounds.Networks.Certificates.PR589.Framed

/-! Transport the deferred scalar correction through the final register frames. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589.Framed

/-- The full framed endpoint is the suffix on the original input plus the
initial D correction, both expressed in the receiving register's final frame. -/
theorem execute_deferD {Ω : Type*} (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) (Ω → ZMod 2))
    (stored : Fin 661 → Ω → ZMod 2) (i : Fin 661) :
    let x := Copy.extendStored stored
    let suffix := sectionA ++ sectionscatter ++ sectionB ++ sectionC
    let final := frameOf (Frames.finalRefs i.val)
    execute frameOf (FramedCircuit.encode (fun j => frameOf (Frames.snapshot Frames.initialRefs j)) x) i.val =
      final (FramedCircuit.moduleRun (suffix.map RawGate.toCircuit) x i.val) +
      final (FramedCircuit.moduleRun (sectionD.map RawGate.toCircuit) x i.val - x i.val) := by
  intro x suffix final
  rw [execute_endpoint]
  simp only [FramedCircuit.encode,Frames.snapshot,i.isLt,ite_true]
  rw [← map_add]
  apply congrArg final
  funext ω
  simp only [Pi.add_apply,Pi.sub_apply,FramedCircuit.moduleRun_pointwise]
  exact congrFun (deferD (fun j => x j ω)) i.val

/-- Decode the suffix's endpoint, run D there, and encode in the final frame.
All inputs to D come from the returned stream bank. -/
theorem execute_D_last {Ω : Type*} (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) (Ω → ZMod 2))
    (stored : Fin 661 → Ω → ZMod 2) :
    let x := Copy.extendStored stored
    let suffix := sectionA ++ sectionscatter ++ sectionB ++ sectionC
    execute frameOf (FramedCircuit.encode (fun j => frameOf (Frames.snapshot Frames.initialRefs j)) x) =
      FramedCircuit.encode (fun j => frameOf (Frames.snapshot Frames.finalRefs j))
        (FramedCircuit.moduleRun (sectionD.map RawGate.toCircuit)
          (FramedCircuit.moduleRun (suffix.map RawGate.toCircuit) x)) := by
  intro x suffix
  rw [execute_endpoint]
  apply congrArg (FramedCircuit.encode _)
  funext i ω
  simp only [FramedCircuit.moduleRun_pointwise]
  have input : (fun j => x j ω) = extendInput (fun j => stored j ω) := by
    funext j
    by_cases h : j < 661 <;> simp [x,Copy.extendStored,extendInput,h]
  rw [input]
  exact congrFun (run_D_last (fun j => stored j ω)) i

end IntegerMultBounds.Networks.Certificates.PR589.Framed
