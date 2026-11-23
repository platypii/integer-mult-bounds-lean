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

private theorem run_common_frame {Ω : Type*} (f : FramedCircuit.Frame (ZMod 2) (Ω → ZMod 2))
    (gs : List (Circuit.Gate ℕ (ZMod 2))) (x : ℕ → Ω → ZMod 2) :
    FramedCircuit.moduleRun gs (FramedCircuit.encode (fun _ => f) x) =
      FramedCircuit.encode (fun _ => f) (FramedCircuit.moduleRun gs x) := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [FramedCircuit.moduleRun_cons,FramedCircuit.moduleRun_cons,
      FramedCircuit.gate_invariant g _ f (fun _ _ => rfl),ih]

/-- Run all D additions in frame 1 and apply one conversion to each
receiving register at the endpoint, independently of its source count. -/
theorem execute_D_common {Ω : Type*} (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) (Ω → ZMod 2))
    (stored : Fin 661 → Ω → ZMod 2) (i : Fin 661) :
    let x := Copy.extendStored stored
    let suffix := sectionA ++ sectionscatter ++ sectionB ++ sectionC
    let returned := FramedCircuit.moduleRun (suffix.map RawGate.toCircuit) x
    let common := FramedCircuit.encode (fun _ : ℕ => frameOf 1) returned
    let result := FramedCircuit.moduleRun (sectionD.map RawGate.toCircuit) common
    execute frameOf (FramedCircuit.encode (fun j => frameOf (Frames.snapshot Frames.initialRefs j)) x) i.val =
      frameOf (Frames.finalRefs i.val) ((frameOf 1).symm (result i.val)) := by
  intro x suffix returned common result
  rw [execute_D_last]
  dsimp only [result,common]
  rw [run_common_frame]
  simp only [FramedCircuit.encode,Frames.snapshot,i.isLt,ite_true,LinearEquiv.symm_apply_apply]
  rfl

/-- An already encoded target can keep its suffix value in place. Only the
additive increment accumulated in frame 1 needs the target's conversion. -/
theorem execute_D_increment {Ω : Type*} (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) (Ω → ZMod 2))
    (stored : Fin 661 → Ω → ZMod 2) (i : Fin 661) :
    let x := Copy.extendStored stored
    let returned := FramedCircuit.moduleRun ((sectionA ++ sectionscatter ++ sectionB ++ sectionC).map RawGate.toCircuit) x
    let common := FramedCircuit.encode (fun _ : ℕ => frameOf 1) returned
    let increment := FramedCircuit.moduleRun (sectionD.map RawGate.toCircuit) common i.val - common i.val
    let target := frameOf (Frames.finalRefs i.val)
    execute frameOf (FramedCircuit.encode (fun j => frameOf (Frames.snapshot Frames.initialRefs j)) x) i.val =
      target (returned i.val) + target ((frameOf 1).symm increment) := by
  intro x returned common increment target
  rw [execute_D_common]
  dsimp only [increment]
  rw [map_sub,map_sub]
  simp only [common,FramedCircuit.encode,LinearEquiv.symm_apply_apply]
  abel

private theorem helper_final_one : ∀ h : Fin 439, Frames.finalRefs (222+h.val) = 1 := by
  decide +kernel

/-- Read the helpers exactly as stored in the final frames of the suffix.
A zero target accumulates the correction before conversion to its own frame. -/
theorem execute_D_from_helpers {Ω : Type*} (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) (Ω → ZMod 2))
    (stored : Fin 661 → Ω → ZMod 2) (t : Fin 111) :
    let x := Copy.extendStored stored
    let returned := FramedCircuit.moduleRun ((sectionA ++ sectionscatter ++ sectionB ++ sectionC).map RawGate.toCircuit) x
    let encoded := FramedCircuit.encode (fun j => frameOf (Frames.finalRefs j)) returned
    let acc := fun j => if 222 ≤ j ∧ j < 661 then encoded j else 0
    let i := 111+t.val
    execute frameOf (FramedCircuit.encode (fun j => frameOf (Frames.snapshot Frames.initialRefs j)) x) i =
      encoded i + frameOf (Frames.finalRefs i) ((frameOf 1).symm
        (FramedCircuit.moduleRun (sectionD.map RawGate.toCircuit) acc i)) := by
  intro x returned encoded acc i
  rw [execute_D_increment frameOf stored (⟨i,by dsimp [i]; omega⟩ : Fin 661)]
  congr 2
  apply congrArg (frameOf 1).symm
  funext ω
  simp only [Pi.sub_apply,FramedCircuit.moduleRun_pointwise]
  apply d_accumulator
  · simp [acc,i,show ¬222 ≤ 111+t.val by omega]
  · intro j lo hi
    have ref := helper_final_one (⟨j-222,by omega⟩ : Fin 439)
    change Frames.finalRefs (222+(j-222)) = 1 at ref
    rw [show 222+(j-222) = j by omega] at ref
    simp only [acc,encoded,FramedCircuit.encode,lo,hi,and_self,ite_true,ref]
    rfl

/-- A literal D row can read each helper at its own physical address. -/
theorem execute_D_row {Ω P : Type*} (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) (Ω → ZMod 2))
    (stored : Fin 661 → Ω → ZMod 2) (g : RawGate) (hg : g ∈ sectionD)
    (address : ℕ → Ω → P) (bank : ℕ → P → ZMod 2) :
    let x := Copy.extendStored stored
    let returned := FramedCircuit.moduleRun ((sectionA ++ sectionscatter ++ sectionB ++ sectionC).map RawGate.toCircuit) x
    let encoded := FramedCircuit.encode (fun j => frameOf (Frames.finalRefs j)) returned
    (∀ j ∈ g.sources, ∀ ω, bank j (address j ω) = encoded j ω) →
    execute frameOf (FramedCircuit.encode (fun j => frameOf (Frames.snapshot Frames.initialRefs j)) x) g.target =
      encoded g.target + frameOf (Frames.finalRefs g.target) ((frameOf 1).symm
        (fun ω => (g.sources.map (fun j => bank j (address j ω))).sum)) := by
  intro x returned encoded reads
  obtain ⟨ht,hs⟩ := d_row_bounds hg
  let t : Fin 111 := ⟨g.target-111,by omega⟩
  have idx : 111+t.val = g.target := by dsimp [t]; omega
  have endpoint := execute_D_from_helpers frameOf stored t
  dsimp only at endpoint
  rw [idx] at endpoint
  rw [endpoint]
  apply congrArg (fun v => encoded g.target + frameOf (Frames.finalRefs g.target) v)
  apply congrArg (frameOf 1).symm
  funext ω
  rw [FramedCircuit.moduleRun_pointwise,d_row g hg]
  simp only [show ¬(222 ≤ g.target ∧ g.target < 661) by omega,ite_false,Pi.zero_apply,zero_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  simpa only [if_pos (hs j hj)] using (reads j hj ω).symm

end IntegerMultBounds.Networks.Certificates.PR589.Framed
