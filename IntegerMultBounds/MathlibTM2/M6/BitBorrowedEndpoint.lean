module

public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedScatter
public import IntegerMultBounds.MathlibTM2.M6.OrthogonalInvocation

/-! The PR589 dirty-register endpoint separately on each borrowed label. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^w) := ⟨pow_ne_zero _ Shared50ModularControl.prime_prime.ne_zero⟩

private theorem scatter_encode (w : ℕ) (x : ℕ → AddressStream (ZMod (prime^w)))
    (high : ∀ j, 661 ≤ j → x j = 0) :
    let frame := fun j => selectedFrame w (Frames.beforeScatter j)
    borrowedScatter w (FramedCircuit.encode frame x) =
      FramedCircuit.encode frame (FramedCircuit.moduleRun (sectionscatter.map RawGate.toCircuit) x) := by
  intro frame
  funext j
  by_cases hj : j < 661
  · simp [borrowedScatter,frame,Copy.extendStored,hj,FramedCircuit.decode_encode,FramedCircuit.encode]
  · simp [borrowedScatter,frame,Copy.extendStored,hj,FramedCircuit.encode,
      Framed.moduleRun_high _ Framed.sectionScatter_target_lt _ j (by omega),high j (by omega)]

theorem BorrowedStep.endpoint {n w B K k x y} (step : BorrowedStep n w B K k x y)
    (g : Cover.LabelPadding.Label 64 w) (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) :
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n k.1 k.2,ownerTape_injective n k.1 k.2⟩
    let j := labelSpectator g z
    let initial := FramedCircuit.decode (fun i => selectedFrame w (Frames.snapshot Frames.initialRefs i))
      (phaseRead owner x j)
    phaseRead owner y j = FramedCircuit.encode (fun i => selectedFrame w (Frames.snapshot Frames.finalRefs i))
      (FramedCircuit.moduleRun (program.map RawGate.toCircuit) initial) := by
  intro owner j initial
  let frame := selectedFrame w
  let prepared := FramedCircuit.moduleRun ((sectionD++sectionA).map RawGate.toCircuit) initial
  have high i (hi : 661 ≤ i) : prepared i = 0 := by
    rw [show prepared i = initial i from Framed.moduleRun_high _ Framed.sectionDA_target_lt _ i hi]
    simp [initial,FramedCircuit.decode,phaseRead,Copy.extendStored,show ¬i < 661 by omega]
  let scattered := FramedCircuit.moduleRun (sectionscatter.map RawGate.toCircuit) prepared
  let output := FramedCircuit.moduleRun ((sectionB++sectionC).map RawGate.toCircuit) scattered
  have read := step.1 g z
  simp only [labelPhase,Frames.before_scatter,Frames.after_scatter] at read
  rw [scatter_encode w prepared high] at read
  simp only [Frames.scatterFinish,FramedCircuit.decode_encode] at read
  have aligned := Frames.final_alignment_compiled frame output
  have fixed := final_alignment_identity w frame (FramedCircuit.encode (fun i => frame (Frames.snapshot Frames.after234 i)) output)
  rw [runPhase_eq _ frame (modular_scatter w).choose_spec.1 _ _ (Frames.final_alignment_pairs _) Geometry.Moves.final_checked.1] at fixed
  exact read.trans ((fixed.symm.trans aligned).trans (by simp only [output,scattered,prepared,program,List.map_append,Framed.moduleRun_append]; rfl))

/-- At a fixed label, each of the 111 targets adds its corresponding
source. Every source and helper retains its decoded dirty input. -/
theorem BorrowedStep.dirtyRead {n w B K k x y} (step : BorrowedStep n w B K k x y)
    (g : Cover.LabelPadding.Label 64 w) (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) (i : Fin 661) :
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n k.1 k.2,ownerTape_injective n k.1 k.2⟩
    let j := labelSpectator g z
    let input := fun a : Fin 661 => (selectedFrame w (Frames.initialRefs a.val)).symm (phaseRead owner x j a.val)
    phaseRead owner y j i.val = selectedFrame w (Frames.finalRefs i.val)
      (if h : 111 ≤ i.val ∧ i.val < 222 then input i + input ⟨i.val-111,by omega⟩ else input i) := by
  intro owner j input
  let initial := FramedCircuit.decode (fun a => selectedFrame w (Frames.snapshot Frames.initialRefs a))
    (phaseRead owner x j)
  rw [step.endpoint g z]
  change selectedFrame w (Frames.snapshot Frames.finalRefs i.val)
    (FramedCircuit.moduleRun (program.map RawGate.toCircuit) initial i.val) = _
  rw [Frames.snapshot,ite_eq_left i.isLt]
  apply congrArg
  funext s
  rw [FramedCircuit.moduleRun_pointwise]
  have bank : (fun a => initial a s) = extendInput (fun a => input a s) := by
    funext a
    by_cases ha : a < 661 <;> simp [initial,input,FramedCircuit.decode,Frames.snapshot,
      phaseRead,Copy.extendStored,extendInput,ha]
  rw [bank,dirty_endpoint]
  split <;> rfl

def BorrowedPorts (n : Fin 9) (w B K : ℕ)
    (x y : Fin 142081 → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2) : Prop :=
  ∀ (run : Fin 32 × Fin 5) (t : Fin 111) (g : Cover.LabelPadding.Label 64 w)
    (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B),
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n run.1 run.2,ownerTape_injective n run.1 run.2⟩
    let j := labelSpectator g z
    let src : Fin 661 := ⟨t.val,by omega⟩
    let dst : Fin 661 := ⟨111+t.val,by omega⟩
    let read := fun a (i : Fin 661) => phaseRead owner a j i.val
    let input := fun i : Fin 661 => (selectedFrame w (Frames.initialRefs i.val)).symm (read x i)
    read y src = selectedFrame w (Frames.finalRefs src.val) (input src) ∧
    read y dst = selectedFrame w (Frames.finalRefs dst.val) (input dst + input src)

/-- All 160 invocations together add each source exactly once to its own
target at the same borrowed label, in the selected port frames. -/
theorem borrowedSweep_ports {n w B K x y}
    (trace : stageRuns.foldr (fun k cont a => ∃ b, BorrowedStep n w B K k a b ∧ cont b)
      (fun a => a = y) x) : BorrowedPorts n w B K x y := by
  intro run t g z
  intro owner j src dst read input
  let view := fun a => (read a src,read a dst)
  let action := fun (a b : AddressStream (ZMod (prime^w)) × AddressStream (ZMod (prime^w))) =>
    let source := (selectedFrame w (Frames.initialRefs src.val)).symm a.1
    b.1 = selectedFrame w (Frames.finalRefs src.val) source ∧
    b.2 = selectedFrame w (Frames.finalRefs dst.val) ((selectedFrame w (Frames.initialRefs dst.val)).symm a.2 + source)
  apply (uniqueTraceRead run view action (BorrowedStep n w B K) ?_ ?_ stageRuns stageRuns_nodup x y trace).1 (mem_stageRuns run)
  · intro a b st
    have source := st.dirtyRead g z src
    have target := st.dirtyRead g z dst
    simpa only [src,dst,action,view,read,Fin.val_mk,Nat.add_sub_cancel_left,
      show ¬(111 ≤ t.val ∧ t.val < 222) by omega,
      show 111 ≤ 111+t.val ∧ 111+t.val < 222 by omega,and_self,↓reduceDIte] using And.intro source target
  · intro k other a b st
    have kept (i : Fin 661) (hi : i.val < 222) : read b i = read a i := by
      have eqn := st.2 (owner i) (Fin.castSucc_ne_last _) (fun h => otherRunMissesPort n k run other h i hi)
      funext s
      simpa only [read,phaseRead,Copy.extendStored,dite_eq_left i.isLt] using congrFun eqn (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j)
    exact Prod.ext (kept src (by dsimp [src]; omega)) (kept dst (by dsimp [dst]; omega))

theorem BorrowedStep.helperRead {n w B K k x y} (step : BorrowedStep n w B K k x y)
    (g : Cover.LabelPadding.Label 64 w) (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B)
    (h : Fin 439) (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))) :
    let i : Fin 661 := ⟨222+h.val,by omega⟩
    let tape := ownerTape n k.1 k.2 i
    let pos := fun a => FlatCoordinateLayout.index (AffineFieldCoordinates.embed a) (labelSpectator g z)
    y tape (pos s.swap) = x tape (pos s) := by
  intro i tape pos
  have read := step.dirtyRead g z i
  have outside : ¬(111 ≤ i.val ∧ i.val < 222) := by dsimp [i]; omega
  have frames : Frames.initialRefs i.val = 0 ∧ Frames.finalRefs i.val = 1 := BitHosting.helper_frames h.val h.isLt
  simp only [dite_eq_right outside,frames.1,frames.2,emptyFrame_decode] at read
  have cell := congrFun read s.swap
  rw [fullFrame_read,Prod.swap_swap] at cell
  simp only [phaseRead,Copy.extendStored,dite_eq_left i.isLt] at cell
  convert cell using 1

/-- At every borrowed label an inactive role swaps its two active fields
once per helper use. Its spectator coordinates stay fixed throughout. -/
def BorrowedHelpers (n : Fin 9) (w B K : ℕ)
    (x y : Fin 142081 → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2) : Prop :=
  ∀ (ρ : Role), ρ.bank.val / 2 ≠ BitHosting.activePair n.val →
    ∀ (g : Cover.LabelPadding.Label 64 w) (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B)
      (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))),
    let tape := ((Fin.cast card_role) (Fintype.equivFin Role ρ)).castSucc
    let uses := stageRuns.filter fun k => decide (∃ h : Fin 439, hostRole n k.1 k.2 h = ρ)
    let pos := fun a => FlatCoordinateLayout.index (AffineFieldCoordinates.embed a) (labelSpectator g z)
    y tape (pos (if uses.length % 2 = 1 then s.swap else s)) = x tape (pos s)

theorem borrowedSweep_helpers {n w B K x y}
    (trace : stageRuns.foldr (fun k cont a => ∃ b, BorrowedStep n w B K k a b ∧ cont b)
      (fun a => a = y) x) : BorrowedHelpers n w B K x y := by
  intro ρ inactive g z s tape uses pos
  let swap := fun (a : Swap.Shear.State (Fin 8) (ZMod (prime^w))) (k : Fin 32 × Fin 5) =>
    if decide (∃ h : Fin 439, hostRole n k.1 k.2 h = ρ) then a.swap else a
  have follow (ks : List (Fin 32 × Fin 5)) (a)
      (steps : ks.foldr (fun k cont a => ∃ b, BorrowedStep n w B K k a b ∧ cont b) (fun a => a = y) a)
      (state) : y tape (pos (ks.foldl swap state)) = a tape (pos state) := by
    induction ks generalizing a state with
    | nil => cases steps; rfl
    | cons k ks ih =>
      obtain ⟨b,step,rest⟩ := steps
      rw [List.foldl_cons,ih b rest]
      simpa only [swap,decide_eq_true_eq] using inactiveRunRead n w (fun u (_ : Fin 1) => pos u) a b k
        (fun h u _ => step.helperRead g z h u) step.2 ρ inactive state 0
  have parity := helperSwap_parity n ρ stageRuns s
  exact (congrArg (fun a => y tape (pos a)) parity.symm).trans (follow stageRuns x trace s)

end IntegerMultBounds.MathlibTM2.M6.BitNode
