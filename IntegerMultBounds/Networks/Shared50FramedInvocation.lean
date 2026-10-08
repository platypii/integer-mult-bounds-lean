import IntegerMultBounds.Networks.FramedBlocks
import IntegerMultBounds.Networks.Shared50InvocationRank
import IntegerMultBounds.Networks.Shared50FiniteFramed
import IntegerMultBounds.Networks.FramedEmbedding

/-! Physical forward execution of the sparse twelve-block invocation, including
all boundary alignments and the actual finite framed middle computation.
The scalar erasure and arbitrary-module common-frame identity are exact. -/

namespace IntegerMultBounds.Networks.Shared50FramedInvocation

open Circuit FramedCircuit Shared50BlockFrames


open scoped TensorProduct
open MotifLabels Shared50StageFrames Shared50LabeledInvocation NeighborCounts

variable {n s : ℕ} {E H M : Type*} [AddCommGroup E] [Module ℚ E]
  [AddCommGroup H] [Module ℚ H] [AddCommGroup M] [Module (ZMod 2) M]

attribute [local irreducible] Shared50Finite.program SharedPointReplay.circuit SharedPointExecution.code

noncomputable def middle (g : Geometry ℚ E Factor) (q : H)
    (frameOf : Space E H → Frame (ZMod 2) M) : List (Instruction (Wire n s) (ZMod 2) M) :=
  FramedEmbedding.embed (Shared50Invocation.sideEmbedding n 509194 50 s)
    (Shared50FiniteFramed.forward (fun U => frameOf (label g q U)))

/-- Bank-preserving embedding stated abstractly, so checking a concrete DAG
never normalizes its large instruction list while comparing endpoint profiles. -/
private theorem side_identity {a c : ℕ} {L : Type*}
    (frameOf : L → Frame (ZMod 2) M)
    (X Y : Fin n → L) (A B : Fin a → L) (C : Fin c → L) (S : Fin s → L)
    (instructions : List (Instruction (Fin a) (ZMod 2) M))
    (p : Program (Fin a) (ZMod 2))
    (h : ∀ state, FramedCircuit.run instructions state =
      encode (fun i => frameOf (B i)) (moduleRun p (decode (fun i => frameOf (A i)) state)))
    (stored : Role n a c s → M) :
    FramedCircuit.run (FramedEmbedding.embed (Shared50Invocation.sideEmbedding n a c s) instructions) stored =
      encode (fun i => frameOf (banks X Y B C S i))
        (moduleRun (GlobalCircuit.embed (Shared50Invocation.sideEmbedding n a c s) p)
          (decode (fun i => frameOf (banks X Y A C S i)) stored)) := by
  apply FramedEmbedding.embed_identity_full _ _ _ _ _ h
  intro r hr
  rcases r with i | i | i | i | i
  · rfl
  · rfl
  · exact False.elim (hr i rfl)
  · rfl
  · rfl

theorem middle_identity (g : Geometry ℚ E Factor) (q : H)
    (frameOf : Space E H → Frame (ZMod 2) M) (stored : Wire n s → M) :
    FramedCircuit.run (middle g q frameOf) stored =
      encode (fun i => frameOf (computed g q i))
        (moduleRun (Shared50SparseInvocation.forward n s)
          (decode (fun i => frameOf (returned g q i)) stored)) :=
  side_identity frameOf (fun _ => high g q) (fun _ => low g q)
    (fun i => label g q (Shared50Frames.initialLabels i.val))
    (fun i => label g q (Shared50Frames.finalLabels i.val)) (fun _ => low g q) (fun _ => ⊥)
    (Shared50FiniteFramed.forward (fun U => frameOf (label g q U))) Shared50Finite.program
    (Shared50FiniteFramed.forward_identity (fun U => frameOf (label g q U))) stored

theorem middle_run (g : Geometry ℚ E Factor) (q : H)
    (frameOf : Space E H → Frame (ZMod 2) M) (state : Wire n s → M) :
    FramedCircuit.run (middle g q frameOf) (encode (fun i => frameOf (returned g q i)) state) =
      encode (fun i => frameOf (computed g q i))
        (moduleRun (Shared50SparseInvocation.forward n s) state) := by
  rw [middle_identity,decode_encode]

theorem erase_middle (g : Geometry ℚ E Factor) (q : H)
    (frameOf : Space E H → Frame (ZMod 2) M) :
    BoundedFramedCircuit.erase (middle (n := n) (s := s) g q frameOf) = Shared50SparseInvocation.forward n s := by
  rw [middle,FramedEmbedding.erase_embed,Shared50FiniteFramed.forward_erasure]
  rfl

noncomputable def program (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (frameOf : Space E H → Frame (ZMod 2) M) (initial : Wire n s → Space E H) :
    List (Instruction (Wire n s) (ZMod 2) M) :=
  align frameOf initial (early g q e) ++
  scalar (Shared50SparseInvocation.forward n s) ++
  scalar (Shared50SparseInvocation.read e) ++
  scalar (Shared50SparseInvocation.backward n s) ++
  scalar (Shared50SparseCentral.scatter e) ++
  align frameOf (early g q e) (loaded g q e) ++ scalar (Shared50SparseInvocation.load e) ++
  align frameOf (loaded g q e) (gathered g q) ++ scalar (Shared50SparseCentral.gather e) ++
  align frameOf (gathered g q) (returned g q) ++ scalar (Shared50SparseCentral.scatter e) ++
  middle g q frameOf ++
  align frameOf (computed g q) (readout g q e) ++ scalar (Shared50SparseInvocation.read e) ++
  align frameOf (readout g q e) (output g q e) ++
  scalar (Shared50SparseInvocation.backward n s) ++ scalar (Shared50SparseCentral.gather e) ++
  scalar (Shared50SparseInvocation.load e)

/-- Abstract block erasure avoids reassociating an evaluated concrete DAG. -/
private theorem erase_blocks {ι L : Type*} [Fintype ι] [DecidableEq ι]
    (frameOf : L → Frame (ZMod 2) M) (p0 p1 p2 p3 p4 p5 p6 p7 : ι → L)
    (l j li r v g : Program ι (ZMod 2)) (mid : List (Instruction ι (ZMod 2) M))
    (hm : BoundedFramedCircuit.erase mid = l) :
    BoundedFramedCircuit.erase
      (align frameOf p0 p1 ++ scalar l ++ scalar j ++ scalar li ++ scalar r ++
       align frameOf p1 p2 ++ scalar v ++ align frameOf p2 p3 ++ scalar g ++
       align frameOf p3 p4 ++ scalar r ++ mid ++ align frameOf p5 p6 ++ scalar j ++
       align frameOf p6 p7 ++ scalar li ++ scalar g ++ scalar v) =
      l ++ (j ++ (li ++ (r ++ (v ++ (g ++ (r ++ (l ++ (j ++ (li ++ (g ++ v)))))))))) := by
  simp only [erase_append,erase_align,erase_scalar,hm,List.nil_append,List.append_assoc]

/-- Removing only frame changes gives the actual twelve-block sparse program. -/
theorem scalar_erasure (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (frameOf : Space E H → Frame (ZMod 2) M) (initial : Wire n s → Space E H) :
    BoundedFramedCircuit.erase (program g q e frameOf initial) = Shared50SparseInvocation.program e :=
  erase_blocks frameOf initial (early g q e) (loaded g q e) (gathered g q) (returned g q)
    (computed g q) (readout g q e) (output g q e)
    (Shared50SparseInvocation.forward n s) (Shared50SparseInvocation.read e)
    (Shared50SparseInvocation.backward n s) (Shared50SparseCentral.scatter e)
    (Shared50SparseInvocation.load e) (Shared50SparseCentral.gather e) (middle g q frameOf)
    (erase_middle g q frameOf)

/-- Every scalar block and middle frame executes in the proved chronological
profile. The initial profile can be bottom scratch or reused common scratch. -/
theorem program_invariant (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (frameOf : Space E H → Frame (ZMod 2) M) (initial : Wire n s → Space E H) (state : Wire n s → M) :
    FramedCircuit.run (program g q e frameOf initial) (encode (fun i => frameOf (initial i)) state) =
      encode (fun i => frameOf (output g q e i)) (moduleRun (Shared50SparseInvocation.program e) state) := by
  have hf : Uniform (early (s := s) g q e) (Shared50SparseInvocation.forward n s) :=
    early_side g q e Shared50Finite.program
  have hb : Uniform (early (s := s) g q e) (Shared50SparseInvocation.backward n s) :=
    early_side g q e Shared50Finite.program.reverse
  have ho : Uniform (output (s := s) g q e) (Shared50SparseInvocation.backward n s) :=
    output_side g q e Shared50Finite.program.reverse
  simp only [program,FramedCircuit.run_append,align_run,
    scalar_run frameOf _ _ hf,
    scalar_run frameOf _ _ (early_read g q e),
    scalar_run frameOf _ _ hb,
    scalar_run frameOf _ _ (early_scatter g q e),
    scalar_run frameOf _ _ (loaded_load g q e),
    scalar_run frameOf _ _ (gathered_gather g q e),
    scalar_run frameOf _ _ (returned_scatter g q e),middle_run,
    scalar_run frameOf _ _ (readout_read g q e),
    scalar_run frameOf _ _ ho,
    scalar_run frameOf _ _ (output_gather g q e),scalar_run frameOf _ _ (output_load g q e),
    Shared50SparseInvocation.program,GroupedModuleFrames.moduleRun_append]

/-- Actual physical execution on arbitrary stored module states. -/
theorem program_identity (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (frameOf : Space E H → Frame (ZMod 2) M) (initial : Wire n s → Space E H) (stored : Wire n s → M) :
    FramedCircuit.run (program g q e frameOf initial) stored =
      encode (fun i => frameOf (output g q e i))
        (moduleRun (Shared50SparseInvocation.program e) (decode (fun i => frameOf (initial i)) stored)) := by
  conv_lhs => rw [← encode_decode (fun i => frameOf (initial i)) stored]
  exact program_invariant g q e frameOf initial _

end IntegerMultBounds.Networks.Shared50FramedInvocation
