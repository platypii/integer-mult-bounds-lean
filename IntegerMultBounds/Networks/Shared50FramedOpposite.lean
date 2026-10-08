import IntegerMultBounds.Networks.Shared50OppositeBlockFrames
import IntegerMultBounds.Networks.Shared50OppositeRank
import IntegerMultBounds.Networks.FramedBlocks
import IntegerMultBounds.Networks.Shared50PhysicalEdges

/-! Physical opposite invocation: exchanged sparse scalar blocks with the
literal finite complementary inverse DAG in the middle. Exact frame history,
scalar erasure, and arbitrary-module execution are proved together. -/

namespace IntegerMultBounds.Networks.Shared50FramedOpposite

open scoped TensorProduct
open Circuit FramedCircuit MotifLabels Shared50StageFrames Shared50LabeledInvocation
open Shared50OppositeLabels Shared50BlockFrames Shared50OppositeBlockFrames NeighborCounts
open Shared50FramedInvocation (align align_run scalar scalar_run erase_align erase_scalar erase_append)

variable {n s : ℕ} {E H M : Type*} [AddCommGroup E] [Module ℚ E]
  [AddCommGroup H] [Module ℚ H] [AddCommGroup M] [Module (ZMod 2) M]

attribute [local irreducible] Shared50Finite.program SharedPointReplay.circuit SharedPointExecution.code

/-- The actual complementary inverse instruction list, placed at side roles. -/
noncomputable def middle (g : Geometry ℚ E Factor) (q : H)
    (frameOf : Space E H → Frame (ZMod 2) M) : List (Instruction (Wire n s) (ZMod 2) M) :=
  FramedEmbedding.embed (Shared50Invocation.sideEmbedding n 509194 50 s)
    (Shared50FiniteFramed.inverse (fun U => frameOf (label g q U)))

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

theorem middle_identity (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (frameOf : Space E H → Frame (ZMod 2) M) (stored : Wire n s → M) :
    FramedCircuit.run (middle g q frameOf) stored =
      encode (fun i => frameOf (reverseComputed g q e i))
        (moduleRun (Shared50SparseInvocation.backward n s)
          (decode (fun i => frameOf (reverseLoaded g q e i)) stored)) :=
  side_identity frameOf (xMid g q e) (fun _ => low g q)
    (fun i => label g q (Shared50ComplementFrames.input i.val))
    (fun i => label g q (Shared50ComplementFrames.output i.val)) (fun _ => low g q) (fun _ => ⊥)
    (Shared50FiniteFramed.inverse (fun U => frameOf (label g q U))) Shared50Finite.program.reverse
    (Shared50FiniteFramed.inverse_identity (fun U => frameOf (label g q U))) stored

theorem middle_run (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (frameOf : Space E H → Frame (ZMod 2) M) (state : Wire n s → M) :
    FramedCircuit.run (middle g q frameOf) (encode (fun i => frameOf (reverseLoaded g q e i)) state) =
      encode (fun i => frameOf (reverseComputed g q e i))
        (moduleRun (Shared50SparseInvocation.backward n s) state) := by
  rw [middle_identity g q e,decode_encode]

theorem erase_middle (g : Geometry ℚ E Factor) (q : H)
    (frameOf : Space E H → Frame (ZMod 2) M) :
    BoundedFramedCircuit.erase (middle (n := n) (s := s) g q frameOf) = Shared50SparseInvocation.backward n s := by
  rw [middle,FramedEmbedding.erase_embed,Shared50FiniteFramed.inverse_erasure]
  rfl

/-- Exact chronological twelve scalar blocks after exchanging X and Y. -/
noncomputable def program (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (frameOf : Space E H → Frame (ZMod 2) M) (initial : Wire n s → Space E H) :
    List (Instruction (Wire n s) (ZMod 2) M) :=
  align frameOf initial (early g q e) ++
  scalar (load e) ++ scalar (gather e) ++ scalar (Shared50SparseInvocation.forward n s) ++
  align frameOf (early g q e) (injected g q e) ++ scalar (read e) ++
  align frameOf (injected g q e) (reverseLoaded g q e) ++ middle g q frameOf ++
  align frameOf (reverseComputed g q e) (reverseGathered g q) ++ scalar (scatter e) ++
  align frameOf (reverseGathered g q) (reverseReturned g q) ++ scalar (gather e) ++
  align frameOf (reverseReturned g q) (drained g q e) ++ scalar (load e) ++
  align frameOf (drained g q e) (output g q e) ++ scalar (scatter e) ++
  scalar (Shared50SparseInvocation.forward n s) ++ scalar (read e) ++
  scalar (Shared50SparseInvocation.backward n s)

/-- Expand the existing actual opposite program without changing scalar order. -/
theorem opposite_blocks (e : Fin n ≃ Triple 50) :
    Shared50SparseInvocation.opposite (s := s) e =
      load e ++ gather e ++ Shared50SparseInvocation.forward n s ++ read e ++
      Shared50SparseInvocation.backward n s ++ scatter e ++ gather e ++ load e ++
      scatter e ++ Shared50SparseInvocation.forward n s ++ read e ++ Shared50SparseInvocation.backward n s := by
  have happ (p r : Program (Wire n s) (ZMod 2)) :
      rename (exchangeRoles n 509194 50 s) (p ++ r) =
        rename (exchangeRoles n 509194 50 s) p ++ rename (exchangeRoles n 509194 50 s) r :=
    List.map_append
  simp only [Shared50SparseInvocation.opposite,Shared50SparseInvocation.inverse,happ,
    Shared50OppositeBlockFrames.load,Shared50OppositeBlockFrames.gather,
    Shared50OppositeBlockFrames.read,Shared50OppositeBlockFrames.scatter,
    Shared50SparseInvocation.forward,Shared50SparseInvocation.backward,rename_side,List.append_assoc]

private theorem erase_blocks {ι L : Type*} [Fintype ι] [DecidableEq ι]
    (frameOf : L → Frame (ZMod 2) M) (p0 p1 p2 p3 p4 p5 p6 p7 p8 : ι → L)
    (l j li r v gc : Program ι (ZMod 2)) (mid : List (Instruction ι (ZMod 2) M))
    (hm : BoundedFramedCircuit.erase mid = li) :
    BoundedFramedCircuit.erase
      (align frameOf p0 p1 ++ scalar v ++ scalar gc ++ scalar l ++
       align frameOf p1 p2 ++ scalar j ++ align frameOf p2 p3 ++ mid ++
       align frameOf p4 p5 ++ scalar r ++ align frameOf p5 p6 ++ scalar gc ++
       align frameOf p6 p7 ++ scalar v ++ align frameOf p7 p8 ++ scalar r ++
       scalar l ++ scalar j ++ scalar li) =
      v ++ gc ++ l ++ j ++ li ++ r ++ gc ++ v ++ r ++ l ++ j ++ li := by
  simp only [erase_append,erase_align,erase_scalar,hm,List.nil_append,List.append_nil]

theorem scalar_erasure (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (frameOf : Space E H → Frame (ZMod 2) M) (initial : Wire n s → Space E H) :
    BoundedFramedCircuit.erase (program g q e frameOf initial) = Shared50SparseInvocation.opposite e :=
  (erase_blocks frameOf initial (early g q e) (injected g q e) (reverseLoaded g q e)
    (reverseComputed g q e) (reverseGathered g q) (reverseReturned g q) (drained g q e) (output g q e)
    (Shared50SparseInvocation.forward n s) (read e) (Shared50SparseInvocation.backward n s)
    (scatter e) (load e) (gather e) (middle g q frameOf) (erase_middle g q frameOf)).trans
    (opposite_blocks e).symm

theorem program_invariant (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (q : H) (e : Fin n ≃ Triple 50) (frameOf : Space E H → Frame (ZMod 2) M)
    (initial : Wire n s → Space E H) (state : Wire n s → M) :
    FramedCircuit.run (program g q e frameOf initial) (encode (fun i => frameOf (initial i)) state) =
      encode (fun i => frameOf (output g q e i)) (moduleRun (Shared50SparseInvocation.opposite e) state) := by
  have hf : Uniform (early (s := s) g q e) (Shared50SparseInvocation.forward n s) :=
    early_side g q e Shared50Finite.program
  have ho : Uniform (output (s := s) g q e) (Shared50SparseInvocation.forward n s) :=
    output_side g q e Shared50Finite.program
  have hb : Uniform (output (s := s) g q e) (Shared50SparseInvocation.backward n s) :=
    output_side g q e Shared50Finite.program.reverse
  simp only [program,FramedCircuit.run_append,align_run,
    scalar_run frameOf _ _ (early_load g q e),scalar_run frameOf _ _ (early_gather g q e),
    scalar_run frameOf _ _ hf,scalar_run frameOf _ _ (injected_read g q e),middle_run g q e,
    scalar_run frameOf _ _ (gathered_scatter g q e),scalar_run frameOf _ _ (returned_gather g q e),
    scalar_run frameOf _ _ (drained_load g hcurrent q e),scalar_run frameOf _ _ (output_scatter g q e),
    scalar_run frameOf _ _ ho,scalar_run frameOf _ _ (output_read g q e),scalar_run frameOf _ _ hb,
    opposite_blocks,GroupedModuleFrames.moduleRun_append]

/-- Arbitrary stored contents, with the proved input/output frame profiles. -/
theorem program_identity (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (q : H) (e : Fin n ≃ Triple 50) (frameOf : Space E H → Frame (ZMod 2) M)
    (initial : Wire n s → Space E H) (stored : Wire n s → M) :
    FramedCircuit.run (program g q e frameOf initial) stored =
      encode (fun i => frameOf (output g q e i))
        (moduleRun (Shared50SparseInvocation.opposite e) (decode (fun i => frameOf (initial i)) stored)) := by
  conv_lhs => rw [← encode_decode (fun i => frameOf (initial i)) stored]
  exact program_invariant g hcurrent q e frameOf initial _

open FramedEdgeTrace

theorem middle_pairs (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (frameOf : Space E H → Frame (ZMod 2) M) :
    pairs (middle (n := n) (s := s) g q frameOf) =
      (RankTrace.edges (reverseLoaded (s := s) g q e) (Shared50OppositeRank.middleUpdates g q)).map
        (fun p => (frameOf p.1,frameOf p.2)) := by
  rw [middle,pairs_embed,Shared50PhysicalEdges.inverse,Shared50OppositeRank.middle_edges,List.map_map]
  rfl

/-- Every physical edge is exactly the corresponding edge of the rank trace. -/
theorem program_pairs (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (frameOf : Space E H → Frame (ZMod 2) M) (initial : Wire n s → Space E H) :
    pairs (program g q e frameOf initial) =
      (RankTrace.edges initial (Shared50OppositeRank.updates g q e)).map
        (fun p => (frameOf p.1,frameOf p.2)) := by
  simp only [Shared50OppositeRank.updates,RankTrace.edges_append,RankTrace.finish_append,
    Shared50InvocationRank.align_finish,Shared50OppositeRank.middle_finish,List.map_append]
  simp only [program,pairs_append,scalar,pairs_gates,align,pairs_edges,middle_pairs g q e,
    Shared50InvocationRank.align,List.append_nil]

end IntegerMultBounds.Networks.Shared50FramedOpposite
