import IntegerMultBounds.Networks.Shared50GlobalTraceStages
import IntegerMultBounds.Networks.Shared50InvocationPhysicalEdges
import IntegerMultBounds.Networks.Shared50FramedOpposite

/-! The actual finite physical instruction schedule on the reused two-bank
world. Local forward and complementary inverse programs use their proved stage
profiles, and every boundary alignment is an explicit instruction list. -/

namespace IntegerMultBounds.Networks.Shared50GlobalFramed

noncomputable section
open scoped TensorProduct
open Circuit FramedCircuit
open Shared50GlobalBudget (Triple World)
open Shared50GlobalTrace
open Shared50GlobalTracePlacement
open Shared50ReuseLabels (vector)

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

attribute [local irreducible] Shared50Finite.program SharedPointReplay.circuit SharedPointExecution.code

section PlacementIdentity
variable {ι κ L : Type*} [DecidableEq ι] [DecidableEq κ]

/-- Abstract physical placement and trace placement share the same endpoint
profile, including every spectator outside the local bank. -/
private theorem place_identity (f : ι ↪ κ) (frameOf : L → Frame (ZMod 2) M)
    (instructions : List (Instruction ι (ZMod 2) M)) (p : Program ι (ZMod 2))
    (initial final : ι → L) (xs : List (ι × L))
    (hphysical : ∀ state, FramedCircuit.run instructions state =
      encode (fun i => frameOf (final i)) (moduleRun p (decode (fun i => frameOf (initial i)) state)))
    (hfinish : RankTrace.finish initial xs = final) (current : κ → L)
    (hcurrent : current ∘ f = initial) (stored : κ → M) :
    FramedCircuit.run (FramedEmbedding.embed f instructions) stored =
      encode (fun i => frameOf (RankTrace.finish current (Shared50InvocationRank.embedUpdates f xs) i))
        (moduleRun (GlobalCircuit.embed f p) (decode (fun i => frameOf (current i)) stored)) := by
  apply FramedEmbedding.embed_identity_full
  · intro state
    have hi : (fun i => frameOf (current i)) ∘ f = fun i => frameOf (initial i) := by
      exact congrArg (fun labels => fun i => frameOf (labels i)) hcurrent
    have hf : (fun i => frameOf (RankTrace.finish current (Shared50InvocationRank.embedUpdates f xs) i)) ∘ f =
        fun i => frameOf (final i) := by
      funext i
      simp only [Function.comp_apply,Shared50InvocationRank.finish_embed_at,hcurrent,hfinish]
    rw [hi,hf]
    exact hphysical state
  · intro k hk
    rw [Shared50InvocationRank.finish_embed_outside f current xs k hk]
end PlacementIdentity

/-- Literal forward, complementary inverse, and forward physical local programs
in the three tensor coordinate systems. -/
def localProgram (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M)
    (j : Fin 3) (q : Triple × Triple) : List (Instruction (Role n 509194 50 0) (ZMod 2) M) :=
  if j = 0 then
    Shared50FramedInvocation.program firstGeometry (vector q.1 ⊗ₜ[ℚ] vector q.2) e
      (fun U => frameOf (firstMap U))
      (Shared50LabeledInvocation.commonInput firstGeometry (vector q.1 ⊗ₜ[ℚ] vector q.2) e)
  else if j = 1 then
    Shared50FramedOpposite.program (secondGeometry q) (vector q.2) e
      (fun U => frameOf (secondMap U))
      (Shared50LabeledInvocation.commonInput (secondGeometry q) (vector q.2) e)
  else
    Shared50FramedInvocation.program (thirdGeometry q) (1 : ℚ) e
      (fun U => frameOf (thirdMap U))
      (Shared50LabeledInvocation.commonInput (thirdGeometry q) (1 : ℚ) e)

theorem local_erasure (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M)
    (j : Fin 3) (q : Triple × Triple) :
    BoundedFramedCircuit.erase (localProgram e frameOf j q) = Shared50GlobalCircuit.localProgram e j := by
  fin_cases j
  · exact Shared50FramedInvocation.scalar_erasure firstGeometry (vector q.1 ⊗ₜ[ℚ] vector q.2) e _ _
  · exact Shared50FramedOpposite.scalar_erasure (secondGeometry q) (vector q.2) e _ _
  · exact Shared50FramedInvocation.scalar_erasure (thirdGeometry q) (1 : ℚ) e _ _

/-- The proved common input and output profiles in actual cube coordinates. -/
theorem local_identity (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M)
    (j : Fin 3) (q : Triple × Triple) (stored : Role n 509194 50 0 → M) :
    FramedCircuit.run (localProgram e frameOf j q) stored =
      encode (fun i => frameOf (localOutput e j q i))
        (moduleRun (Shared50GlobalCircuit.localProgram e j)
          (decode (fun i => frameOf (localInput e j q i)) stored)) := by
  fin_cases j
  · have hh := Shared50FramedInvocation.program_identity firstGeometry (vector q.1 ⊗ₜ[ℚ] vector q.2) e
      (fun U => frameOf (firstMap U))
      (Shared50LabeledInvocation.commonInput firstGeometry (vector q.1 ⊗ₜ[ℚ] vector q.2) e) stored
    have hi := congrArg (fun labels => fun i => frameOf (labels i)) (first_input_map e q)
    have ho := congrArg (fun labels => fun i => frameOf (labels i)) (first_output_map e q)
    rw [hi,ho] at hh
    exact hh
  · have hh := Shared50FramedOpposite.program_identity (secondGeometry q) rfl (vector q.2) e
      (fun U => frameOf (secondMap U))
      (Shared50LabeledInvocation.commonInput (secondGeometry q) (vector q.2) e) stored
    have hi := congrArg (fun labels => fun i => frameOf (labels i)) (second_input_map e q)
    have ho := congrArg (fun labels => fun i => frameOf (labels i)) (second_output_map e q)
    rw [hi,ho] at hh
    exact hh
  · have hh := Shared50FramedInvocation.program_identity (thirdGeometry q) (1 : ℚ) e
      (fun U => frameOf (thirdMap U))
      (Shared50LabeledInvocation.commonInput (thirdGeometry q) (1 : ℚ) e) stored
    have hi := congrArg (fun labels => fun i => frameOf (labels i)) (third_input_map e q)
    have ho := congrArg (fun labels => fun i => frameOf (labels i)) (third_output_map e q)
    rw [hi,ho] at hh
    exact hh

/-- The local physical edge pairs agree with the cube-valued local rank trace. -/
theorem local_pairs (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M)
    (j : Fin 3) (q : Triple × Triple) :
    FramedEdgeTrace.pairs (localProgram e frameOf j q) =
      (RankTrace.edges (localInput e j q) (localUpdates e j q)).map
        (fun p => (frameOf p.1,frameOf p.2)) := by
  fin_cases j
  · change FramedEdgeTrace.pairs (Shared50FramedInvocation.program _ _ _ _ _) =
      (RankTrace.edges (localInput e 0 q) (firstUpdates e q)).map _
    rw [← first_input_map,firstUpdates,edges_mapLabels,List.map_map]
    exact Shared50InvocationPhysicalEdges.program_pairs _ _ _ _ _
  · change FramedEdgeTrace.pairs (Shared50FramedOpposite.program _ _ _ _ _) =
      (RankTrace.edges (localInput e 1 q) (secondUpdates e q)).map _
    rw [← second_input_map,secondUpdates,edges_mapLabels,List.map_map]
    exact Shared50FramedOpposite.program_pairs _ _ _ _ _
  · change FramedEdgeTrace.pairs (Shared50FramedInvocation.program _ _ _ _ _) =
      (RankTrace.edges (localInput e 2 q) (thirdUpdates e q)).map _
    rw [← third_input_map,thirdUpdates,edges_mapLabels,List.map_map]
    exact Shared50InvocationPhysicalEdges.program_pairs _ _ _ _ _

/-- Each local instruction is placed at the actual reused scalar-world role. -/
def invocation (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M)
    (j : Fin 3) (q : Triple × Triple) : List (Instruction World (ZMod 2) M) :=
  FramedEmbedding.embed (Shared50GlobalCircuit.localEmbedding e j q) (localProgram e frameOf j q)

theorem invocation_erasure (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M)
    (j : Fin 3) (q : Triple × Triple) :
    BoundedFramedCircuit.erase (invocation e frameOf j q) = Shared50GlobalCircuit.invocationProgram e j q := by
  rw [invocation,FramedEmbedding.erase_embed,local_erasure]
  rfl

/-- One placed physical invocation follows its exact placed label history. -/
theorem invocation_identity (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M)
    (j : Fin 3) (q : Triple × Triple) (current : Profile)
    (hcurrent : current ∘ Shared50GlobalCircuit.localEmbedding e j q = localInput e j q)
    (stored : World → M) :
    FramedCircuit.run (invocation e frameOf j q) stored =
      encode (fun i => frameOf (RankTrace.finish current (place e j q (localUpdates e j q)) i))
        (moduleRun (Shared50GlobalCircuit.invocationProgram e j q)
          (decode (fun i => frameOf (current i)) stored)) :=
  place_identity (Shared50GlobalCircuit.localEmbedding e j q) frameOf
    (localProgram e frameOf j q) (Shared50GlobalCircuit.localProgram e j)
    (localInput e j q) (localOutput e j q) (localUpdates e j q)
    (local_identity e frameOf j q) (localUpdates_endpoints e j q) current hcurrent stored

theorem invocation_run (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M)
    (j : Fin 3) (q : Triple × Triple) (current : Profile)
    (hcurrent : current ∘ Shared50GlobalCircuit.localEmbedding e j q = localInput e j q)
    (state : World → M) :
    FramedCircuit.run (invocation e frameOf j q) (encode (fun i => frameOf (current i)) state) =
      encode (fun i => frameOf (RankTrace.finish current (place e j q (localUpdates e j q)) i))
        (moduleRun (Shared50GlobalCircuit.invocationProgram e j q) state) := by
  rw [invocation_identity e frameOf j q current hcurrent,decode_encode]

/-- The entire global stage follows the scalar schedule's literal key order. -/
def partialStage (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M)
    (j : Fin 3) (qs : List (Triple × Triple)) : List (Instruction World (ZMod 2) M) :=
  qs.flatMap (invocation e frameOf j)

def stage (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M)
    (j : Fin 3) : List (Instruction World (ZMod 2) M) :=
  partialStage e frameOf j (GlobalCircuit.keys e)

theorem partialStage_erasure (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M)
    (j : Fin 3) (qs : List (Triple × Triple)) :
    BoundedFramedCircuit.erase (partialStage e frameOf j qs) = Shared50GlobalCircuit.partialStage e j qs := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [partialStage,Shared50GlobalCircuit.partialStage,List.flatMap_cons,
      Shared50FramedInvocation.erase_append,invocation_erasure] at *
    rw [ih]

theorem stage_erasure (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M) (j : Fin 3) :
    BoundedFramedCircuit.erase (stage e frameOf j) = Shared50GlobalCircuit.stage e j :=
  partialStage_erasure e frameOf j _

private theorem ready_after (e : Fin n ≃ Triple) (j : Fin 3) (q r : Triple × Triple)
    (hqr : q ≠ r) (current : Profile)
    (hcurrent : current ∘ Shared50GlobalCircuit.localEmbedding e j r = localInput e j r) :
    RankTrace.finish current (place e j q (localUpdates e j q)) ∘
      Shared50GlobalCircuit.localEmbedding e j r = localInput e j r := by
  funext i
  rw [Function.comp_apply,place,Shared50InvocationRank.finish_embed_outside]
  · exact congrFun hcurrent i
  · intro k
    exact local_disjoint e j q r hqr k i

/-- Every unvisited coordinate line retains its input profile while the actual
physical prefix executes; dirty contents need no restriction. -/
theorem partialStage_invariant (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M)
    (j : Fin 3) (qs : List (Triple × Triple)) (hn : qs.Nodup) (current : Profile)
    (hready : ∀ q ∈ qs, current ∘ Shared50GlobalCircuit.localEmbedding e j q = localInput e j q)
    (state : World → M) :
    FramedCircuit.run (partialStage e frameOf j qs) (encode (fun i => frameOf (current i)) state) =
      encode (fun i => frameOf (RankTrace.finish current
        (qs.flatMap (fun q => place e j q (localUpdates e j q))) i))
        (moduleRun (Shared50GlobalCircuit.partialStage e j qs) state) := by
  induction qs generalizing current state with
  | nil => rfl
  | cons q qs ih =>
    obtain ⟨hq,hn⟩ := List.nodup_cons.mp hn
    have hr : ∀ r ∈ qs, RankTrace.finish current (place e j q (localUpdates e j q)) ∘
        Shared50GlobalCircuit.localEmbedding e j r = localInput e j r := by
      intro r hr
      exact ready_after e j q r (fun he => hq (he.symm ▸ hr)) current (hready r (by simp [hr]))
    simp only [partialStage,Shared50GlobalCircuit.partialStage,List.flatMap_cons,FramedCircuit.run_append,
      RankTrace.finish_append,GroupedModuleFrames.moduleRun_append]
    rw [invocation_run e frameOf j q current (hready q (by simp))]
    exact ih hn _ hr _

theorem invocation_pairs (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M)
    (j : Fin 3) (q : Triple × Triple) (current : Profile)
    (hcurrent : current ∘ Shared50GlobalCircuit.localEmbedding e j q = localInput e j q) :
    FramedEdgeTrace.pairs (invocation e frameOf j q) =
      (RankTrace.edges current (place e j q (localUpdates e j q))).map
        (fun p => (frameOf p.1,frameOf p.2)) := by
  rw [invocation,FramedEdgeTrace.pairs_embed,local_pairs,place,Shared50InvocationRank.edges_embed,hcurrent]

theorem partialStage_pairs (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M)
    (j : Fin 3) (qs : List (Triple × Triple)) (hn : qs.Nodup) (current : Profile)
    (hready : ∀ q ∈ qs, current ∘ Shared50GlobalCircuit.localEmbedding e j q = localInput e j q) :
    FramedEdgeTrace.pairs (partialStage e frameOf j qs) =
      (RankTrace.edges current (qs.flatMap (fun q => place e j q (localUpdates e j q)))).map
        (fun p => (frameOf p.1,frameOf p.2)) := by
  induction qs generalizing current with
  | nil => rfl
  | cons q qs ih =>
    obtain ⟨hq,hn⟩ := List.nodup_cons.mp hn
    have hr : ∀ r ∈ qs, RankTrace.finish current (place e j q (localUpdates e j q)) ∘
        Shared50GlobalCircuit.localEmbedding e j r = localInput e j r := by
      intro r hr
      exact ready_after e j q r (fun he => hq (he.symm ▸ hr)) current (hready r (by simp [hr]))
    simp only [partialStage,List.flatMap_cons,FramedEdgeTrace.pairs_append,RankTrace.edges_append,List.map_append]
    rw [invocation_pairs e frameOf j q current (hready q (by simp))]
    exact congrArg (List.append _) (ih hn _ hr)

/-- Every stage reaches its concrete global output profile. -/
theorem stage_run (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M)
    (j : Fin 3) (state : World → M) :
    FramedCircuit.run (stage e frameOf j) (encode (fun i => frameOf (input j i)) state) =
      encode (fun i => frameOf (output j i)) (moduleRun (Shared50GlobalCircuit.stage e j) state) := by
  have hh := partialStage_invariant e frameOf j (GlobalCircuit.keys e) (GlobalCircuit.keys_nodup e)
    (input j) (fun q _ => input_local e j q) state
  change FramedCircuit.run (stage e frameOf j) (encode (fun i => frameOf (input j i)) state) =
    encode (fun i => frameOf (RankTrace.finish (input j) (Shared50GlobalTraceStages.stageUpdates e j) i))
      (moduleRun (Shared50GlobalCircuit.stage e j) state) at hh
  rw [Shared50GlobalTraceStages.stage_finish] at hh
  exact hh

theorem stage_pairs (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M) (j : Fin 3) :
    FramedEdgeTrace.pairs (stage e frameOf j) =
      (RankTrace.edges (input j) (Shared50GlobalTraceStages.stageUpdates e j)).map
        (fun p => (frameOf p.1,frameOf p.2)) :=
  partialStage_pairs e frameOf j (GlobalCircuit.keys e) (GlobalCircuit.keys_nodup e)
    (input j) (fun q _ => input_local e j q)

/-- All four boundary attachments are explicit complete-world frame changes. -/
def boundary (frameOf : Label → Frame (ZMod 2) M) (j : Fin 4) :
    List (Instruction World (ZMod 2) M) :=
  Shared50FramedInvocation.align frameOf (boundaryBefore j) (boundaryAfter j)

theorem boundary_erasure (frameOf : Label → Frame (ZMod 2) M) (j : Fin 4) :
    BoundedFramedCircuit.erase (boundary frameOf j) = [] :=
  Shared50FramedInvocation.erase_align frameOf _ _

theorem boundary_run (frameOf : Label → Frame (ZMod 2) M) (j : Fin 4) (state : World → M) :
    FramedCircuit.run (boundary frameOf j) (encode (fun i => frameOf (boundaryBefore j i)) state) =
      encode (fun i => frameOf (boundaryAfter j i)) state :=
  Shared50FramedInvocation.align_run frameOf _ _ state

theorem boundary_pairs (frameOf : Label → Frame (ZMod 2) M) (j : Fin 4) :
    FramedEdgeTrace.pairs (boundary frameOf j) =
      (RankTrace.edges (boundaryBefore j) (boundaryUpdates j)).map
        (fun p => (frameOf p.1,frameOf p.2)) :=
  FramedEdgeTrace.pairs_edges frameOf (boundaryBefore j) (boundaryAfter j) _

/-- The complete physical reused-world program in its actual chronological order. -/
def program (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M) :
    List (Instruction World (ZMod 2) M) :=
  boundary frameOf 0 ++ stage e frameOf 0 ++ boundary frameOf 1 ++ stage e frameOf 1 ++
    boundary frameOf 2 ++ stage e frameOf 2 ++ boundary frameOf 3

/-- Erasing only frame changes gives the already proved actual scalar exchange. -/
theorem scalar_erasure (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M) :
    BoundedFramedCircuit.erase (program e frameOf) = Shared50GlobalCircuit.program e := by
  simp only [program,Shared50FramedInvocation.erase_append,boundary_erasure,stage_erasure,
    List.nil_append,List.append_nil,Shared50GlobalCircuit.program]

/-- The complete actual physical schedule preserves the frame interpretation
through all three stages and all four boundary attachments. -/
theorem program_invariant (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M)
    (state : World → M) :
    FramedCircuit.run (program e frameOf) (encode (fun i => frameOf (source i)) state) =
      encode (fun i => frameOf (sink i)) (moduleRun (Shared50GlobalCircuit.program e) state) := by
  have h0 (v : World → M) : FramedCircuit.run (boundary frameOf 0)
      (encode (fun i => frameOf (source i)) v) = encode (fun i => frameOf (input 0 i)) v :=
    boundary_run frameOf 0 v
  have h1 (v : World → M) : FramedCircuit.run (boundary frameOf 1)
      (encode (fun i => frameOf (output 0 i)) v) = encode (fun i => frameOf (input 1 i)) v :=
    boundary_run frameOf 1 v
  have h2 (v : World → M) : FramedCircuit.run (boundary frameOf 2)
      (encode (fun i => frameOf (output 1 i)) v) = encode (fun i => frameOf (input 2 i)) v :=
    boundary_run frameOf 2 v
  have h3 (v : World → M) : FramedCircuit.run (boundary frameOf 3)
      (encode (fun i => frameOf (output 2 i)) v) = encode (fun i => frameOf (sink i)) v :=
    boundary_run frameOf 3 v
  simp only [program,FramedCircuit.run_append,h0,h1,h2,h3,stage_run,
    Shared50GlobalCircuit.program,GroupedModuleFrames.moduleRun_append]

/-- End-to-end stored-state semantics, without assuming any clean scratch. -/
theorem program_identity (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M)
    (stored : World → M) :
    FramedCircuit.run (program e frameOf) stored =
      encode (fun i => frameOf (sink i))
        (moduleRun (Shared50GlobalCircuit.program e) (decode (fun i => frameOf (source i)) stored)) := by
  conv_lhs => rw [← encode_decode (fun i => frameOf (source i)) stored]
  exact program_invariant e frameOf _

/-- Exact old/new physical frame pairs of the complete reused-world program,
including every boundary edge and every scalar-empty declared pivot. -/
theorem program_pairs (e : Fin n ≃ Triple) (frameOf : Label → Frame (ZMod 2) M) :
    FramedEdgeTrace.pairs (program e frameOf) =
      (RankTrace.edges source (Shared50GlobalTraceStages.trace e)).map
        (fun p => (frameOf p.1,frameOf p.2)) := by
  have h0 : RankTrace.finish source (boundaryUpdates 0) = input 0 := boundary_finish 0
  have h1 : RankTrace.finish (output 0) (boundaryUpdates 1) = input 1 := boundary_finish 1
  have h2 : RankTrace.finish (output 1) (boundaryUpdates 2) = input 2 := boundary_finish 2
  simp only [program,FramedEdgeTrace.pairs_append,boundary_pairs,stage_pairs,
    Shared50GlobalTraceStages.trace,RankTrace.edges_append,RankTrace.finish_append,
    h0,h1,h2,Shared50GlobalTraceStages.stage_finish,List.map_append,boundaryBefore]

end
end IntegerMultBounds.Networks.Shared50GlobalFramed
