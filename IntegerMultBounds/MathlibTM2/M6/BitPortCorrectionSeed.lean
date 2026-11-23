module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinaryOwner
public import IntegerMultBounds.MathlibTM2.M6.BitPhaseRun

/-! Assemble the private correction stacks from the individual port workspaces. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)

theorem placePort_fixed {k v w : ℕ} (dst : Fin (k+1))
    (a : SharedBankStage.Stage _ 1 prime (@portOwner v))
    (b : SharedBankStage.Stage _ 1 prime (@portOwner w))
    (fixed : SharedBankSkeleton.ofStage a = SharedBankSkeleton.ofStage b) :
    SharedBankSkeleton.ofStage (placePort dst a) = SharedBankSkeleton.ofStage (placePort dst b) := by
  cases a
  cases b
  injection fixed with ht hs hp hslot
  subst_vars
  rfl

theorem compiledPort_fixed {k v w : ℕ} {α : Type*} (slot : α → Fin (k+1)) (jobs : List α)
    (a : α → SharedBankStage.Stage _ 1 prime (@portOwner v)) (b : α → SharedBankStage.Stage _ 1 prime (@portOwner w))
    (fixed : ∀ j ∈ jobs, SharedBankSkeleton.ofStage (a j) = SharedBankSkeleton.ofStage (b j)) :
    SharedBankSkeleton.ofStage (SharedBankStage.compile _ (Nat.zero_lt_succ k) (jobs.map fun j => placePort (slot j) (a j))) =
    SharedBankSkeleton.ofStage (SharedBankStage.compile _ (Nat.zero_lt_succ k) (jobs.map fun j => placePort (slot j) (b j))) := by
  simp only [SharedBankSkeleton.ofStage_compile,List.map_map]
  exact congrArg _ (List.map_congr_left fun j hj => placePort_fixed _ _ _ (fixed j hj))

/-- Placing and sequencing any number of ports requires only the private
words used by each one-port pass. Shared owner slots start blank in the seed. -/
theorem compiledPortSeed {k V : ℕ} {α : Type*} (slot : α → Fin (k+1))
    (port : α → SharedBankStage.Stage _ 1 prime (@portOwner V)) (jobs : List α)
    (seed : ∀ j ∈ jobs, HasStackSeed (port j).metadata) :
    let stage := SharedBankStage.compile _ (Nat.zero_lt_succ k) (jobs.map fun j => placePort (slot j) (port j))
    ∃ S, ChartPrivateReady stage S := by
  intro stage
  have rep : HasStackSeed stage.metadata := by
    induction jobs with
    | nil => exact HasStackSeed.empty _
    | cons j js ih =>
      have localSeed := (seed j List.mem_cons_self).append (HasStackSeed.empty k)
      exact ((HasStackSeed.empty _).append localSeed).append
        (ih (fun a ha => seed a (List.mem_cons_of_mem _ ha)))
  obtain ⟨S,read⟩ := rep
  exact ⟨S,fun i _ => read i⟩

theorem compileSeededPorts {k V : ℕ} {α : Type*} (slot : α ↪ Fin (k+1))
    (port : α → SharedBankStage.Stage _ 1 prime (@portOwner V)) (ts : List α) (unique : ts.Nodup)
    (seed : ∀ j ∈ ts, HasStackSeed (port j).metadata) :
    ∃ post : SharedBankStage.Stage _ (k+1) prime (phaseOwners (N := V)),
      (∃ S, ChartPrivateReady post S) ∧
      post.tapes = k+1 + (ts.map fun t => k+1+((port t).tapes+k)).sum ∧
      post.states = (ts.map fun t => (port t).states).sum + 1 ∧
      post.cost = (ts.map fun t => (port t).cost).sum + ts.length ∧
      (∀ data t, t ∈ ts → post.transform data (slot t) = (port t).transform (data (slot t))) ∧
      ∀ data i, (∀ t ∈ ts, slot t ≠ i) → post.transform data i = data i :=
  ⟨_,compiledPortSeed slot port ts seed,compiledPorts_spec slot port ts unique⟩

theorem compileFixedPorts {k V R : ℕ} {α : Type*} (slot : α ↪ Fin (k+1))
    (port : α → SharedBankStage.Stage _ 1 prime (@portOwner V)) (ts : List α) (unique : ts.Nodup)
    (reference : α → SharedBankStage.Stage _ 1 prime (@portOwner R))
    (fixed : ∀ j ∈ ts, SharedBankSkeleton.ofStage (port j) = SharedBankSkeleton.ofStage (reference j))
    (seed : ∀ j ∈ ts, HasStackSeed (port j).metadata) :
    ∃ post : SharedBankStage.Stage _ (k+1) prime (phaseOwners (N := V)),
      SharedBankSkeleton.ofStage post = SharedBankSkeleton.ofStage (SharedBankStage.compile _ (Nat.zero_lt_succ k) (ts.map fun j => placePort (slot j) (reference j))) ∧
      (∃ S, ChartPrivateReady post S) ∧
      post.tapes = k+1 + (ts.map fun t => k+1+((port t).tapes+k)).sum ∧
      post.states = (ts.map fun t => (port t).states).sum + 1 ∧
      post.cost = (ts.map fun t => (port t).cost).sum + ts.length ∧
      (∀ data t, t ∈ ts → post.transform data (slot t) = (port t).transform (data (slot t))) ∧
      ∀ data i, (∀ t ∈ ts, slot t ≠ i) → post.transform data i = data i :=
  ⟨_,compiledPort_fixed slot ts port reference fixed,compiledPortSeed slot port ts seed,compiledPorts_spec slot port ts unique⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
