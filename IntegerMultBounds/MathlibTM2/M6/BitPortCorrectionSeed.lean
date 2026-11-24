module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinaryOwner
public import IntegerMultBounds.MathlibTM2.M6.BitPhaseRun
public import IntegerMultBounds.MathlibTM2.M6.BitStagePlacement

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

def blankPortStacks (t : ℕ) : Stacks t prime := ⟨[],[],fun _ => [],fun _ => []⟩

private theorem blankPortStacks_rep (t : ℕ) : RepT (SharedBank.empty t prime)
    (blankPortStacks t).L (blankPortStacks t).R := by
  intro i z
  simp [blankPortStacks,SharedBank.empty,readAt_nil_left,wordTape_nil]

private theorem adjacentPortStacks_rep {n m : ℕ} {a : Tapes n prime} {b : Tapes m prime}
    {L : Stacks n prime} {R : Stacks m prime} (left : RepT a L.L L.R) (right : RepT b R.L R.R) :
    RepT (a.append b) (adjacentStageStacks L R).L (adjacentStageStacks L R).R := by
  intro i z
  induction i using Fin.addCases with
  | left i => simpa only [adjacentStageStacks,Tapes.append,Fin.addCases_left] using left i z
  | right i => simpa only [adjacentStageStacks,Tapes.append,Fin.addCases_right] using right i z

/-- Stack layout of the compiled chart, with the individual port seeds in
execution order and blank stacks in every extra slot. -/
noncomputable def compiledPortStacks {k V : ℕ} {α : Type*} (slot : α → Fin (k+1))
    (port : α → SharedBankStage.Stage _ 1 prime (@portOwner V))
    (seed : ∀ j, Stacks (port j).tapes prime) (jobs : List α) :
    Stacks (SharedBankStage.compile _ (Nat.zero_lt_succ k)
      (jobs.map fun j => placePort (slot j) (port j))).tapes prime :=
  match jobs with
  | [] => blankPortStacks _
  | j :: js => adjacentStageStacks
      (adjacentStageStacks (blankPortStacks _) (adjacentStageStacks (seed j) (blankPortStacks k)))
      (compiledPortStacks slot port seed js)

/-- Each scheduled occurrence has a disjoint physical bank containing its
port tapes followed by the spare slots introduced by placement. -/
theorem compiledPortBanks {k V : ℕ} {α : Type*} (slot : α → Fin (k+1))
    (port : α → SharedBankStage.Stage _ 1 prime (@portOwner V)) (jobs : List α) :
    let stage := SharedBankStage.compile _ (Nat.zero_lt_succ k) (jobs.map fun a => placePort (slot a) (port a))
    ∃ bank : ∀ a : Fin jobs.length, Fin ((port jobs[a]).tapes+k) ↪ Fin stage.tapes,
      (∀ a b, a ≠ b → ∀ h l, bank a h ≠ bank b l) ∧
      ∀ seed a h, let S := compiledPortStacks slot port seed jobs
        let words := adjacentStageStacks (seed jobs[a]) (blankPortStacks k)
        S.L (bank a h) = words.L h ∧ S.R (bank a h) = words.R h := by
  have left {m n} (L : Stacks m prime) (R : Stacks n prime) (i : Fin m) :
      (adjacentStageStacks L R).L (i.castAdd n) = L.L i ∧ (adjacentStageStacks L R).R (i.castAdd n) = L.R i := by
    simp [adjacentStageStacks]
  have right {m n} (L : Stacks m prime) (R : Stacks n prime) (i : Fin n) :
      (adjacentStageStacks L R).L (i.natAdd m) = R.L i ∧ (adjacentStageStacks L R).R (i.natAdd m) = R.R i := by
    simp [adjacentStageStacks]
  induction jobs with
  | nil => exact ⟨fun a => Fin.elim0 a,fun a => Fin.elim0 a,fun _ a => Fin.elim0 a⟩
  | cons j jobs ih =>
    obtain ⟨bank,separate,read⟩ := ih
    let tail := SharedBankStage.compile _ (Nat.zero_lt_succ k) (jobs.map fun a => placePort (slot a) (port a))
    let head := (Fin.natAddEmb (k+1) (m := (port j).tapes+k)).trans (Fin.castAddEmb tail.tapes)
    let rest := Fin.natAddEmb ((k+1)+((port j).tapes+k)) (m := tail.tapes)
    have apart (h l) : head h ≠ rest l := by
      intro eq
      have val := congrArg Fin.val eq
      change k+1+h.val = (k+1+((port j).tapes+k))+l.val at val
      omega
    let place (a : Fin (j :: jobs).length) : Fin ((port ((j :: jobs)[a])).tapes+k) ↪ Fin _ :=
      Fin.cases head (fun b => (bank b).trans rest) a
    refine ⟨place,?_,?_⟩
    · intro a b ne
      induction a using Fin.cases with
      | zero =>
        induction b using Fin.cases with
        | zero => exact False.elim (ne rfl)
        | succ b => exact fun h l => apart h (bank b l)
      | succ a =>
        induction b using Fin.cases with
        | zero => exact fun h l => (apart l (bank a h)).symm
        | succ b => exact fun h l => rest.injective.ne (separate a b (fun eq => ne (congrArg Fin.succ eq)) h l)
    · intro seed a
      induction a using Fin.cases with
      | zero =>
        intro h
        let words := adjacentStageStacks (seed j) (blankPortStacks k)
        let localBank := adjacentStageStacks (blankPortStacks (k+1)) words
        have outer := left localBank (compiledPortStacks slot port seed jobs) (h.natAdd (k+1))
        have inner := right (blankPortStacks (k+1)) words h
        exact ⟨outer.1.trans inner.1,outer.2.trans inner.2⟩
      | succ b =>
        intro h
        let localBank := adjacentStageStacks (blankPortStacks (k+1))
          (adjacentStageStacks (seed j) (blankPortStacks k))
        have outer := right localBank (compiledPortStacks slot port seed jobs) (bank b h)
        exact ⟨outer.1.trans (read seed b h).1,outer.2.trans (read seed b h).2⟩


theorem compiledPortStacks_rep {k V : ℕ} {α : Type*} (slot : α → Fin (k+1))
    (port : α → SharedBankStage.Stage _ 1 prime (@portOwner V)) (seed : ∀ j, Stacks (port j).tapes prime)
    (jobs : List α) (ready : ∀ j ∈ jobs, RepT (port j).metadata (seed j).L (seed j).R) :
    let stage := SharedBankStage.compile _ (Nat.zero_lt_succ k) (jobs.map fun j => placePort (slot j) (port j))
    let S := compiledPortStacks slot port seed jobs
    RepT stage.metadata S.L S.R := by
  induction jobs with
  | nil => exact blankPortStacks_rep _
  | cons j js ih =>
    exact adjacentPortStacks_rep (adjacentPortStacks_rep (blankPortStacks_rep _)
      (adjacentPortStacks_rep (ready j List.mem_cons_self) (blankPortStacks_rep k)))
      (ih (fun i hi => ready i (List.mem_cons_of_mem _ hi)))

/-- Placing and sequencing any number of ports requires only the private
words used by each one-port pass. Shared owner slots start blank in the seed. -/
theorem compiledPortSeed {k V : ℕ} {α : Type*} (slot : α → Fin (k+1))
    (port : α → SharedBankStage.Stage _ 1 prime (@portOwner V)) (jobs : List α)
    (seed : ∀ j ∈ jobs, HasStackSeed (port j).metadata) :
    let stage := SharedBankStage.compile _ (Nat.zero_lt_succ k) (jobs.map fun j => placePort (slot j) (port j))
    ∃ S, ChartPrivateReady stage S := by
  intro stage
  classical
  let S (j : α) := if h : j ∈ jobs then (seed j h).choose else blankPortStacks (port j).tapes
  have rep := compiledPortStacks_rep slot port S jobs (fun j hj => by
    simpa only [S,dite_eq_left hj] using (seed j hj).choose_spec)
  exact ⟨compiledPortStacks slot port S jobs,fun i _ => rep i⟩

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
