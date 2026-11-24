module

public import IntegerMultBounds.MathlibTM2.M6.BitSeededIdleWindow

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout

/-- Assemble the parent from its packed sweeps and the compiled idle windows.
The idle branches inherit one recurrence coefficient across all nine stages. -/
theorem assembledIdleParent [M8.Machine.Net] {P U Config : Type} {N : ℕ} :
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q →
    ∀ {body : P → Pr P N Q prime U} {dst : Fin (142081+2) ↪ Fin N} {leafRate : ℝ}
      {childBudget : {c : CutoffNodeInput // c.cutoff < c.node.width} → ℕ → ℕ},
    SplitRecordTreeFamily Subtype.val body dst leafRate childBudget →
    ∃ (init fixed base swaps : Fin 9 → ℕ) (minimum : ℝ) (leaf : Fin 9 → ℝ) (assemble : ℕ),
    0 ≤ minimum ∧ (∀ i, 0 ≤ leaf i) ∧ ∀ D, minimum ≤ D →
    ∀ (input : Config → CutoffNodeInput) (blocks : Config → ℕ),
    (∀ c, (input c).root.Positive) → (∀ c, 142080^((input c).depth+1) ∣ (input c).root.rows) →
    (∀ c, (input c).root.beforeH = blocks c*prime^(64*(input c).root.width)) →
    let child := fun c i j => scheduledChild prime (input c).node (idleDirectoryIndex (i,j))
    let fuel := fun c => (input c).depth-((input c).path.length+1)
    (∀ c i j, let p := input c; p.cutoff < (child c i j).width →
      ∀ (x : {v : CutoffNodeInput // v.cutoff < v.node.width}),
        x.val.root = p.root → x.val.path = p.path++[idleDirectoryIndex (i,j)] → x.val.cutoff = p.cutoff →
        ∀ k : Fin nodeChildren5.length, let d := scheduledChild prime (child c i j) k
        p.cutoff < d.width → childBudget x k.val ≤ cutoffTreeBudget D leafRate p.cutoff (fuel c-1) d) →
    let branch := fun c i j => let p := input c; if p.cutoff < (child c i j).width then
      idleRecordOverhead p (fixed i) (base i) (swaps i)+cutoffTreeBudget D leafRate p.cutoff (fuel c) (child c i j)
      else ⌊leaf i*((child c i j).width : ℝ)^M8.Machine.BudgetBound.tau*volume prime (child c i j)⌋₊
    let idleCost := fun c i => let V := (input c).cells
                              init i*V+(735*V+(∑ j, branch c i j)+1)+(142081*(10*V+10)+1)
    let load := fun {T : ℕ} (seed : Config → Stacks T prime) =>
      LoadsPackedSeed (nodeSeedWords ∘ input) (CutoffNodeInput.cells ∘ input) seed
    ∀ sweepCost : Config → Fin 9 → ℕ,
    (∀ i, ∃ (A : Type) (T : ℕ) (host : A → Pr A T Q prime U), ∃ code src dst seed, load seed ∧
      ∀ c, let p := input c
      PackedPieceHandoffWithCharge cleanupWeight p.cells
        (fun x y => ∀ j : Fin (p.idleWidth*142080),
          let addr := fun z => flatWindowEquiv (p.w+1) (p.idleWidth*142080) (windowState (p.w+1) z,j)
          readRoles addr y = (Piece.stage i).run (readRoles addr x))
        host code src dst (seed c) (sweepCost c i)) →
    ∃ (A : Type) (T : ℕ) (host : A → Pr A T Q prime U), ∃ code src dst seed, load seed ∧
      ∀ c, let p := input c
      PackedPieceHandoffWithCharge cleanupWeight p.cells (packedChildOutput (p.w+1) p.cells)
        host code src dst (seed c) ((∑ i, sweepCost c i)+(∑ i, idleCost c i)+assemble*p.cells+2) := by
  classical
  obtain ⟨q,build⟩ := assembledFlatNodeFamilyWithSeed (U := U) (Config := Config)
  let merge := 7+(CyclicRowCycle.states 142080+5)+4
  let header := (fun {n : ℕ} (_ : Program 38 n prime) => n) (RecursiveRowsNodeHeaders.program 142080)
  let swap := (@rowSwapBlock BinaryRadixEqualShared.supplierNet).states
  refine ⟨max q (max columnCapacity (max swap (max (merge+merge) header))),?_⟩
  intro Q fits body dst leafRate childBudget family
  obtain ⟨assemble,join⟩ := build ((Nat.le_max_left ..).trans fits)
  have room := (Nat.le_max_right ..).trans fits
  have workerRoom := (Nat.le_max_right ..).trans room
  have aux := (Nat.le_max_right ..).trans workerRoom
  choose T table program src out seed init fixed base swaps minimum leaf loader nonneg positive run using
    fun i => seededIdleWindow family ((Nat.le_max_left ..).trans room) ((Nat.le_max_left ..).trans workerRoom)
      ((Nat.le_max_left ..).trans aux) ((Nat.le_max_right ..).trans aux) i
  refine ⟨init,fixed,base,swaps,∑ i, minimum i,leaf,assemble,Finset.sum_nonneg (fun i _ => nonneg i),positive,?_⟩
  intro D enough input blocks root rows label child fuel children branch idleCost load sweepCost sweeps
  have pos c : 0 < (input c).cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
    (Nat.mul_pos (input c).idlePositive (by decide))
  have parent := join (@load) (LoadsPackedSeed.fixed _ _ pos) (fun _ _ => LoadsPackedSeed.join)
    (fun c => (input c).w+1) (fun c => (input c).idleWidth*142080) (fun c => (input c).cells)
    (fun _ => rfl) pos (fun _ => Equiv.refl _) sweepCost idleCost
  apply parent sweeps
  intro i
  refine ⟨_,T i,table i,program i,src i,out i,seed i ∘ input,?_,?_⟩
  · obtain ⟨rate,install⟩ := loader i
    refine ⟨rate,?_⟩
    intro P U T Q body bank source apart
    obtain ⟨code,exec⟩ := install body bank source apart
    exact ⟨code,fun c => exec (input c)⟩
  · intro c
    have bound := (Finset.single_le_sum (fun j _ => nonneg j) (Finset.mem_univ i)).trans enough
    exact run i D bound (input c) (blocks c) (root c) (rows c) (label c) (children c i)

end IntegerMultBounds.MathlibTM2.M6.BitNode
