module

public import IntegerMultBounds.MathlibTM2.M6.BitCompactBandStage
public import IntegerMultBounds.MathlibTM2.M6.BitFlatNodeHandoff
public import IntegerMultBounds.MathlibTM2.M6.BitSeededIdleWindow
public import IntegerMultBounds.MathlibTM2.M6.BitCutoffBandSupplier

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Certificates.PR589 RecursiveInterchangeLayout
open Shared50ModularControl (prime)

private theorem stageInParent {P U : Type} {T Q w W V Z price : ℕ} (n : Fin 9)
    (tailEq : W = Z) (size : (prime^w)^128*W = V)
    {body : P → Pr P T Q prime U} {code src dst seed}
    (run : PackedPieceHandoffWithReserve cleanupWeight (fun l r => ∑ j, cleanupWeight (l j) (r j)) V
      (fun x y => ∀ j : Fin W, let addr := fun z => (flatWindowEquiv w W (windowState w z,j)).cast size
        readRoles addr y = (Piece.stage n).run (readRoles addr x)) body code src dst seed price) :
    PackedPieceHandoffWithReserve cleanupWeight (fun l r => ∑ j, cleanupWeight (l j) (r j)) ((prime^w)^128*Z)
      (fun x y => ∀ j : Fin Z, let addr := fun z => flatWindowEquiv w Z (windowState w z,j)
        readRoles addr y = (Piece.stage n).run (readRoles addr x)) body code src dst seed price := by
  subst Z V
  exact run

/-- Install all compact stages and bridges in the parent. The remaining
supplier provides only the nine remainder windows in flat node order. -/
theorem compactBandParent [M8.Machine.Net] {U Config : Type} :
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q → ∃ (bridgeRate : ℕ) (stageRate : Fin 9 → ℝ),
    ∀ (input : Config → CutoffNodeInput) (_band : ∀ c, 7*((input c).w+1) ≤ (input c).cutoff)
      (σ : ℝ), 0 ≤ σ →
    let w := fun c => (input c).w+1
    let W := fun c => (input c).idleWidth*142080
    let V := fun c => (input c).cells
    let scale := fun c => ((input c).node.width : ℝ)^σ*((input c).cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ)*V c
    ∀ idleCost : Config → Fin 9 → ℕ,
    (∀ n : Fin 9, ∃ (P : Type) (T : ℕ) (body : P → Pr P T Q prime U), ∃ code src dst, ∃ seed : Config → Stacks T prime,
      ∀ c, PackedPieceHandoffWithReserve cleanupWeight (fun l r => ∑ j, cleanupWeight (l j) (r j)) (V c)
        (fun x y => ∀ j : Fin (W c), let addr := fun z => flatWindowEquiv (w c) (W c) (windowState (w c) z,j)
          readRoles addr y = (Piece.remainder n.val).run (readRoles addr x)) body code src dst (seed c) (idleCost c n)) →
    ∃ (P : Type) (T : ℕ) (body : P → Pr P T Q prime U), ∃ code src dst, ∃ seed : Config → Stacks T prime,
      ∀ c, PackedPieceHandoffWithReserve cleanupWeight (fun l r => ∑ j, cleanupWeight (l j) (r j)) (V c)
        (packedChildOutput (w c) (V c)) body code src dst (seed c)
        ((∑ i, ⌊stageRate i*scale c⌋₊)+(∑ i, idleCost c i)+bridgeRate*V c+2) := by
  classical
  choose qs stages using packedCompactBandStage
  obtain ⟨q,build⟩ := assembledFlatNodeWithCounters (U := U) (Config := Config)
  refine ⟨max (Finset.univ.sup qs) q,?_⟩
  intro Q fits
  obtain ⟨bridgeRate,assemble⟩ := build ((le_max_right ..).trans fits)
  choose T src dst Label host code rate run using fun n => stages n (U := U)
    ((Finset.le_sup (Finset.mem_univ n)).trans ((le_max_left ..).trans fits))
  refine ⟨bridgeRate,rate,?_⟩
  intro input band σ positive w W V scale idleCost windows
  have pos (c) : 0 < V c := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
    (Nat.mul_pos (input c).idlePositive (by decide))
  have parent := assemble (fun _ => True) (fun _ => trivial) (fun _ _ _ _ => trivial)
    w W V (fun _ => rfl) pos (fun _ => Equiv.refl _) (fun c i => ⌊rate i*scale c⌋₊) idleCost
  simp only [true_and,Equiv.refl_apply] at parent
  apply parent
  · intro n
    choose seed step using fun c => run n (input c) (band c) σ positive
    exact ⟨Label n,T n,host n,code n,src n,dst n,seed,fun c => stageInParent n (input c).stageTail
      (input c).sweepVolume (step c)⟩
  · exact windows

/-- The compact parent executes both the nine stage sweeps and their compiled
remainder windows. Recursive work is supplied at active idle records only. -/
theorem compactBandParentWithRecords [M8.Machine.Net] {U Config : Type} :
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q →
    ∀ {P : Type} {N : ℕ} {body : P → Pr P N Q prime U} {dst : Fin (142081+2) ↪ Fin N} {leafRate : ℝ}
      {Child : Type} {childInput : Child → CutoffNodeInput} {permits : Child → ℕ → ℕ → Prop},
    RecordTreeFamily childInput body dst leafRate permits →
    ∃ (bridgeRate : ℕ) (stageRate : Fin 9 → ℝ) (init fixed base swaps : Fin 9 → ℕ)
      (minimum : ℝ) (leaf : Fin 9 → ℝ), ∀ D, minimum ≤ D →
    ∀ (input : Config → CutoffNodeInput) (blocks : Config → ℕ),
      (∀ c, 7*((input c).w+1) ≤ (input c).cutoff) →
      (∀ c, (input c).root.Positive) → (∀ c, 142080^((input c).depth+1) ∣ (input c).root.rows) →
      (∀ c, (input c).root.beforeH = blocks c*prime^(64*(input c).root.width)) →
      let child c i j := scheduledChild prime (input c).node (idleDirectoryIndex (i,j))
      (∀ c i j, (input c).cutoff < (child c i j).width →
        ChildRecordAt childInput permits D leafRate (input c) (idleDirectoryIndex (i,j))) →
      let branch c i j := let p := input c; if p.cutoff < (child c i j).width then
        idleRecordOverhead p (fixed i) (base i) (swaps i)+cutoffTreeBudget D leafRate p.cutoff
          (p.depth-(p.path.length+1)) (child c i j)
        else ⌊leaf i*((child c i j).width : ℝ)^M8.Machine.BudgetBound.tau*volume prime (child c i j)⌋₊
      let idleCost c i := let V := (input c).cells
                          init i*V+(735*V+(∑ j, branch c i j)+1)+(142081*(10*V+10)+1)
      ∀ σ : ℝ, 0 ≤ σ →
      ∃ (A : Type) (T : ℕ) (host : A → Pr A T Q prime U), ∃ code src dst, ∃ seed : Config → Stacks T prime,
        ∀ c, let p := input c
        PackedPieceHandoffWithReserve cleanupWeight (fun l r => ∑ j, cleanupWeight (l j) (r j)) p.cells
          (packedChildOutput (p.w+1) p.cells) host code src dst (seed c)
          ((∑ i, ⌊stageRate i*((p.node.width : ℝ)^σ*(p.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ)*p.cells)⌋₊)+
            (∑ i, idleCost c i)+bridgeRate*p.cells+2) := by
  classical
  obtain ⟨q,parent⟩ := compactBandParent (U := U) (Config := Config)
  let merge := 7+(CyclicRowCycle.states 142080+5)+4
  let header := (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080)
  let swap := (@rowSwapBlock BinaryRadixEqualShared.supplierNet).states
  refine ⟨max q (max columnCapacity (max swap (max (merge+merge) header))),?_⟩
  intro Q fits P N body dst leafRate Child childInput permits family
  obtain ⟨bridgeRate,stageRate,assemble⟩ := parent ((Nat.le_max_left ..).trans fits)
  have room := (Nat.le_max_right ..).trans fits
  have workerRoom := (Nat.le_max_right ..).trans room
  have aux := (Nat.le_max_right ..).trans workerRoom
  choose T table program src out seed init fixed base swaps minimum leaf loader nonneg positive run using
    fun i => seededIdleWindowWithReserve family ((Nat.le_max_left ..).trans room) ((Nat.le_max_left ..).trans workerRoom)
      ((Nat.le_max_left ..).trans aux) ((Nat.le_max_right ..).trans aux) i (fun l r => ∑ j, cleanupWeight (l j) (r j))
  obtain ⟨M,bound⟩ := Finite.exists_le minimum
  refine ⟨bridgeRate,stageRate,init,fixed,base,swaps,M,leaf,?_⟩
  intro D enough input blocks band root rows label child children branch idleCost σ nonnegσ
  apply assemble input band σ nonnegσ idleCost
  intro i
  exact ⟨_,T i,table i,program i,src i,out i,seed i ∘ input,fun c =>
    run i D ((bound i).trans enough) (input c) (blocks c) (root c) (rows c) (label c) (children c i)⟩

private structure ActiveBandRecord where
  input : CutoffNodeInput
  blocks : ℕ
  positive : input.root.Positive
  rows : 142080^(input.depth+1) ∣ input.root.rows
  label : input.root.beforeH = blocks*prime^(64*input.root.width)
  active : input.cutoff < input.node.width
  band : 7*(input.w+1) ≤ input.cutoff

/-- A seeded compact parent with its active idle records executed by the
bounded-height band tree and its stopped records executed by the leaf machine. -/
theorem compactBandParentExecution {U Config : Type} :
    let _ := BinaryRadixEqualShared.supplierNet
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q →
    ∃ (bridgeRate : ℕ) (stageRate : Fin 9 → ℝ) (init fixed base swaps : Fin 9 → ℕ)
      (leafRate minimum : ℝ) (leaf : Fin 9 → ℝ), ∀ D, minimum ≤ D →
    ∀ (input : Config → CutoffNodeInput) (blocks : Config → ℕ),
      (∀ c, 7*((input c).w+1) ≤ (input c).cutoff) →
      (∀ c, (input c).root.Positive) → (∀ c, 142080^((input c).depth+1) ∣ (input c).root.rows) →
      (∀ c, (input c).root.beforeH = blocks c*prime^(64*(input c).root.width)) →
      let child c i j := scheduledChild prime (input c).node (idleDirectoryIndex (i,j))
      let branch c i j := let p := input c; if p.cutoff < (child c i j).width then
        idleRecordOverhead p (fixed i) (base i) (swaps i)+cutoffTreeBudget D leafRate p.cutoff
          (p.depth-(p.path.length+1)) (child c i j)
        else ⌊leaf i*((child c i j).width : ℝ)^M8.Machine.BudgetBound.tau*volume prime (child c i j)⌋₊
      let idleCost c i := let V := (input c).cells
                          init i*V+(735*V+(∑ j, branch c i j)+1)+(142081*(10*V+10)+1)
      ∀ σ : ℝ, 0 ≤ σ →
      ∃ (A : Type) (T : ℕ) (host : A → Pr A T Q prime U), ∃ code src dst, ∃ seed : Config → Stacks T prime,
        ∀ c, let p := input c
        PackedPieceHandoffWithReserve cleanupWeight (fun l r => ∑ j, cleanupWeight (l j) (r j)) p.cells
          (packedChildOutput (p.w+1) p.cells) host code src dst (seed c)
          ((∑ i, ⌊stageRate i*((p.node.width : ℝ)^σ*(p.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ)*p.cells)⌋₊)+
            (∑ i, idleCost c i)+bridgeRate*p.cells+2) := by
  intro inst
  obtain ⟨q,build⟩ := compactBandParentWithRecords (U := U) (Config := Config)
  obtain ⟨r,tree⟩ := cutoffBandTree U
  refine ⟨max q r,?_⟩
  intro Q fits
  obtain ⟨_,_,_,_,leafRate,install⟩ := tree ((le_max_right ..).trans fits)
  have family := install ActiveBandRecord.input ActiveBandRecord.blocks ActiveBandRecord.positive
    ActiveBandRecord.rows ActiveBandRecord.label ActiveBandRecord.active ActiveBandRecord.band
  obtain ⟨bridge,stage,init,fixed,base,swaps,minimum,leaf,run⟩ := build ((le_max_left ..).trans fits) family
  refine ⟨bridge,stage,init,fixed,base,swaps,leafRate,minimum,leaf,?_⟩
  intro D enough input blocks band root rows label child
  apply run D enough input blocks band root rows label
  intro x i j active c node rootEq _ cut depth live
  have width := (activeIdleRecordWidth (input x) i j (band x) active).2
  rw [← node,c.width] at width
  have atoms : c.w+1 ≤ (input x).w+1 := by omega
  exact ⟨⟨c,blocks x,rootEq ▸ root x,by simpa only [rootEq,depth] using rows x,
    rootEq ▸ label x,live,cut ▸ (Nat.mul_le_mul_left 7 atoms).trans (band x)⟩,rfl,fun _ _ => trivial⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
