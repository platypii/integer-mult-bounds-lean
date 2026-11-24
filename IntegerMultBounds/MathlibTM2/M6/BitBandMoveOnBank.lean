module

public import IntegerMultBounds.MathlibTM2.M6.BitPhaseBandMove

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine RecursiveInterchangeLayout
open Shared50ModularControl (prime)

/-- A fixed extra suffix supplies the compact bank. Its blank-frame charge
is absorbed into a single volume rate for every invocation at this rank. -/
theorem bandMoveOnBank {U : Type} :
    let _ := BinaryRadixEqualShared.supplierNet
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q → ∃ minimum leafRate : ℝ, ∀ D, minimum ≤ D →
      ∃ N : ℕ, rowSwapBlock.tapes ≤ N ∧ ∀ {H : ℕ} (ports : Fin (N+35) ↪ Fin H) (rank : ℕ), rank ≤ 8 →
      ∃ (P : Type) (table : P → Pr P H Q prime U) (code : Pr P H Q prime U) (rate : ℕ),
      ∀ (a : ActiveBandRecord) (node : Descriptor) (w W L : ℕ), let p := a.input
      let V := (prime^(w+1))^16*W
      ∀ position : Fin (volume prime p.node) ≃ Fin V,
        (∀ i, (position i).val = (CopyChildLayout.packActive p.node i).val) →
        0 < W → p.node.width = (w+1)*rank → ((w+1)*rank).size ≤ L → p.cutoff < 2^L → L ≤ p.cutoff →
        MoveOnBankExec node p.node w W ports (binSyms L p.cutoff) position table code
          (cutoffTreeBudget D leafRate p.cutoff (p.depth-p.path.length) p.node+rate*V) true := by
  intro inst
  obtain ⟨states,compile⟩ := phaseBandWorker (U := U)
  refine ⟨states,?_⟩
  intro Q enough
  obtain ⟨minimum,R,build⟩ := compile enough
  refine ⟨minimum,R,?_⟩
  intro D large
  obtain ⟨B,worker⟩ := build D large
  let N := rowSwapBlock.tapes+B
  refine ⟨N,by dsimp [N]; omega,?_⟩
  intro H ports rank fits
  let front : Fin (rowSwapBlock.tapes+35) ↪ Fin (N+35) := Fin.castLEEmb (by dsimp [N]; omega)
  let back : Fin B ↪ Fin (N+35) := ⟨fun i => ⟨rowSwapBlock.tapes+35+i.val,by dsimp [N]; omega⟩,
    fun i j eq => Fin.ext (by have := congrArg Fin.val eq; dsimp at this; omega)⟩
  let r := BandPhase.slot.trans (front.trans ports)
  have apart (i : Fin B) (j : Fin 94) : ports (back i) ≠ r j := by
    intro eq
    have h := congrArg Fin.val (ports.injective eq)
    change rowSwapBlock.tapes+35+i.val = j.val at h
    have := rowSwapFits
    omega
  obtain ⟨P,table,inner,rate,run⟩ := worker (front.trans ports) (back.trans ports)
    (fun i j => apart i _) (fun i j => apart i _) (fun i j => apart i _) rank fits
  let slot := front (BandPhase.slot 35)
  obtain ⟨code,openCall⟩ := packedMoveRecordCall table inner ports slot (by decide : 35 ≤ (35 : ℕ)) rank fits
  let c := rate+19100000034
  let overhead := (prime+8)*(B*2)
  refine ⟨P,table,code,c+overhead+30400,?_⟩
  intro a node w W L p V position packed rows width precision cutFits short
  let tree := cutoffTreeBudget D R p.cutoff (p.depth-p.path.length) p.node
  have eq : volume prime p.node = V := by simpa only [Fintype.card_fin] using Fintype.card_congr position
  let lane := packedDescriptor p.node.width (CopyChildLayout.spectators p.node)
  have size : volume prime lane = V := by rw [← eq]; simp only [lane,packedDescriptor,volume,CopyChildLayout.spectators]; ring
  have pos : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) rows
  have result := openCall node p.node w W L p.cutoff (tree+(c+overhead)*V) rows width position packed
  rw [Nat.add_mul (c+overhead),← Nat.add_assoc]
  apply result
  intro x u S fields cut clock base clean data
  have fresh (i : Fin B) := clean (back i) (by change 35 ≤ rowSwapBlock.tapes+35+i.val; omega) (by
    intro e
    exact apart i 35 (congrArg ports e))
  obtain ⟨z,F,t,exec,user,paid,out,frame⟩ := run a w L x u S width precision cutFits short clock cut base
    ((fields 5).trans (canonicalBits_symbols _)) ((fields 3).trans (canonicalBits_symbols _)) (fun i hi =>
      clean (front (BandPhase.slot i)) hi.le (by intro e; have h := congrArg Fin.val e; change i.val = 35 at h; omega)) data
  have fixed : ((frameSlots (back.trans ports)).map (fun j => (S.L j).length+(S.R j).length+2)).sum = B*2 := by
    have words := List.map_congr_left (l := frameSlots (back.trans ports))
      (f := fun j => (S.L j).length+(S.R j).length+2) (g := fun _ => 2) (fun j hj => by
        obtain ⟨i,rfl⟩ := (mem_frameSlots _ j).mp hj
        simp [(fresh i).1,(fresh i).2,Function.Embedding.trans_apply])
    rw [words]; simp [frameSlots_length]
  rw [fixed,size] at paid
  refine ⟨z,F,t,exec,?_,user,out,frame⟩
  intro js nd
  apply (paid js nd).trans (Nat.add_le_add_left ?_ _)
  change tree+c*V+overhead ≤ tree+(c+overhead)*V
  have h := Nat.le_mul_of_pos_right overhead pos
  rw [Nat.add_mul c overhead,← Nat.add_assoc]; exact Nat.add_le_add_left h _

/-- At a parent schedule position, the compact MOVE spends the child's
recursive bill and a fixed multiple of the parent's cell count. -/
theorem scheduledBandMoveOnBank {U : Type} :
    let _ := BinaryRadixEqualShared.supplierNet
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q → ∃ minimum leafRate : ℝ, ∀ D, minimum ≤ D →
      ∃ N : ℕ, rowSwapBlock.tapes ≤ N ∧ ∀ {H : ℕ} (ports : Fin (N+35) ↪ Fin H) (rank : ℕ), rank ≤ 7 →
      ∃ (P : Type) (table : P → Pr P H Q prime U) (code : Pr P H Q prime U) (rate : ℕ),
      ∀ (p : CutoffNodeInput) (blocks : ℕ) (i : Fin nodeChildren5.length),
        let child := scheduledChild prime p.node i
        let V := (prime^(p.w+1))^16*p.stageWidth
        p.root.Positive → 142080^(p.depth+1) ∣ p.root.rows →
        p.root.beforeH = blocks*prime^(64*p.root.width) → nodeChildren5[i.val] = rank →
        p.cutoff < child.width → 49*(p.w+1) ≤ 64*p.cutoff →
        ∀ position : Fin (volume prime child) ≃ Fin V,
          (∀ j, (position j).val = (CopyChildLayout.packActive child j).val) →
          MoveOnBankExec p.node child p.w p.stageWidth ports (binSyms p.root.width.size p.cutoff) position table code
            (cutoffTreeBudget D leafRate p.cutoff (p.depth-(p.path.length+1)) child+rate*p.cells) true := by
  intro inst
  obtain ⟨states,compile⟩ := bandMoveOnBank (U := U)
  refine ⟨states,?_⟩
  intro Q room
  obtain ⟨minimum,R,build⟩ := compile room
  refine ⟨minimum,R,?_⟩
  intro D large
  obtain ⟨N,space,place⟩ := build D large
  refine ⟨N,space,?_⟩
  intro H ports rank fits
  obtain ⟨P,table,code,rate,call⟩ := place ports rank (fits.trans (by decide))
  refine ⟨P,table,code,rate,?_⟩
  intro p blocks i child V positive rows label kind live band position packed
  have next : (p.path++[i]).foldl (scheduledChild prime) p.root = child := by
    simp [child,CutoffNodeInput.node,List.foldl_append]
  obtain ⟨c,root,path,depth,_,cut⟩ := activeCutoffNodeInput p.root p.depth p.b p.cutoff blocks
    positive p.levels p.base p.rootWidth rows label p.stop _ (next ▸ live)
  have node : c.node = child := by simpa only [CutoffNodeInput.node,root,path] using next
  have shape : child.width = (p.w+1)*rank := by
    change nodeChildren5[i.val]*(p.node.width/64) = _
    rw [kind,p.width,Nat.mul_div_cancel_left _ (by decide),Nat.mul_comm]
  have childBand : 7*child.width ≤ 64*p.cutoff := by
    rw [shape]
    have bound := Nat.mul_le_mul_left (p.w+1) fits
    omega
  have small : 7*(c.w+1) ≤ c.cutoff := by rw [← node,c.width] at childBand; rw [cut]; omega
  let a : ActiveBandRecord := ⟨c,blocks,root ▸ positive,by simpa only [root,depth] using rows,
    root ▸ label,by simpa only [cut,node] using live,small⟩
  have below : child.width ≤ p.root.width := by
    have h := directoryDigits_bound prime p.root (p.path++[i])
    rw [next] at h
    omega
  have cutFits := (live.trans_le below).trans (Nat.lt_size_self _)
  have precision := Nat.size_le_size below
  have short : p.root.width.size ≤ p.cutoff := Nat.size_le.mpr (by
    have h := alignedRootWidth_le p.root p.depth p.b p.cutoff p.levels p.base p.rootWidth p.stop
    have pos : 0 < p.root.width := p.rootWidth ▸ Nat.mul_pos (pow_pos (by decide) _) p.base
    omega)
  have cells : 0 < p.cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
    (Nat.mul_pos p.idlePositive (by decide : 0 < 142080))
  have exec := call a p.node p.w p.stageWidth p.root.width.size
  dsimp only [a] at exec
  rw [node,cut,depth,path,List.length_append,List.length_singleton] at exec
  rw [shape] at precision
  have run := exec position packed (Nat.pos_of_mul_pos_left (p.stageCells ▸ cells)) shape precision cutFits short
  simpa only [p.stageCells] using run

end IntegerMultBounds.MathlibTM2.M6.BitNode
