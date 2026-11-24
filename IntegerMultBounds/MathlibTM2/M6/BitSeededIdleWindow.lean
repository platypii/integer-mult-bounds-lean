module

public import IntegerMultBounds.MathlibTM2.M6.BitIdleWindowHandoff

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback SweepFile M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout

/-- A fixed packed remainder program with an initializer composable by the
nine-stage parent. Runtime division touches only the shared archive. -/
theorem seededIdleWindow [M8.Machine.Net] {P U : Type} {N Q : ℕ}
    {body : P → Pr P N Q prime U} {dst : Fin (142081+2) ↪ Fin N} {leafRate : ℝ}
    {permits : {c : CutoffNodeInput // c.cutoff < c.node.width} → ℕ → ℕ → Prop}
    (family : RecordTreeFamily Subtype.val body dst leafRate permits)
    (column : columnCapacity ≤ Q) (swapCap : (@rowSwapBlock BinaryRadixEqualShared.supplierNet).states ≤ Q)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (headerCap : (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q)
    (i : Fin 9) :
    let Job := Fin idleCopies.length
    let Label := (Job ⊕ (Σ _ : Job, Option (Empty ⊕ P))) ⊕ Job
    ∃ (T : ℕ) (table : Label → Pr Label T Q prime U) (code : Pr Label T Q prime U) (src dst : Fin (142081+2) ↪ Fin T)
      (seed : CutoffNodeInput → Stacks T prime) (init fixed base swaps : ℕ) (minimum C : ℝ),
      LoadsPackedSeed nodeSeedWords CutoffNodeInput.cells seed ∧ 0 ≤ minimum ∧ 0 ≤ C ∧
      ∀ D, minimum ≤ D → ∀ (p : CutoffNodeInput) blocks, p.root.Positive → 142080^(p.depth+1) ∣ p.root.rows →
      p.root.beforeH = blocks*prime^(64*p.root.width) →
      let child j := scheduledChild prime p.node (idleDirectoryIndex (i,j))
      let fuel := p.depth-(p.path.length+1)
      (∀ j, p.cutoff < (child j).width → ∀ (x : {c : CutoffNodeInput // c.cutoff < c.node.width}),
        x.val.root = p.root → x.val.path = p.path++[idleDirectoryIndex (i,j)] → x.val.cutoff = p.cutoff →
        ∀ k : Fin nodeChildren5.length, let d := scheduledChild prime (child j) k
        p.cutoff < d.width → permits x k.val (cutoffTreeBudget D leafRate p.cutoff (fuel-1) d)) →
      let branch j := if p.cutoff < (child j).width then idleRecordOverhead p fixed base swaps+
        cutoffTreeBudget D leafRate p.cutoff fuel (child j)
        else ⌊C*((child j).width : ℝ)^M8.Machine.BudgetBound.tau*volume prime (child j)⌋₊
      PackedPieceHandoffWithCharge cleanupWeight p.cells
        (fun x y => ∀ j : Fin (p.idleWidth*142080),
          let addr := fun v => flatWindowEquiv (p.w+1) (p.idleWidth*142080) (windowState (p.w+1) v,j)
          readRoles addr y = (Piece.remainder i.val).run (readRoles addr x))
        table code src dst (seed p) ((init*p.cells+(735*p.cells+(∑ j, branch j)+1))+(142081*(10*p.cells+10)+1)) := by
  intro Job Label
  let owner : Job ↪ Fin 142081 := ⟨fun j => idleTape i idleCopies[j.val],fun {a b} eq =>
    (idleCopyIndex_at a).symm.trans ((congrArg idleCopyIndex ((idleTape_injective i) eq)).trans (idleCopyIndex_at b))⟩
  obtain ⟨H,fan,board,seed,loader,payload,rawOff,fieldOff,build⟩ := seededIdleCallerBoards (P := Empty) (U := U) owner headerCap
  obtain ⟨divide,init,divideRun⟩ := build Empty.elim
  let X := intervalHostSize (113+intervalSplitTapes) N
  let front := Fin.castAddEmb X (n := H)
  let raw j := ((Fin.castAddEmb 6 (n := 72)).trans (board j)).trans front
  let fields j := ((Fin.natAddEmb 72 (m := 6)).trans (board j)).trans front
  obtain ⟨active,scratch,minimum,fixed,base,swaps,nonneg,large⟩ := installedIdleWindow family swapCap capacity i board
  obtain ⟨K,C,table,code,pos,_,dispatch⟩ := dispatchIdleWindow column capacity i active Sum.inl raw fields
    (scratch.map (Fin.natAddEmb H))
  let bank := Fin.castAddEmb K (n := H+X)
  let hostBank := front.trans bank
  let owners := fan.trans hostBank
  let worker := (embProg hostBank Empty.elim divide).seq (Prog.seqList (idleCopies.map fun k => code (idleCopyIndex k)))
  let extra := Fin.castAddEmb 2 (n := H+X+K)
  let place := Exit.chart 0 (H+X+K+2)
  let blankSeed (t : ℕ) : Stacks t prime := ⟨[],[],fun _ => [],fun _ => []⟩
  let saved p := adjacentStageStacks (adjacentStageStacks (seed p) (blankSeed X)) (blankSeed K)
  let prepared p := flatStageSeed (adjacentStageStacks (saved p) (blankSeed 2))
  have blanks (t : ℕ) := LoadsPackedSeed.fixed nodeSeedWords CutoffNodeInput.cells (fun p =>
    Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) (Nat.mul_pos p.idlePositive (by decide))) (blankSeed t)
  obtain ⟨packed,pack⟩ := packedOwnerTraversal owners table worker
  refine ⟨_,fun f => embProg place id (embProg extra id (table f)),packed,(stageFan owners).trans place,returnedFan (stageFan owners),prepared,init,fixed,base,swaps,minimum,C,
    (((loader.join (blanks X)).join (blanks K)).join (blanks 2)).flatStage,nonneg,pos,?_⟩
  intro D enough p blocks positive rows align child fuel children branch
  apply pack
  · intro t away
    have h : ¬ ∃ k, place k = t := fun ⟨k,eq⟩ => away k eq
    let seed := adjacentStageStacks (saved p) (blankSeed 2)
    exact ⟨Function.extend_apply' seed.L (fun _ => []) _ h,Function.extend_apply' seed.R (fun _ => []) _ h⟩
  intro x u S live stock
  have seedAt t : (prepared p).L (place (extra t)) = (saved p).L t ∧
      (prepared p).R (place (extra t)) = (saved p).R t := by
    simp [prepared,flatStageSeed,place,extra,adjacentStageStacks,(Exit.chart 0 _).injective.extend_apply]
  have outside t (off : ∀ r, owners r ≠ t) := And.intro
    ((stock t off).1.trans (seedAt t).1) ((stock t off).2.trans (seedAt t).2)
  obtain ⟨v,E,m,exec,user,paid,ready,roles,kept⟩ := divideRun p (embDn hostBank u) (embStk hostBank S) (by
    intro t away
    have h := outside (hostBank t) (fun r => by
      change hostBank (fan r) ≠ hostBank t
      exact hostBank.injective.ne (away r))
    change S.L (hostBank t) = _ ∧ S.R (hostBank t) = _
    simpa only [saved,hostBank,front,bank,Function.Embedding.trans_apply,Fin.castAddEmb_apply,
      adjacentStageStacks,Fin.addCases_left,id_eq] using h)
  obtain ⟨a,G,lifted,_,same,view,off⟩ := exec_emb (body' := table) (ι := Empty.elim) hostBank.injective
    (fun f => nomatch f) exec u rfl S rfl
  rw [← view] at paid ready roles kept
  let price j := 2940*((prime^(p.w+1))^128*p.idleWidth)+branch j
  have traverse := traverseIdleRecords i table owners code price G a x
  obtain ⟨y,F,z,n,run,cost,last,out,action,frame⟩ := traverse (by
    intro r t
    have h := kept r
    change G.L (owners r) = S.L (owners r) ∧ G.R (owners r) = S.R (owners r) at h
    simp only [h.1,h.2]
    exact live r t) (by
    intro j k word v R input frame
    have slot : bank (raw j 24) = owners (idleTape i k) := by
      change hostBank (board j ((24 : Fin 72).castAdd 6)) = hostBank (fan (owner j))
      exact congrArg hostBank (payload j)
    rw [← slot] at input ⊢
    apply dispatch D leafRate permits fixed base swaps (large D enough) j p blocks positive rows align (children j) word v R input
    · intro h ne
      have eq := frame (hostBank (board j (h.castAdd 6))) (fun r => by
        change hostBank (fan r) ≠ hostBank (board j (h.castAdd 6))
        exact hostBank.injective.ne (rawOff j h ne r).symm)
      exact ⟨eq.1.trans (ready j h ne).1,eq.2.trans (ready j h ne).2⟩
    · intro t mem
      obtain ⟨l,_,rfl⟩ := List.mem_map.mp mem
      have away r := bank.injective.ne (suffixApart l r).symm
      have old := outside _ (fun r => away (fan r))
      have h := frame _ (fun r => away (fan r))
      have g := off _ away
      simpa [saved,bank,blankSeed,adjacentStageStacks] using
        And.intro (h.1.trans (g.1.trans old.1)) (h.2.trans (g.2.trans old.2))
    · intro h
      have eq := frame (hostBank (board j (h.natAdd 72))) (fun r => by
        change hostBank (fan r) ≠ hostBank (board j (h.natAdd 72))
        exact hostBank.injective.ne (fieldOff j h r).symm)
      exact eq.2.trans (roles j h)
    · intro t
      have away (r : Fin (H+X)) := (suffixApart t r).symm
      have old := outside _ (fun r => away (front (fan r)))
      have h := frame _ (fun r => away (front (fan r)))
      have g := off _ (fun r => away (front r))
      simpa [saved,blankSeed,adjacentStageStacks] using
        And.intro (h.1.trans (g.1.trans old.1)) (h.2.trans (g.2.trans old.2)))
  rw [show (∑ j, price j) = 735*p.cells+∑ j, branch j from dispatchIdleWindowBill p branch] at cost
  exact ⟨y,F,z,m+n,lifted.seq run,(CleanupBound.place hostBank off paid).seq cost,last.trans (same.trans user),out,action⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
