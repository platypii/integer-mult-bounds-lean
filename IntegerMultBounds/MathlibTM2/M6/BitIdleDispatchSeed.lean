module

public import IntegerMultBounds.MathlibTM2.M6.BitScheduledIdleInterval
public import IntegerMultBounds.MathlibTM2.M6.BitIdleChartHandoff

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)
open IntervalDescriptor RecursiveInterchangeLayout

/-- Place the cutoff comparison on ordinary registers 5 through 14. The
owner word on register 24 can change independently of all the private inputs. -/
theorem idleDispatchSeed (N : ℕ) :
    let bank := Fin.castAddEmb N (n := 72)
    ∃ cmp : Fin 10 ↪ Fin (72+N), ∀ w W L cutoff : ℕ,
    let M := prime^(w+1)
    ∃ seed : Stacks (72+N) prime, ∀ S : Stacks (72+N) prime,
      (∀ j, j ≠ bank 24 → S.L j = seed.L j ∧ S.R j = seed.R j) →
      S.R (bank 2) = binSyms M.size M ∧ S.R (bank 28) = binSyms 1 1 ∧
      S.R (bank 53) = binSyms W.size W ∧ (S.R (bank 71)).length = w+1 ∧
      (∀ i : Fin 72, 59 ≤ i.val → i.val ≤ 65 → S.R (bank i) = []) ∧ S.L (bank 59) = [] ∧
      (∀ i, S.L (bank (descriptorPorts i)) = [] ∧ S.R (bank (descriptorPorts i)) = []) ∧
      (∀ j : Fin N, S.L (j.natAdd 72) = [] ∧ S.R (j.natAdd 72) = []) ∧
      (S.R (cmp 0)).length = w ∧ S.R (cmp 1) = binSyms L cutoff ∧
      ∀ k : Fin 10, 2 ≤ k.val → S.R (cmp k) = [] := by
  intro bank
  let cmp := ((Fin.natAddEmb 5 (m := 10)).trans (Fin.castLEEmb (by decide : 15 ≤ 72))).trans bank
  refine ⟨cmp,?_⟩
  intro w W L cutoff M
  let contents (j : ℕ) : List (Fin (prime+4)) :=
    if j = 2 then binSyms M.size M else if j = 28 then binSyms 1 1 else
    if j = 53 then binSyms W.size W else if j = 71 then List.replicate (w+1) blank else
    if j = 5 then List.replicate w blank else if j = 6 then binSyms L cutoff else []
  refine ⟨⟨[],[],fun _ => [],fun j => contents j.val⟩,?_⟩
  intro S frame
  have get (j : Fin (72+N)) (ne : j.val ≠ 24) : S.L j = [] ∧ S.R j = contents j.val :=
    frame j (fun h => ne (congrArg Fin.val h))
  have atReg (j : Fin 72) (ne : j.val ≠ 24) : S.R (bank j) = contents j.val := (get _ ne).2
  have emptyAt (n : ℕ) (h : n ≠ 2 ∧ n ≠ 28 ∧ n ≠ 53 ∧ n ≠ 71 ∧ n ≠ 5 ∧ n ≠ 6) : contents n = [] := by
    simp [contents,h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2]
  refine ⟨(atReg 2 (by decide)).trans rfl,(atReg 28 (by decide)).trans rfl,(atReg 53 (by decide)).trans rfl,?_,?_,
    (get (bank 59) (by change 59 ≠ 24; decide)).1,?_,?_,?_,(get (cmp 1) (by change 6 ≠ 24; decide)).2.trans rfl,?_⟩
  · rw [atReg 71 (by decide)]
    exact List.length_replicate
  · intro j lo hi
    rw [atReg j (by omega)]
    simp [contents,show j.val ≠ 71 by omega,show j.val ≠ 53 by omega,show j.val ≠ 28 by omega,
      show j.val ≠ 2 by omega,show j.val ≠ 5 by omega,show j.val ≠ 6 by omega]
  · intro i
    have range : (bank (descriptorPorts i)).val = 33+i.val := rfl
    have pair := get (bank (descriptorPorts i)) (by rw [range]; omega)
    refine ⟨pair.1,pair.2.trans ?_⟩
    rw [range]
    apply emptyAt
    omega
  · intro j
    have pair := get (j.natAdd 72) (by change 72+j.val ≠ 24; omega)
    refine ⟨pair.1,pair.2.trans ?_⟩
    change contents (72+j.val) = []
    apply emptyAt
    omega
  · rw [(get (cmp 0) (by change 5 ≠ 24; decide)).2]
    exact List.length_replicate
  · intro k lower
    have idx : (cmp k).val = 5+k.val := rfl
    rw [(get _ (by rw [idx]; omega)).2,idx]
    apply emptyAt
    omega

/-- Run an aligned idle directory occurrence with its payload as the only shared tape. -/
theorem seededIdleDispatch [M8.Machine.Net] {Q : ℕ} {U : Type} (capacity : columnCapacity ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    ∃ (C : ℝ) (N : ℕ) (table : Unit → Pr Unit (72+N) Q prime U), 0 ≤ C ∧
    let bank := Fin.castAddEmb N (n := 72)
    ∀ {P : Type} (body : P → Pr P (72+N) Q prime U) (leafLabel : Unit → P),
    (∀ f, body (leafLabel f) = embProg (Function.Embedding.refl _) leafLabel (table f)) →
    ∀ (i : Fin 9) (j : Fin idleCopies.length) (recursiveLabel : P), ∃ code : Pr P (72+N) Q prime U,
    ∀ (root : Descriptor) (path : List (Fin nodeChildren5.length)) (depth b cutoff w groups : ℕ),
      0 < depth → 0 < b → root.width = 64^depth*b → 42^depth*b ≤ cutoff →
      let node := path.foldl (scheduledChild prime) root
      let a := w+1
      cutoff ≤ node.width →
      node.width = 64*a →
      node.rows = 142080*(142080*groups) →
      let W := node.beforeRows*groups*node.beforeH*node.between*node.afterD
      let e := idleInterval i idleCopies[j.val].2
      let lane := phaseIntervalChild (e.1+1) (e.2+1) a W 64
      let child := scheduledChild prime node (idleDirectoryIndex (i,j))
      0 < W → ∃ seed : Stacks (72+N) prime,
      ∀ (word : Fin ((prime^a)^128*(W*142080)) → ZMod 2) u S,
      S.L (bank 24) = [] → S.R (bank 24) = List.ofFn (fun k => SparseRoleCircuit.encode (word k)) →
      (∀ j, j ≠ bank 24 → S.L j = seed.L j ∧ S.R j = seed.R j) → ∀ recursiveBudget,
      (cutoff < child.width → IntervalWorkerExec body recursiveLabel lane a W recursiveBudget) →
      ∃ z F t changed, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧ RecordPayload (bank 24) (fun _ => blank) 0 changed F ∧
        parentIntervalRead i idleCopies[j.val].2 a (W*142080) word changed ∧
        ∀ js : List _, js.Nodup → t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+2*volume prime child + if cutoff < child.width then recursiveBudget
          else ⌊C*(child.width : ℝ)^M8.Machine.BudgetBound.tau*volume prime child⌋₊ := by
  obtain ⟨C,N,table,pos,dispatch⟩ := alignedIdleDispatch (U := U) capacity mergeCap
  obtain ⟨cmp,prepare⟩ := idleDispatchSeed N
  refine ⟨C,N,table,pos,?_⟩
  intro bank P body leaf installed i j recursiveLabel
  obtain ⟨code,run⟩ := dispatch body leaf installed i j cmp recursiveLabel
  refine ⟨code,?_⟩
  intro root path depth b cutoff w groups levels base alignment stop node a active width split W e lane child positive
  obtain ⟨_,_,_,call⟩ := run root path depth b cutoff w groups levels base alignment stop active width split positive
  obtain ⟨seed,ready⟩ := prepare w W root.width.size cutoff
  refine ⟨seed,?_⟩
  intro word u S left right fresh budget recurse
  obtain ⟨radix,unit,suffix,atom,scratch,tl,headers,unused,clock,stored,free⟩ := ready S fresh
  have payload : RecordPayload (bank 24) (fun _ => blank) 0 word S := by
    have encode (x : ZMod 2) : RadixToBinary.binaryEncoding.encode (SparseRoleCircuit.encode (a := 0) x) =
        SparseRoleCircuit.encode (a := prime) x := by fin_cases x <;> rfl
    intro z
    simpa only [left,right,sub_zero,payloadWord,M8.AtomBank.arrTape,List.map_ofFn,Function.comp_def,encode] using
      (payload_reads (SparseRoleCircuit.encode ∘ word) z).symm
  obtain ⟨z,F,t,exec,user,⟨y,out,reads,_⟩,paid⟩ := call word u S radix unit suffix atom scratch payload tl headers unused
    budget clock stored free recurse
  exact ⟨z,F,t,y,exec,user,out,reads,paid⟩

/-- Compile the remainder once. All its idle occurrences dispatch on their own
widths, sharing the same recursive procedure and stopped-leaf table. -/
theorem dispatchedRemainder [M8.Machine.Net] {Q : ℕ} {U : Type} (capacity : columnCapacity ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    ∃ (C : ℝ) (N : ℕ) (table : Unit → Pr Unit (72+N) Q prime U), 0 ≤ C ∧
    ∀ {P : Type} (body : P → Pr P (72+N) Q prime U) (leaf : Unit → P),
    (∀ f, body (leaf f) = embProg (Function.Embedding.refl _) leaf (table f)) →
    ∀ (i : Fin 9) (label : P), ∃ (H : ℕ) (R : Type) (host : R → Pr R H Q prime U) (code : Pr R H Q prime U)
      (src dst : Fin (142081+2) ↪ Fin H),
    ∀ (root : Descriptor) (path : List (Fin nodeChildren5.length)) (depth b cutoff w groups : ℕ),
      0 < depth → 0 < b → root.width = 64^depth*b → 42^depth*b ≤ cutoff →
      let node := path.foldl (scheduledChild prime) root
      let a := w+1
      cutoff ≤ node.width → node.width = 64*a → node.rows = 142080*(142080*groups) →
      let W := node.beforeRows*groups*node.beforeH*node.between*node.afterD
      let V := (prime^a)^128*(W*142080)
      0 < W → ∀ recursiveBudget : Fin nodeChildren5.length → ℕ,
      let child := scheduledChild prime node
      let budget := fun k => 2*volume prime (child k) + if cutoff < (child k).width then recursiveBudget k
        else ⌊C*((child k).width : ℝ)^M8.Machine.BudgetBound.tau*volume prime (child k)⌋₊
      (∀ j : Fin idleCopies.length, let k := idleDirectoryIndex (i,j)
        let e := idleInterval i idleCopies[j.val].2
        cutoff < (child k).width → IntervalWorkerExec body label (phaseIntervalChild (e.1+1) (e.2+1) a W 64) a W (recursiveBudget k)) →
      ∃ seed, PackedPieceHandoffWithCharge cleanupWeight V (fun x y => ∀ j : Fin (W*142080),
        let addr := fun z => flatWindowEquiv a (W*142080) (windowState a z,j)
        readRoles addr y = (Piece.remainder i.val).run (readRoles addr x))
        host code src dst seed ((∑ j : Fin idleCopies.length, budget (idleDirectoryIndex (i,j)))+1+(142081*(10*V+10)+1)) := by
  classical
  obtain ⟨C,N,table,nonneg,build⟩ := seededIdleDispatch (U := U) capacity mergeCap
  refine ⟨C,N,table,nonneg,?_⟩
  intro P body leaf installed i label
  let Job := (Fin 32 × Fin 5) × Fin 222
  have worker (k : Job) := build body leaf installed i (idleCopyIndex k) label
  let slot := (Fin.castAddEmb N (n := 72)) 24
  obtain ⟨H,host,code,src,dst,assemble⟩ := uniformRemainderWindow i (fun _ => 72+N) (fun _ => P)
    (fun _ => slot) (fun _ => body) (fun k => (worker k).choose)
  refine ⟨H,_,host,code,src,dst,?_⟩
  intro root path depth b cutoff w groups levels base alignment stop node a active width split W V positive recursiveBudget child budget recurse
  have ready (k : Job) := (worker k).choose_spec root path depth b cutoff w groups levels base alignment stop active width split positive
  apply assemble a (W*142080) (fun k => (ready k).choose) budget
  intro k word v D left right fresh
  obtain ⟨z,F,t,y,exec,user,record,reads,paid⟩ := (ready k).choose_spec word v D left right fresh
    (recursiveBudget (idleDirectoryIndex (i,idleCopyIndex k))) (recurse (idleCopyIndex k))
  exact ⟨z,F,t,y,exec,by simpa only [budget,child,node,Nat.add_assoc] using paid,user,record,by simpa only [idleCopyIndex_get] using reads⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
