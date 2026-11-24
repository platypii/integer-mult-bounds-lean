module

public import IntegerMultBounds.MathlibTM2.M6.BitNodeSeedWords

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout

private theorem loadArchiveFromWords {Config : Type} (node : Config → Descriptor) (w V : Config → ℕ)
    (words : Config → Fin 12 → List (Fin (prime+4)))
    (header : ∀ x (i : Fin 9), words x (i.succ.castAdd 2) = (parentArchiveSeed (node x) (w x)).R (parentArchivePorts i))
    (rate : ℕ) (limit : ∀ x, seedLoadBill (fun i => (parentArchiveSeed (node x) (w x)).R (parentArchivePorts i))+31 ≤ rate*V x) :
    LoadsPackedSeed words V (fun x => parentArchiveSeed (node x) (w x)) := by
  refine ⟨rate,?_⟩
  intro P U T Q body bank source apart
  let src := fun i : Fin 9 => source (i.succ.castAdd 2)
  have regs i : [src i,bank (parentArchivePorts i),bank 0,bank 1].Nodup := by
    have zero := (by decide : ∀ i, parentArchivePorts i ≠ 0) i
    have one := (by decide : ∀ i, parentArchivePorts i ≠ 1) i
    have ext j : src i ≠ bank j := (apart _ _).symm
    simp [List.nodup_cons,ext,bank.injective.eq_iff,zero,one]
  obtain ⟨code,load⟩ := loadParentArchiveSeed body bank src (bank 0) (bank 1) (fun i j => apart _ _) regs
  refine ⟨code,?_⟩
  intro x u S read fresh
  obtain ⟨v,F,n,run,user,paid,ready,frame⟩ := load (node x) (w x) u S
    (fun i => (read _).trans (header x i))
    fresh (fresh 0).2 (fresh 1).2
  refine ⟨v,F,n,run,user,?_,ready,frame⟩
  intro js nd
  exact (paid js nd).trans (Nat.add_le_add_left (limit x) _)

private theorem loadNodeArchive :
    LoadsPackedSeed nodeSeedWords CutoffNodeInput.cells (fun c => parentArchiveSeed c.node c.w) :=
  loadArchiveFromWords CutoffNodeInput.node CutoffNodeInput.w CutoffNodeInput.cells nodeSeedWords
    (fun c i => by simp only [nodeSeedWords,Fin.addCases_left,sweepSeedWords,Fin.cons_succ])
    (133*142080+65) archiveSeedLoadCost

/-- Keep one copy of the parent descriptor alongside the whole idle window.
Its six marked words can feed the row divider without recovering dimensions
from the lane's combined spectator width. -/
theorem idleWindowArchiveLoader {Job : Type} {H N : ℕ}
    (origin : Fin H → Option (Σ _ : Job, Fin (72+N)))
    (free : ∃ a b, a ≠ b ∧ origin a = none ∧ origin b = none) :
    LoadsPackedSeed nodeSeedWords CutoffNodeInput.cells (fun c =>
      adjacentStageStacks (idleWindowSeed origin (fun _ => idleDispatchStacks N c.w c.idleWidth c.root.width.size c.cutoff))
        (parentArchiveSeed c.node c.w)) :=
  (nodeIdleLoader id origin free).join loadNodeArchive

/-- Divide the inherited row count once on the shared archive. All six
canonical role words remain available to every scheduled idle occurrence. -/
theorem idleParentRoleHeaders {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin (80+273) ↪ Fin T)
    (capacity : (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q) :
    let dst := ((Fin.natAddEmb 38 (m := 6)).trans (Fin.castAddEmb 36)).trans (Fin.castAddEmb 273)
    ∃ (code : Pr P T Q prime U) (rate : ℕ), ∀ (c : CutoffNodeInput) u (S : Stacks T prime),
      ParentArchiveInput c.node c.w (embStk bank S) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (rate*c.cells) ∧
        (∀ i, F.R (bank (dst i)) = (Routines.hdr (role c.node 142080) i).map bitSymbol) ∧
        ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro dst
  let slots := (Fin.castAddEmb 42 (n := 38)).trans (Fin.castAddEmb 273)
  let tmp : Fin (80+273) := (44 : Fin 80).castAdd 273
  let run := loadRoleHeaders_exec (U := U) (P := Empty) Empty.elim slots dst tmp
    (by decide) (by decide) (by decide) capacity
  let machine := RecursiveRowsNodeHeaders.program (q := prime) 142080
  let src := fun i : Fin 6 => slots (⟨3+i.val,by omega⟩ : Fin 38)
  let localCode : Pr Empty (80+273) Q prime U := .seq
    (statePlacedNormalized slots capacity (Nat.zero_lt_of_lt machine.start.isLt) Empty.elim (foreign machine))
    (loadDimensions src dst tmp (List.finRange 6))
  obtain ⟨price,charge⟩ := placedClosedWorkerCost (P := P) bank localCode true
  let K := (RecursiveRowsQuotient.constant 142080+30)*142080*43+152
  refine ⟨embProg bank Empty.elim localCode,price*K,?_⟩
  intro c u S ready
  let v := {c.node with rows := c.rowsPerStage}
  have eq : role c.node 142080 = v := by
    unfold role v
    rw [c.rows,Nat.mul_div_cancel_left _ (by decide)]
    rfl
  have mass : volume prime v = c.cells := by
    apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 142080)
    rw [← eq,c.cells_share,role_volume_mul prime 142080 c.node ⟨_,c.rows⟩]
  have rowBound : c.rowsPerStage ≤ c.cells := by
    have h := (RecursiveRowsDimensions.products_le Shared50ModularControl.prime_prime.two_le 1 v c.stagePositive).2.2
    simp only [Nat.div_one,mass] at h
    exact (Nat.le_mul_of_pos_left v.rows c.stagePositive.1).trans h
  have positive : 0 < c.cells := c.stagePositive.2.1.trans_le rowBound
  obtain ⟨a,D,n,user,exec,time,fields,_⟩ := run c.node c.rowsPerStage c.rows c.stagePositive.2.1
    (embDn bank u) (embStk bank S) ready.1 ready.2.1 ready.2.2.1 ready.2.2.2.1
  obtain ⟨z,F,placed,_,same,view,off⟩ := exec_emb bank.injective
    (ι := Empty.elim) (body' := body) (fun f => nomatch f) exec u rfl S rfl
  have sum (js : List (Fin 6)) :
      (js.map (fun i => 8*(Routines.hdr v i).length+8)).sum ≤ js.length*(24*c.cells) := by
    induction js with
    | nil => simp
    | cons i js ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      rw [Nat.succ_mul js.length]
      have limit := RecursiveRowsNode.header_length v c.stagePositive _ (Routines.hdr_headers v) i
      rw [mass] at limit
      omega
  have copies := sum (List.finRange 6)
  rw [List.length_finRange] at copies
  have time' : n ≤ K*c.cells := by
    let C := RecursiveRowsQuotient.constant 142080+30
    have cost := Nat.mul_le_mul_left (C*142080*43) rowBound
    rw [c.rows] at time
    change n ≤ C*(142080*c.rowsPerStage)*43+((List.finRange 6).map (fun i => 8*(Routines.hdr v i).length+8)).sum+8 at time
    rw [show C*(142080*c.rowsPerStage)*43 = C*142080*43*c.rowsPerStage by ring] at time
    change n ≤ (C*142080*43+152)*c.cells
    rw [Nat.add_mul]
    omega
  refine ⟨z,_,_,placed,same.trans user,?_,?_,off⟩
  · intro js nd
    exact (charge body _ _ _ _ _ placed js nd).trans
      (Nat.add_le_add_left (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left price time') _)
  · intro i
    rw [eq]
    exact (congrArg (fun B : Stacks (80+273) prime => B.R (dst i)) view).trans (fields i)

/-- Initialize the window and its shared role directory from the node's twelve
master words, leaving every occurrence's ordinary dispatch seed intact. -/
theorem prepareIdleWindowRoles {Job P U : Type} {H N T Q : ℕ}
    (origin : Fin H → Option (Σ _ : Job, Fin (72+N)))
    (free : ∃ a b, a ≠ b ∧ origin a = none ∧ origin b = none)
    (body : P → Pr P T Q prime U) (bank : Fin (H+(80+273)) ↪ Fin T) (master : Fin 12 → Fin T)
    (apart : ∀ i j, bank i ≠ master j)
    (capacity : (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q) :
    let window := (Fin.castAddEmb (80+273)).trans bank
    let archive := (Fin.natAddEmb H).trans bank
    let dst := ((Fin.natAddEmb 38 (m := 6)).trans (Fin.castAddEmb 36)).trans (Fin.castAddEmb 273)
    ∃ (code : Pr P T Q prime U) (rate : ℕ), ∀ (c : CutoffNodeInput) u (S : Stacks T prime),
      (∀ i, S.R (master i) = nodeSeedWords c i) →
      (∀ i, S.L (bank i) = [] ∧ S.R (bank i) = []) →
      let seed := idleWindowSeed origin (fun _ => idleDispatchStacks N c.w c.idleWidth c.root.width.size c.cutoff)
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧ CleanupBound S F t (rate*c.cells) ∧
        (∀ j, F.L (window j) = seed.L j ∧ F.R (window j) = seed.R j) ∧
        (∀ i, F.R (archive (dst i)) = (Routines.hdr (role c.node 142080) i).map bitSymbol) ∧
        ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro window archive dst
  obtain ⟨a,install⟩ := idleWindowArchiveLoader origin free
  obtain ⟨load,start⟩ := install body bank master apart
  obtain ⟨divide,b,finish⟩ := idleParentRoleHeaders body archive capacity
  refine ⟨load.seq divide,a+b,?_⟩
  intro c u S words vacant seed
  obtain ⟨v,D,n,exec,user,paid,ready,frame⟩ := start c u S words vacant
  have left : (embStk archive D).L = (parentArchiveSeed c.node c.w).L := by
    funext k
    change D.L (bank (k.natAdd H)) = _
    simpa only [adjacentStageStacks,Fin.addCases_right,id_eq] using (ready (k.natAdd H)).1
  have right : (embStk archive D).R = (parentArchiveSeed c.node c.w).R := by
    funext k
    change D.R (bank (k.natAdd H)) = _
    simpa only [adjacentStageStacks,Fin.addCases_right,id_eq] using (ready (k.natAdd H)).2
  have installed : ParentArchiveInput c.node c.w (embStk archive D) := by
    have transfer {A B : Stacks (80+273) prime} (hl : A.L = B.L) (hr : A.R = B.R)
        (h : ParentArchiveInput c.node c.w B) : ParentArchiveInput c.node c.w A := by
      simpa only [ParentArchiveInput,embStk,hl,hr] using h
    exact transfer left right (parentArchiveSeed_ready c.node c.w)
  obtain ⟨z,F,m,ran,same,bill,fields,off⟩ := finish c v D installed
  refine ⟨z,F,_,exec.seq ran,same.trans user,?_,?_,fields,?_⟩
  · rw [Nat.add_mul]
    exact paid.seq bill
  · intro k
    have h := off (window k) (fun i => bank.injective.ne (by
      intro eq
      have bad := congrArg Fin.val eq
      change H+i.val = k.val at bad
      omega))
    exact ⟨h.1.trans (by simpa only [window,seed,adjacentStageStacks,Fin.addCases_left,id_eq,Function.Embedding.trans_apply,Fin.castAddEmb_apply] using (ready (k.castAdd _)).1),
      h.2.trans (by simpa only [window,seed,adjacentStageStacks,Fin.addCases_left,id_eq,Function.Embedding.trans_apply,Fin.castAddEmb_apply] using (ready (k.castAdd _)).2)⟩
  · intro j away
    have h := off j (fun k => away _)
    exact ⟨h.1.trans (frame j away).1,h.2.trans (frame j away).2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
