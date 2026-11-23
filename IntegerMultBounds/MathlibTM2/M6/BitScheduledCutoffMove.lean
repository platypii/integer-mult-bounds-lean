module

public import IntegerMultBounds.MathlibTM2.M6.BitPackedMoveTranspose
public import IntegerMultBounds.MathlibTM2.M6.BitActiveSweep
public import IntegerMultBounds.MathlibTM2.M6.BitCutoffRecurrence

/-! Fit the fixed-bank MOVE wrapper into the active child's local reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open RecursiveInterchangeLayout (Descriptor volume)
open Shared50ModularControl (prime)

private theorem recordHeaderCost (w W : ℕ) (record : List (Fin (prime+4))) (positive : 0 < W)
    (fits : record.length ≤ (prime^(w+1))^16*W) :
    seedLoadBill ![binSyms (prime^(w+1)).size (prime^(w+1)),binSyms 1 1,binSyms W.size W,record] ≤
      57*((prime^(w+1))^16*W) := by
  let M := prime^(w+1)
  have radix := (Nat.le_self_pow (by decide : 16 ≠ 0) M).trans (Nat.le_mul_of_pos_right _ positive)
  have width : W ≤ M^16*W := Nat.le_mul_of_pos_left _ (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
  have bits (n : ℕ) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have h := (bits M).trans radix
  have k := (bits W).trans width
  dsimp only [M] at *
  simp [seedLoadBill,Fin.sum_univ_succ,length_binSyms]
  omega

/-- Copy the four serialized header words from the live record before running a
local worker. The clock can be read separately from the caller's unary tape. -/
theorem recordHeaderReturn {P U : Type} {B T Q n : ℕ} [NeZero B]
    (ports : Fin (n+35) ↪ Fin T) (room : B+3 ≤ n) (slots : Fin 4 ↪ Fin B)
    (tmp saved : Fin B) (spare : ∀ i, slots i ≠ 0)
    (ht : tmp ≠ 0) (hs : saved ≠ 0) (apart : ∀ i, [slots i,tmp,saved].Nodup) :
    ∃ (bank : Fin B ↪ Fin T) (wrap : (P → Pr P B Q prime U) → Pr P B Q prime U → Pr P T Q prime U),
    ∀ {w W m : ℕ} (node child : Descriptor) (record : List (Fin (prime+4)))
      (position : Fin (volume prime child) ≃ Fin ((prime^(w+1))^16*W))
      (span : m*142080 = (prime^(w+1))^16*W) (body : P → Pr P B Q prime U)
      (worker : Pr P B Q prime U) (price : ℕ) (charged : Bool),
      let V := (prime^(w+1))^16*W
      let header : Fin 4 → List (Fin (prime+4)) :=
        ![binSyms (prime^(w+1)).size (prime^(w+1)),binSyms 1 1,binSyms W.size W,record]
      (∀ (x : Fin V → ZMod 2) v D,
        D.R 0 = List.ofFn (fun k : Fin (m*142080) => SparseRoleCircuit.encode (x (k.cast span))) →
        (∀ j, D.L j = []) → (∀ i, D.R (slots i) = header i) →
        (∀ j, j ≠ 0 → (∀ i, slots i ≠ j) → D.R j = []) →
        ∃ z F t y, Exec body worker (mk v D) t (mk z F) ∧ z.user = v.user ∧
          (∀ k, y (position k) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x ∘ position) k) ∧
          RecordPayload 0 (fun _ => blank) 0 y F ∧
          t+tapeCharge cleanupWeight (List.finRange B) F ≤ tapeCharge cleanupWeight (List.finRange B) D+price) →
      MoveOnBankExec node child w W ports record position (fun f => embProg bank id (body f))
        (wrap body worker) (seedLoadBill header+price+30*V+4*B+33) charged := by
  classical
  obtain ⟨bank,finish,separate,restore⟩ := activeHostReturn (B := B) (P := P) (U := U) (Q := Q) ports room
  let src : Fin 4 → Fin T := fun i => scheduledRecordPorts ports (![2,28,27,34] i)
  let host := fun (body : P → Pr P B Q prime U) f => embProg bank id (body f)
  have regs i : [src i,bank (slots i),bank tmp,bank saved].Nodup := by
    have h := apart i
    simpa [src,List.nodup_cons,bank.injective.eq_iff,Ne.symm (separate _ _)] using h
  choose load prepare using fun body => installChildSeed (host body) bank slots src (bank tmp) (bank saved)
    (fun i j => separate _ _) regs
  refine ⟨bank,fun body worker => finish ((load body).seq (embProg bank id worker)),?_⟩
  intro w W m node child record position span body worker price charged V header execute
  apply restore node child record position span (host body) _ (seedLoadBill header+price) charged
  intro x v D ready word left right
  let seed : Stacks B prime := ⟨[],[],fun _ => [],Function.extend slots header (fun _ => [])⟩
  have atSlot i : seed.R (slots i) = header i := slots.injective.extend_apply header (fun _ => []) i
  have masters i : D.R (src i) = seed.R (slots i) := by
    rw [atSlot]
    fin_cases i
    · exact ready.modulus
    · exact ready.one
    · exact ready.width
    · exact ready.archive
  obtain ⟨u,R,a,init,user,paid,filled,off⟩ := prepare body seed v D masters
    (fun i => right _ (spare i)) (right _ ht) (right _ hs)
  let E := {D with R := R}
  have keep j (away : ∀ i, slots i ≠ j) := off (bank j) (fun i => bank.injective.ne (away i))
  obtain ⟨q,G,b,y,run,same,effect,out,bill⟩ := execute x (embDn bank u) (embStk bank E)
    ((keep 0 spare).trans word) left (fun i => (filled _ (fun away => False.elim (away i rfl))).trans (atSlot i))
    (fun j ne away => (keep j away).trans (right j ne))
  obtain ⟨z,F,exec,_,last,view,frame⟩ := exec_emb (ι := id) (body' := host body) bank.injective
    (fun _ => rfl) run u rfl E rfl
  rw [← view] at out bill
  let js := (List.finRange B).map bank
  have loadCost := paid js ((List.nodup_finRange _).map bank.injective)
  simp only [atSlot] at loadCost
  have weight (A : Stacks T prime) : tapeCharge cleanupWeight (List.finRange B) (embStk bank A) =
      tapeCharge cleanupWeight js A := by simp [js,tapeCharge,embStk,List.map_map,Function.comp_def]
  rw [weight,weight] at bill
  refine ⟨z,F,_,y,init.seq exec,last.trans (same.trans user),effect,out,?_,?_⟩
  · change a+tapeCharge cleanupWeight js E ≤ tapeCharge cleanupWeight js D+seedLoadBill header at loadCost
    change _+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js D+_
    omega
  · intro j away
    exact ⟨(frame j away).1,((frame j away).2).trans (off j (fun i => away _))⟩

private theorem cutoffMoveReserve [M8.Machine.Net] (c : CutoffNodeInput) (D rate entryRate : ℝ)
    (k : ℕ) (short : c.path.length < c.depth) (active : c.cutoff < c.node.width)
    (enough : (k : ℝ) ≤ entryRate) (localRate : entryRate ≤ D) :
    let child := c.node
    let scale := (volume prime child : ℝ)*(child.width : ℝ)^M8.Machine.BudgetBound.tau
    let budget := cutoffTreeBudget D rate c.cutoff (c.depth-c.path.length) child
    k*volume prime child ≤ ⌊entryRate*scale⌋₊ ∧ ⌊entryRate*scale⌋₊ ≤ budget := by
  intro child scale budget
  have positive : 1 ≤ child.width := by
    change 1 ≤ c.node.width
    rw [c.width]
    omega
  have power : 1 ≤ (child.width : ℝ)^M8.Machine.BudgetBound.tau :=
    Real.one_le_rpow (by exact_mod_cast positive) M8.Machine.BudgetBound.exponent_range.1.le
  have mass : (volume prime child : ℝ) ≤ scale := le_mul_of_one_le_right (by positivity) power
  have wrapper : k*volume prime child ≤ ⌊entryRate*scale⌋₊ := by
    apply Nat.le_floor
    push_cast
    exact mul_le_mul enough mass (by positivity) (by linarith)
  have fits : ⌊entryRate*scale⌋₊ ≤ budget := by
    dsimp only [budget]
    rw [show c.depth-c.path.length = (c.depth-c.path.length-1)+1 by omega,cutoffTreeBudget,ite_eq_left active]
    exact (Nat.floor_mono (mul_le_mul_of_nonneg_right localRate ((by positivity : (0 : ℝ) ≤ volume prime child).trans mass))).trans (Nat.le_add_right ..)
  exact ⟨wrapper,fits⟩

theorem scheduledCutoffMove [M8.Machine.Net] {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U) (entry : P)
    (bank : Fin (intervalSplitTapes+1) ↪ Fin T) (tmp buf : Fin T)
    (tmpOff : ∀ i, bank i ≠ tmp) (bufOff : ∀ i, bank i ≠ buf) (distinct : tmp ≠ buf)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let fan := (withHelperPort (intervalOwners 142080)).trans bank
    ∀ dst : Fin (142081+2) ↪ Fin T,
    (∀ j i, bank (moveReturnPorts j) ≠ childReturnFan dst i) →
    ∃ code : Pr P T Q prime U, ∀ (c : CutoffNodeInput) seed (D rate entryRate : ℝ),
      let child := c.node
      let atom := c.w+1
      let width : child.width = 64*atom := c.width
      let groups : 142080 ∣ child.rows := ⟨_,c.rows⟩
      let W := CopyChildLayout.spectators child / 142080
      let lane := packedDescriptor (64*atom) W
      let m := volume prime lane
      let wide := packedDescriptor (64*atom) (W*142080)
      let size : m*142080 = volume prime wide := by simp [m,lane,wide,volume,packedDescriptor,Nat.mul_assoc]
      let layout := CopyChildLayout.changeLayout wide child width.symm (scheduledMoveSpectators child atom groups)
      let position := (CopyChildLayout.flatAddress wide).symm.trans (layout.trans (CopyChildLayout.flatAddress child))
      let budget := cutoffTreeBudget D rate c.cutoff (c.depth-c.path.length) child
      let scale := (volume prime child : ℝ)*(child.width : ℝ)^M8.Machine.BudgetBound.tau
      c.path.length < c.depth → c.cutoff < child.width → 214000000 ≤ entryRate → entryRate ≤ D →
      PackedPieceHandoffWithCharge cleanupWeight c.cells (packedChildOutput atom c.cells) body (body entry) fan dst seed (budget-⌊entryRate*scale⌋₊) →
      ∀ (x : Fin (volume prime child) → ZMod 2) u (S : Stacks T prime),
      S.R (bank (Fin.succ 0)) = List.ofFn (fun i => SparseRoleCircuit.encode (x (position (i.cast size)))) →
      (∀ i, S.L (bank i) = []) → (∀ i, i ≠ Fin.succ 0 → S.R (bank i) = []) →
      S.L tmp = [] → S.R tmp = [] → S.R buf = [] →
      (∀ j, (∀ i, fan i ≠ bank j) → seed.L (bank j) = [] ∧ seed.R (bank j) = []) →
      (∀ j, (∀ i, bank i ≠ j) → S.L j = seed.L j ∧ S.R j = seed.R j) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        RecordPayload (bank (Fin.succ 0)) (fun _ => blank) 0
          ((Shared50RecursiveNodeRows.transpose (one_dvd child.rows) x) ∘ position) F ∧
        t ≤ budget := by
  intro fan dst disjoint
  obtain ⟨code,run⟩ := scheduledPackedMove body entry bank tmp buf tmpOff bufOff distinct capacity dst disjoint
  refine ⟨code,?_⟩
  intro c seed D rate entryRate child atom width groups W lane m wide size layout position budget scale short active enough localRate worker x u S source left empty tl tr br localSeed outerSeed
  have volumeEq := Fintype.card_congr position
  simp only [Fintype.card_fin] at volumeEq
  have cells : c.cells = m := Nat.eq_of_mul_eq_mul_right (by decide : 0 < 142080)
    (c.cells_share.trans (size.trans volumeEq).symm)
  have pos : 0 < c.cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
    (Nat.mul_pos c.idlePositive (by decide))
  rw [cells] at worker pos
  obtain ⟨z,F,t,exec,user,out,bill⟩ := run child atom _ seed width groups worker pos x u S source left empty tl tr br localSeed outerSeed
  refine ⟨z,F,t,exec,user,out,?_⟩
  obtain ⟨wrapper,fits⟩ := cutoffMoveReserve c D rate entryRate 214000000 short active enough localRate
  change 214000000*volume prime child ≤ ⌊entryRate*scale⌋₊ at wrapper
  change ⌊entryRate*scale⌋₊ ≤ budget at fits
  omega

/-- Account for the returned workspace within the active cutoff reserve. -/
theorem chargedCutoffMove [M8.Machine.Net] {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U) (entry : P)
    (bank : Fin (intervalSplitTapes+1) ↪ Fin T) (tmp buf : Fin T)
    (tmpOff : ∀ i, bank i ≠ tmp) (bufOff : ∀ i, bank i ≠ buf) (distinct : tmp ≠ buf)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let fan := (withHelperPort (intervalOwners 142080)).trans bank
    ∀ dst : Fin (142081+2) ↪ Fin T,
    (∀ j i, bank (moveReturnPorts j) ≠ childReturnFan dst i) →
    ∃ code : Pr P T Q prime U, ∀ (c : CutoffNodeInput) seed (D rate entryRate : ℝ),
      let child := c.node
      let atom := c.w+1
      let width : child.width = 64*atom := c.width
      let groups : 142080 ∣ child.rows := ⟨_,c.rows⟩
      let W := CopyChildLayout.spectators child / 142080
      let lane := packedDescriptor (64*atom) W
      let m := volume prime lane
      let wide := packedDescriptor (64*atom) (W*142080)
      let size : m*142080 = volume prime wide := by simp [m,lane,wide,volume,packedDescriptor,Nat.mul_assoc]
      let layout := CopyChildLayout.changeLayout wide child width.symm (scheduledMoveSpectators child atom groups)
      let position := (CopyChildLayout.flatAddress wide).symm.trans (layout.trans (CopyChildLayout.flatAddress child))
      let budget := cutoffTreeBudget D rate c.cutoff (c.depth-c.path.length) child
      let scale := (volume prime child : ℝ)*(child.width : ℝ)^M8.Machine.BudgetBound.tau
      c.path.length < c.depth → c.cutoff < child.width → 1000000000 ≤ entryRate → entryRate ≤ D →
      PackedPieceHandoffWithCharge cleanupWeight c.cells (packedChildOutput atom c.cells) body (body entry) fan dst seed (budget-⌊entryRate*scale⌋₊) →
      ∀ (x : Fin (volume prime child) → ZMod 2) u (S : Stacks T prime),
      S.R (bank (Fin.succ 0)) = List.ofFn (fun i => SparseRoleCircuit.encode (x (position (i.cast size)))) →
      (∀ i, S.L (bank i) = []) → (∀ i, i ≠ Fin.succ 0 → S.R (bank i) = []) →
      S.L tmp = [] → S.R tmp = [] → S.R buf = [] →
      (∀ j, (∀ i, fan i ≠ bank j) → seed.L (bank j) = [] ∧ seed.R (bank j) = []) →
      (∀ j, (∀ i, bank i ≠ j) → S.L j = seed.L j ∧ S.R j = seed.R j) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        RecordPayload (bank (Fin.succ 0)) (fun _ => blank) 0
          ((Shared50RecursiveNodeRows.transpose (one_dvd child.rows) x) ∘ position) F ∧
        ∀ js, js.Nodup → (∀ i, bank (moveReturnPorts i) ∈ js) →
          t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
            min budget (budget-⌊entryRate*scale⌋₊+1000000000*volume prime child) := by
  intro fan dst disjoint
  obtain ⟨code,run⟩ := chargedPackedMoveTranspose body entry bank tmp buf tmpOff bufOff distinct capacity dst disjoint
  refine ⟨code,?_⟩
  intro c seed D rate entryRate child atom width groups W lane m wide size layout position budget scale short active enough localRate worker x u S source left empty tl tr br localSeed outerSeed
  have volumeEq := Fintype.card_congr position
  simp only [Fintype.card_fin] at volumeEq
  have cells : c.cells = m := Nat.eq_of_mul_eq_mul_right (by decide : 0 < 142080)
    (c.cells_share.trans (size.trans volumeEq).symm)
  have pos : 0 < c.cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
    (Nat.mul_pos c.idlePositive (by decide))
  rw [cells] at worker pos
  obtain ⟨z,F,t,exec,user,out,bill⟩ := run atom W _ seed worker pos (x ∘ position) u S
    source left empty tl tr br localSeed outerSeed
  have physical : Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) (x ∘ position) =
      Shared50RecursiveNodeRows.transpose (one_dvd child.rows) x ∘ position :=
    funext (transpose_changeLayout wide child width.symm (scheduledMoveSpectators child atom groups) x)
  refine ⟨z,F,t,exec,user,?_,?_⟩
  · rw [← physical]
    exact out
  intro js unique savedIn
  have charged := bill js unique savedIn
  change t+tapeCharge cleanupWeight js F ≤ _+tapeCharge cleanupWeight js S+1000000000*volume prime wide at charged
  rw [volumeEq] at charged
  obtain ⟨wrapper,fits⟩ := cutoffMoveReserve c D rate entryRate 1000000000 short active enough localRate
  change 1000000000*volume prime child ≤ ⌊entryRate*scale⌋₊ at wrapper
  change ⌊entryRate*scale⌋₊ ≤ budget at fits
  omega

/-- Return a cutoff transpose to the scheduled record and clear its borrowed bank. -/
theorem cutoffMoveRecord [M8.Machine.Net] {P U : Type} {B T Q n : ℕ} [NeZero B]
    (body : P → Pr P B Q prime U) (entry : P)
    (bank : Fin (intervalSplitTapes+1) ↪ Fin B) (tmp buf : Fin B)
    (tmpOff : ∀ i, bank i ≠ tmp) (bufOff : ∀ i, bank i ≠ buf) (distinct : tmp ≠ buf)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (dst : Fin (142081+2) ↪ Fin B) (apart : ∀ j i, bank (moveReturnPorts j) ≠ childReturnFan dst i)
    (ports : Fin (n+35) ↪ Fin T) (room : B+3 ≤ n) :
    ∃ (workspace : Fin B ↪ Fin T) (code : Pr P T Q prime U),
    ∀ (charged : Bool) {w W : ℕ} (parent : Descriptor) (record : List (Fin (prime+4))) (c : CutoffNodeInput),
    let child := c.node
    let atom := c.w+1
    let groups : 142080 ∣ child.rows := ⟨_,c.rows⟩
    let spectators := CopyChildLayout.spectators child / 142080
    let wide := packedDescriptor (64*atom) (spectators*142080)
    let layout := CopyChildLayout.changeLayout wide child c.width.symm (scheduledMoveSpectators child atom groups)
    let logical := (CopyChildLayout.flatAddress wide).symm.trans (layout.trans (CopyChildLayout.flatAddress child))
    ∀ (size : volume prime wide = (prime^(w+1))^16*W),
    let position := logical.symm.trans (finCongr size)
    ∀ seed (D rate entryRate : ℝ),
      let fan := (withHelperPort (intervalOwners 142080)).trans bank
      let budget := cutoffTreeBudget D rate c.cutoff (c.depth-c.path.length) child
      let scale := (volume prime child : ℝ)*(child.width : ℝ)^M8.Machine.BudgetBound.tau
      c.path.length < c.depth → c.cutoff < child.width → ((1000000063+4*B : ℕ) : ℝ) ≤ entryRate → entryRate ≤ D →
      (∀ j, (∀ i, fan i ≠ j) → seed.L j = [] ∧ seed.R j = []) →
      PackedPieceHandoffWithCharge cleanupWeight c.cells (packedChildOutput atom c.cells)
        body (body entry) fan dst seed (budget-⌊entryRate*scale⌋₊) →
      MoveOnBankExec parent child w W ports record position (fun f => embProg workspace id (body f)) code
        budget charged := by
  obtain ⟨workspace,wrap,restore⟩ := activeBankReturn (P := P) (U := U) (Q := Q)
    ports room (bank (Fin.succ 0))
  obtain ⟨move,run⟩ := chargedCutoffMove body entry bank tmp buf tmpOff bufOff distinct capacity dst apart
  refine ⟨workspace,wrap move,?_⟩
  intro charged w W parent record c child atom groups spectators wide layout logical size position
  let lane := packedDescriptor (64*atom) spectators
  have split : volume prime lane*142080 = volume prime wide := by
    simp [lane,wide,packedDescriptor,volume,Nat.mul_assoc]
  intro seed D rate entryRate fan budget scale short active enough localRate clean worker
  let runtime := budget-⌊entryRate*scale⌋₊+1000000000*volume prime child
  have volumeEq := Fintype.card_congr position
  simp only [Fintype.card_fin] at volumeEq
  have positive : 0 < volume prime child := by
    rw [← c.cells_share]
    have := c.idlePositive
    have := Shared50ModularControl.prime_prime.pos
    unfold CutoffNodeInput.cells
    positivity
  have space := Nat.le_mul_of_pos_right (4*B+33) positive
  obtain ⟨reserve,fits⟩ := cutoffMoveReserve c D rate entryRate (1000000063+4*B) short active enough localRate
  change (1000000063+4*B)*volume prime child ≤ ⌊entryRate*scale⌋₊ at reserve
  change ⌊entryRate*scale⌋₊ ≤ budget at fits
  have total : runtime+30*((prime^(w+1))^16*W)+4*B+33 ≤ budget := by
    rw [← volumeEq]
    dsimp only [runtime]
    rw [Nat.add_mul] at space reserve
    omega
  suffices runRecord : MoveOnBankExec parent child w W ports record position
      (fun f => embProg workspace id (body f)) (wrap move)
      (runtime+30*((prime^(w+1))^16*W)+4*B+33) charged by
    intro smaller _ _ _ u S word ready cleanBank
    obtain ⟨z,F,t,y,exec,paid,rest⟩ := runRecord smaller u S word ready cleanBank
    exact ⟨z,F,t,y,exec,paid.weaken total,rest⟩
  apply restore parent child record position (split.trans size) body move runtime charged
  intro x u S source left right
  obtain ⟨z,F,t,exec,user,out,bill⟩ := run c seed D rate entryRate short active (by push_cast at enough; linarith) localRate
    worker (x ∘ position) u S (by
      change S.R (bank (Fin.succ 0)) = List.ofFn (fun k : Fin (volume prime lane*142080) =>
        SparseRoleCircuit.encode (x (position (logical (k.cast split)))))
      simpa only [position,Equiv.trans_apply,Equiv.symm_apply_apply,finCongr_apply,Fin.cast_cast] using source)
    (fun i => left _) (fun i h => right _ (bank.injective.ne h)) (left _)
    (right _ (tmpOff _).symm) (right _ (bufOff _).symm)
    (fun j away => clean _ away) (by
      intro j away
      have h := clean j (fun i => away _)
      exact ⟨(left j).trans h.1.symm,(right j (away _).symm).trans h.2.symm⟩)
  change RecordPayload (bank (Fin.succ 0)) (fun _ => blank) 0
    (Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x ∘ position) ∘ logical) F at out
  let y := Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x ∘ position) ∘ position.symm
  refine ⟨z,F,t,y,exec,user,?_,?_,(bill _ (List.nodup_finRange _) (fun i => List.mem_finRange _)).trans
    (Nat.add_le_add_left (Nat.min_le_right budget runtime) _)⟩
  · intro k
    simp [y]
  · apply castPayload size
    simpa [y,position,Function.comp_def] using out

/-- Initialize the child from four live record headers and pay for their copies in the cutoff reserve. -/
theorem seededCutoffMoveRecord [M8.Machine.Net] {P U : Type} {B T Q n : ℕ} [NeZero B]
    (body : P → Pr P B Q prime U) (entry : P)
    (bank : Fin (intervalSplitTapes+1) ↪ Fin B) (tmp buf : Fin B)
    (tmpOff : ∀ i, bank i ≠ tmp) (bufOff : ∀ i, bank i ≠ buf) (distinct : tmp ≠ buf)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (dst : Fin (142081+2) ↪ Fin B) (apart : ∀ j i, bank (moveReturnPorts j) ≠ childReturnFan dst i)
    (ports : Fin (n+35) ↪ Fin T) (room : B+3 ≤ n)
    (owner : bank (Fin.succ 0) = 0) (headers : Fin 4 ↪ Fin B)
    (outside : ∀ i j, headers i ≠ bank j) (work : ∀ i, [headers i,tmp,buf].Nodup) :
    ∃ (workspace : Fin B ↪ Fin T) (code : Pr P T Q prime U),
    ∀ (charged : Bool) {w W : ℕ} (parent : Descriptor) (record : List (Fin (prime+4))) (c : CutoffNodeInput),
    let child := c.node
    let atom := c.w+1
    let groups : 142080 ∣ child.rows := ⟨_,c.rows⟩
    let spectators := CopyChildLayout.spectators child / 142080
    let wide := packedDescriptor (64*atom) (spectators*142080)
    let layout := CopyChildLayout.changeLayout wide child c.width.symm (scheduledMoveSpectators child atom groups)
    let logical := (CopyChildLayout.flatAddress wide).symm.trans (layout.trans (CopyChildLayout.flatAddress child))
    ∀ (size : volume prime wide = (prime^(w+1))^16*W),
    let position := logical.symm.trans (finCongr size)
    ∀ seed (D rate entryRate : ℝ),
      let fan := (withHelperPort (intervalOwners 142080)).trans bank
      let budget := cutoffTreeBudget D rate c.cutoff (c.depth-c.path.length) child
      let scale := (volume prime child : ℝ)*(child.width : ℝ)^M8.Machine.BudgetBound.tau
      c.path.length < c.depth → c.cutoff < child.width → ((1000000120+4*B : ℕ) : ℝ) ≤ entryRate → entryRate ≤ D →
      record.length ≤ (prime^(w+1))^16*W →
      let header : Fin 4 → List (Fin (prime+4)) :=
        ![binSyms (prime^(w+1)).size (prime^(w+1)),binSyms 1 1,binSyms W.size W,record]
      (∀ i, seed.R (headers i) = header i) →
      (∀ j, (∀ i, fan i ≠ j) → seed.L j = [] ∧ ((∀ i, headers i ≠ j) → seed.R j = [])) →
      PackedPieceHandoffWithCharge cleanupWeight c.cells (packedChildOutput atom c.cells)
        body (body entry) fan dst seed (budget-⌊entryRate*scale⌋₊) →
      MoveOnBankExec parent child w W ports record position (fun f => embProg workspace id (body f)) code
        budget charged := by
  obtain ⟨workspace,wrap,restore⟩ := recordHeaderReturn (P := P) (U := U) (Q := Q)
    ports room headers tmp buf (fun i => owner ▸ outside i _) (owner ▸ (tmpOff _).symm) (owner ▸ (bufOff _).symm) work
  obtain ⟨move,run⟩ := chargedCutoffMove body entry bank tmp buf tmpOff bufOff distinct capacity dst apart
  refine ⟨workspace,wrap body move,?_⟩
  intro charged w W parent record c child atom groups spectators wide layout logical size position
  let lane := packedDescriptor (64*atom) spectators
  have split : volume prime lane*142080 = volume prime wide := by
    simp [lane,wide,packedDescriptor,volume,Nat.mul_assoc]
  intro seed D rate entryRate fan budget scale short active enough localRate recordFits header seedHeaders clean worker
  let runtime := budget-⌊entryRate*scale⌋₊+1000000000*volume prime child
  have volumeEq := Fintype.card_congr position
  simp only [Fintype.card_fin] at volumeEq
  have positive : 0 < volume prime child := by
    rw [← c.cells_share]
    have := c.idlePositive
    have := Shared50ModularControl.prime_prime.pos
    unfold CutoffNodeInput.cells
    positivity
  have space := Nat.le_mul_of_pos_right (4*B+33) positive
  obtain ⟨reserve,fits⟩ := cutoffMoveReserve c D rate entryRate (1000000120+4*B) short active enough localRate
  change (1000000120+4*B)*volume prime child ≤ ⌊entryRate*scale⌋₊ at reserve
  change ⌊entryRate*scale⌋₊ ≤ budget at fits
  have wpos : 0 < W := Nat.pos_of_mul_pos_left (volumeEq ▸ positive)
  have copyCost := recordHeaderCost w W record wpos recordFits
  change seedLoadBill header ≤ 57*((prime^(w+1))^16*W) at copyCost
  have total : seedLoadBill header+runtime+30*((prime^(w+1))^16*W)+4*B+33 ≤ budget := by
    rw [← volumeEq] at copyCost ⊢
    dsimp only [runtime]
    rw [Nat.add_mul] at space reserve
    omega
  suffices runRecord : MoveOnBankExec parent child w W ports record position
      (fun f => embProg workspace id (body f)) (wrap body move)
      (seedLoadBill header+runtime+30*((prime^(w+1))^16*W)+4*B+33) charged by
    intro smaller _ _ _ u S word ready cleanBank
    obtain ⟨z,F,t,y,exec,paid,rest⟩ := runRecord smaller u S word ready cleanBank
    exact ⟨z,F,t,y,exec,paid.weaken total,rest⟩
  apply restore parent child record position (split.trans size) body move runtime charged
  intro x u S source left filled right
  have clear (i : Fin 4) := work i
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at clear
  rw [← owner] at source
  obtain ⟨z,F,t,exec,user,out,bill⟩ := run c seed D rate entryRate short active (by push_cast at enough; linarith) localRate
    worker (x ∘ position) u S (by
      change S.R (bank (Fin.succ 0)) = List.ofFn (fun k : Fin (volume prime lane*142080) =>
        SparseRoleCircuit.encode (x (position (logical (k.cast split)))))
      simpa only [position,Equiv.trans_apply,Equiv.symm_apply_apply,finCongr_apply,Fin.cast_cast] using source)
    (fun i => left _) (fun i h => right _ (owner ▸ bank.injective.ne h) (fun j => outside j i)) (left _)
    (right _ (owner ▸ (tmpOff _).symm) (fun i => (clear i).1.1))
    (right _ (owner ▸ (bufOff _).symm) (fun i => (clear i).1.2))
    (fun j away => ⟨(clean _ away).1,(clean _ away).2 (fun i => outside i j)⟩) (by
      intro j away
      have h := clean j (fun i => away _)
      refine ⟨(left j).trans h.1.symm,?_⟩
      by_cases hit : ∃ i, headers i = j
      · obtain ⟨i,rfl⟩ := hit
        exact (filled i).trans (seedHeaders i).symm
      · have absent := fun i eq => hit ⟨i,eq⟩
        exact (right j (owner ▸ (away _).symm) absent).trans (h.2 absent).symm)
  change RecordPayload (bank (Fin.succ 0)) (fun _ => blank) 0
    (Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x ∘ position) ∘ logical) F at out
  rw [owner] at out
  let y := Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x ∘ position) ∘ position.symm
  refine ⟨z,F,t,y,exec,user,?_,?_,(bill _ (List.nodup_finRange _) (fun i => List.mem_finRange _)).trans
    (Nat.add_le_add_left (Nat.min_le_right budget runtime) _)⟩
  · intro k
    simp [y]
  · apply castPayload size
    simpa [y,position,Function.comp_def] using out

/-- Place MOVE around the installed input and output ports on the existing
host. Only the three return tapes need blank words in the child's seed. -/
theorem installedCutoffMove [M8.Machine.Net] {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U) (entry : P)
    (src dst : Fin (142081+2) ↪ Fin T) (saved : Fin 3 ↪ Fin T) (tmp buf : Fin T)
    (inputs : ∀ i j, saved i ≠ src j) (outputs : ∀ i j, saved i ≠ childReturnFan dst j)
    (temps : ∀ j ∈ [tmp,buf], (∀ i, j ≠ src i) ∧ ∀ i, j ≠ saved i) (distinct : tmp ≠ buf)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    ∃ code : Pr P T Q prime U, ∀ (c : CutoffNodeInput) seed (D rate entryRate : ℝ),
      let child := c.node
      let atom := c.w+1
      let width : child.width = 64*atom := c.width
      let groups : 142080 ∣ child.rows := ⟨_,c.rows⟩
      let W := CopyChildLayout.spectators child / 142080
      let lane := packedDescriptor (64*atom) W
      let m := volume prime lane
      let wide := packedDescriptor (64*atom) (W*142080)
      let size : m*142080 = volume prime wide := by simp [m,lane,wide,volume,packedDescriptor,Nat.mul_assoc]
      let layout := CopyChildLayout.changeLayout wide child width.symm (scheduledMoveSpectators child atom groups)
      let position := (CopyChildLayout.flatAddress wide).symm.trans (layout.trans (CopyChildLayout.flatAddress child))
      let budget := cutoffTreeBudget D rate c.cutoff (c.depth-c.path.length) child
      let scale := (volume prime child : ℝ)*(child.width : ℝ)^M8.Machine.BudgetBound.tau
      c.path.length < c.depth → c.cutoff < child.width → 214000000 ≤ entryRate → entryRate ≤ D →
      PackedPieceHandoffWithCharge cleanupWeight c.cells (packedChildOutput atom c.cells) body (body entry) src dst seed (budget-⌊entryRate*scale⌋₊) →
      ∀ (x : Fin (volume prime child) → ZMod 2) u (S : Stacks T prime),
      S.R (saved 0) = List.ofFn (fun i => SparseRoleCircuit.encode (x (position (i.cast size)))) →
      (∀ i, S.L (src i) = [] ∧ S.R (src i) = []) →
      (∀ i, S.L (saved i) = []) → (∀ i, i ≠ 0 → S.R (saved i) = []) →
      S.L tmp = [] → S.R tmp = [] → S.R buf = [] →
      (∀ i, seed.L (saved i) = [] ∧ seed.R (saved i) = []) →
      (∀ j, (∀ i, src i ≠ j) → (∀ i, saved i ≠ j) → S.L j = seed.L j ∧ S.R j = seed.R j) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        RecordPayload (saved 0) (fun _ => blank) 0
          ((Shared50RecursiveNodeRows.transpose (one_dvd child.rows) x) ∘ position) F ∧
        t ≤ budget := by
  obtain ⟨bank,fan,ret,cover⟩ := splitBankForInput src saved inputs
  have atRet i : bank (moveReturnPorts i) = saved i := DFunLike.congr_fun ret i
  have atInput i : bank (withHelperPort (intervalOwners 142080) i) = src i := DFunLike.congr_fun fan i
  have sourcePort : bank (Fin.succ 0) = saved 0 := atRet 0
  have off j (mem : j ∈ [tmp,buf]) k : bank k ≠ j := by
    rcases cover k with ⟨i,h⟩|⟨i,h⟩
    · exact h ▸ ((temps j mem).2 i).symm
    · exact h ▸ ((temps j mem).1 i).symm
  obtain ⟨code,run⟩ := scheduledCutoffMove body entry bank tmp buf (off tmp (by simp)) (off buf (by simp))
    distinct capacity dst (fun j i => (atRet j) ▸ outputs j i)
  rw [fan,sourcePort] at run
  refine ⟨code,?_⟩
  intro c seed D rate entryRate child atom width groups W lane m wide size layout position budget scale short active enough localRate worker x u S source vacant left right tl tr br clean stock
  refine run c seed D rate entryRate short active enough localRate worker x u S source ?_ ?_ tl tr br ?_ ?_
  · intro j
    rcases cover j with ⟨i,h⟩|⟨i,h⟩
    · exact h ▸ left i
    · exact h ▸ (vacant i).1
  · intro j ne
    rcases cover j with ⟨i,h⟩|⟨i,h⟩
    · rw [h]
      apply right
      rintro rfl
      exact ne (bank.injective (h.trans sourcePort.symm))
    · exact h ▸ (vacant i).2
  · intro j away
    rcases cover j with ⟨i,h⟩|⟨i,h⟩
    · rw [h]; exact clean i
    · exact False.elim (away i h.symm)
  · intro j away
    exact stock j (fun i => atInput i ▸ away _) (fun i => atRet i ▸ away _)

/-- Borrow a workspace for one scheduled MOVE. The enclosing procedure
table supplies the recursive labels and all tapes outside the workspace
retain their two physical stacks. -/
theorem placedCutoffMove [M8.Machine.Net] {P R U : Type} {T N Q : ℕ} (body : P → Pr P T Q prime U) (entry : P)
    (place : Fin T ↪ Fin N) (label : P → R) (host : R → Pr R N Q prime U)
    (installed : ∀ f, host (label f) = embProg place label (body f))
    (src dst : Fin (142081+2) ↪ Fin T) (saved : Fin 3 ↪ Fin T) (tmp buf : Fin T)
    (inputs : ∀ i j, saved i ≠ src j) (outputs : ∀ i j, saved i ≠ childReturnFan dst j)
    (temps : ∀ j ∈ [tmp,buf], (∀ i, j ≠ src i) ∧ ∀ i, j ≠ saved i) (distinct : tmp ≠ buf)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    ∃ code : Pr R N Q prime U, ∀ (c : CutoffNodeInput) seed (D rate entryRate : ℝ),
      let child := c.node
      let atom := c.w+1
      let width : child.width = 64*atom := c.width
      let groups : 142080 ∣ child.rows := ⟨_,c.rows⟩
      let W := CopyChildLayout.spectators child / 142080
      let lane := packedDescriptor (64*atom) W
      let m := volume prime lane
      let wide := packedDescriptor (64*atom) (W*142080)
      let size : m*142080 = volume prime wide := by simp [m,lane,wide,volume,packedDescriptor,Nat.mul_assoc]
      let layout := CopyChildLayout.changeLayout wide child width.symm (scheduledMoveSpectators child atom groups)
      let position := (CopyChildLayout.flatAddress wide).symm.trans (layout.trans (CopyChildLayout.flatAddress child))
      let budget := cutoffTreeBudget D rate c.cutoff (c.depth-c.path.length) child
      let scale := (volume prime child : ℝ)*(child.width : ℝ)^M8.Machine.BudgetBound.tau
      c.path.length < c.depth → c.cutoff < child.width → 214000000 ≤ entryRate → entryRate ≤ D →
      PackedPieceHandoffWithCharge cleanupWeight c.cells (packedChildOutput atom c.cells) body (body entry) src dst seed (budget-⌊entryRate*scale⌋₊) →
      ∀ (x : Fin (volume prime child) → ZMod 2) u (S : Stacks N prime),
      let B := embStk place S
      B.R (saved 0) = List.ofFn (fun i => SparseRoleCircuit.encode (x (position (i.cast size)))) →
      (∀ i, B.L (src i) = [] ∧ B.R (src i) = []) →
      (∀ i, B.L (saved i) = []) → (∀ i, i ≠ 0 → B.R (saved i) = []) →
      B.L tmp = [] → B.R tmp = [] → B.R buf = [] →
      (∀ i, seed.L (saved i) = [] ∧ seed.R (saved i) = []) →
      (∀ j, (∀ i, src i ≠ j) → (∀ i, saved i ≠ j) → B.L j = seed.L j ∧ B.R j = seed.R j) →
      ∃ z F t, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        RecordPayload (place (saved 0)) (fun _ => blank) 0
          ((Shared50RecursiveNodeRows.transpose (one_dvd child.rows) x) ∘ position) F ∧
        t ≤ budget ∧ ∀ j, (∀ i, place i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨move,run⟩ := installedCutoffMove body entry src dst saved tmp buf inputs outputs temps distinct capacity
  refine ⟨embProg place label move,?_⟩
  intro c seed D rate entryRate child atom width groups W lane m wide size layout position budget scale short active enough localRate worker x u S B source vacant left right tl tr br clean stock
  obtain ⟨v,E,t,exec,user,out,bill⟩ := run c seed D rate entryRate short active enough localRate worker x
    (embDn place u) B source vacant left right tl tr br clean stock
  obtain ⟨z,F,placed,_,same,view,off⟩ := exec_emb place.injective installed exec u rfl S rfl
  rw [← view] at out
  exact ⟨z,F,t,placed,same.trans user,out,bill,off⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
