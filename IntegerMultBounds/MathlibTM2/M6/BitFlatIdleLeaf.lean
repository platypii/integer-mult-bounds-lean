module

public import IntegerMultBounds.MathlibTM2.M6.BitPackedChildLayout
public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleCall
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryDirectoryLeaf

/-! Execute a stopped child directly at the physical interval of its remainder owner. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host M8.RevMachine
open RecursiveInterchangeLayout (Descriptor volume)
open Shared50ModularControl (prime)

theorem inheritedLeaf_exec [M8.Machine.Net] {n Q V : ℕ} {P U : Type}
    (capacity : columnCapacity ≤ Q) (body : P → Pr P (n+LeafCore.small) Q prime U)
    (src : Fin 6 → Fin n) (port : Fin n) (child interval : Descriptor)
    (size : volume prime interval = V) (position : Fin (volume prime child) ≃ Fin V)
    (width : interval.width = child.width) (coords : InheritedIntervalPositions child interval size position)
    (word : Fin V → ZMod 2) (u : HS (n+LeafCore.small) Q prime U) (S : Stacks (n+LeafCore.small) prime)
    (positive : 0 < V) (headers : ∀ j, S.R ((src j).castAdd LeafCore.small) = (Routines.hdr interval j).map bitSymbol)
    (payload : RecordPayload (port.castAdd LeafCore.small) (fun _ => blank) 0 word S)
    (free : ∀ j : Fin LeafCore.small, S.L (j.natAdd n) = [] ∧ S.R (j.natAdd n) = []) :
    ∃ z F steps changed, Exec body (hostedStoppedDirectory capacity src port) (mk u S) steps (mk z F) ∧
      (steps : ℝ) ≤ descriptorHeaderCost interval +
        ((LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|))*
        ((V : ℝ)*((max 1 child.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) ∧
      z.user = u.user ∧ RecordPayload (port.castAdd LeafCore.small) (fun _ => blank) 0 changed F ∧
      (∀ t, t ≠ port.castAdd LeafCore.small → F.L t = S.L t ∧ F.R t = S.R t) ∧
      ∀ k, changed (position k) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) k := by
  subst V
  obtain ⟨z,F,steps,user,run,paid,out,_,keep,clean⟩ :=
    hostedStoppedView_exec capacity body src port interval word u S positive headers payload free
  refine ⟨z,F,steps,_,run,width ▸ paid,user,out,?_,?_⟩
  · intro t
    refine Fin.addCases (fun j ne => keep j (fun eq => ne (congrArg (fun t : Fin n => t.castAdd LeafCore.small) eq)))
      (fun j _ => ⟨(clean j).1.trans (free j).1.symm,(clean j).2.trans (free j).2.symm⟩) t
  · exact (coords.transpose_iff width word _).2 (by rfl)

noncomputable def moveWidthProgram {P U : Type} {T Q : ℕ} (r : Fin 10 ↪ Fin T) (rank : ℕ) : Pr P T Q prime U :=
  let push := Prog.act (.push (.rt (r 0)) (fun _ => Node.tick) .done)
  let pop := Prog.act (.pop (.rt (r 0)) (fun v _ => v) .done)
  (((push.seq (Node.umul rank (r 0) (r 2) (r 4))).seq pop).seq
    ((unaryBinary (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9)).seq (bclear (r 2))))

/-- A stopped MOVE reads the two leading packed fields directly. Four descriptor fields
share the unit register; only width and spectator count vary. -/
theorem packedMoveLeaf_exec [M8.Machine.Net] {n Q w W : ℕ} [NeZero (prime^(w+1))] {P U : Type}
    (capacity : columnCapacity ≤ Q) (body : P → Pr P (n+LeafCore.small) Q prime U)
    (bank : Fin 35 ↪ Fin n) (r : Fin 10 ↪ Fin n) (clock : r 0 = bank 33)
    (outside : ∀ i, bank i ≠ r 3) (rank : ℕ) (child : Descriptor) (width : child.width = (w+1)*rank)
    (position : Fin (volume prime child) ≃ Fin ((prime^(w+1))^16*W))
    (packed : ∀ i, (position i).val = (CopyChildLayout.packActive child i).val)
    (word : Fin ((prime^(w+1))^16*W) → ZMod 2) (u : HS (n+LeafCore.small) Q prime U) (S : Stacks (n+LeafCore.small) prime)
    (positive : 0 < (prime^(w+1))^16*W) :
    let V := (prime^(w+1))^16*W
    let lane := packedDescriptor child.width (CopyChildLayout.spectators child)
    let src : Fin 6 → Fin n := ![bank 28,bank 28,bank 28,r 3,bank 28,bank 34]
    let ports := bank.trans (Fin.castAddEmb LeafCore.small)
    let record := binSyms (CopyChildLayout.spectators child).size (CopyChildLayout.spectators child)
    let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) ports (prime^(w+1)).size W.size record
      SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
    let work := r.trans (Fin.castAddEmb LeafCore.small)
    (∀ j : Fin 10, 2 ≤ j.val → S.R (work j) = []) →
    stored word S →
    (∀ j : Fin LeafCore.small, S.L (j.natAdd n) = [] ∧ S.R (j.natAdd n) = []) →
    ∃ z F steps changed, Exec body (((moveWidthProgram work rank).seq (hostedStoppedDirectory capacity src (bank 24))).seq (bclear (work 3))) (mk u S) steps (mk z F) ∧
      (steps : ℝ) ≤ (4*w+23*child.width+2*child.width.size+24 : ℕ) + (descriptorHeaderCost lane : ℝ) +
        ((LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|))*
        ((V : ℝ)*((max 1 child.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) ∧
      z.user = u.user ∧ stored changed F ∧
      (∀ t, t ≠ ports 24 → F.L t = S.L t ∧ F.R t = S.R t) ∧
      ∀ k, changed (position k) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) k := by
  intro V lane src ports record stored work empty ready free
  let wordWidth := binSyms (A := prime) child.width.size child.width
  let D := {S with R := Function.update S.R (work 3) wordWidth}
  have apart (i) : ports i ≠ work 3 := fun eq => outside i ((Fin.castAddEmb LeafCore.small).injective eq)
  obtain ⟨v,m,user₁,time,prepare⟩ := packedMoveWidth_exec body work rank w u S
    (by change (S.R ((r 0).castAdd _)).length = w; rw [clock]; exact ready.clock) empty
  rw [← width] at prepare time
  have storedD : stored word D := ready.returnPayload
    (fun i _ => ⟨rfl,Function.update_of_ne (apart i) ..⟩) (by
      intro k
      simpa only [D,Function.update_of_ne (apart 24)] using (ready.src k).symm)
  have active : D.R (work 3) = wordWidth := Function.update_self ..
  have freeD (j : Fin LeafCore.small) : D.L (j.natAdd n) = [] ∧ D.R (j.natAdd n) = [] := by
    have ne : j.natAdd n ≠ work 3 := by
      intro eq
      have h := congrArg Fin.val eq
      change n+j.val = (r 3).val at h
      have := (r 3).isLt
      omega
    exact ⟨(free j).1,(Function.update_of_ne ne ..).trans (free j).2⟩
  have headers (j : Fin 6) : D.R ((src j).castAdd LeafCore.small) = (Routines.hdr lane j).map bitSymbol := by
    change _ = (FlatCoordinateSchedule.bits (RecursiveDimensionBank.values lane j)).map bitSymbol
    rw [canonicalBits_symbols]
    have one : D.R (ports 28) = binSyms (Nat.size 1) 1 := by simpa using storedD.one
    fin_cases j <;> first | exact one | exact active | exact storedD.archive
  have size := Fintype.card_congr position
  simp only [Fintype.card_fin] at size
  have volumeEq : volume prime lane = V := by
    dsimp only [V]
    rw [← size]
    simp only [volume,lane,packedDescriptor,CopyChildLayout.spectators,one_mul,mul_one]
    ring
  have payloadPort : (bank 24).castAdd LeafCore.small = ports 24 := rfl
  obtain ⟨z,F,t,y,exec,paid,user,out,off,reads⟩ := inheritedLeaf_exec capacity body src (bank 24) child lane volumeEq position rfl
    (fun k => (packed k).symm.trans (packActive_packed child.width (CopyChildLayout.spectators child) ((position k).cast volumeEq.symm)).symm) word v D positive headers
      (by intro k; simpa only [List.map_ofFn,payloadPort] using storedD.src k) freeD
  obtain ⟨z',user₃,_,clear⟩ := bclear_exec (body := body) (work 3) z F
  have kept := off (work 3) (apart 24).symm
  have length : (F.R (work 3)).length = child.width.size := by rw [kept.2,active]; exact length_binSyms ..
  have after : stored y F := storedD.returnPayload (fun j ne => off _ (ports.injective.ne ne))
    (by intro k; simpa only [List.map_ofFn,payloadPort] using (out k).symm)
  let G := {F with R := Function.update F.R (work 3) []}
  have returned : stored y G := after.returnPayload (fun i _ => ⟨rfl,Function.update_of_ne (apart i) ..⟩) (by
    intro k
    simpa only [G,Function.update_of_ne (apart 24)] using (after.src k).symm)
  refine ⟨z',G,_,y,Exec.seq (Exec.seq prepare exec) clear,?_,user₃.trans (user.trans user₁),
    returned,?_,reads⟩
  · rw [length]
    push_cast at paid ⊢
    linarith only [paid,show (m : ℝ) ≤ 4*w+23*child.width+22 by exact_mod_cast time]
  · intro j ne
    obtain ⟨left,right⟩ := off j ne
    refine ⟨left,?_⟩
    by_cases atWidth : j = work 3
    · subst j
      exact (Function.update_self ..).trans (empty 3 (by decide)).symm
    · exact (Function.update_of_ne atWidth ..).trans (right.trans (Function.update_of_ne atWidth ..))

private theorem recordOnBank {m T w W : ℕ} [NeZero (prime^(w+1))] (place : Fin m ↪ Fin T)
    (regs : Fin 35 ↪ Fin m) (target : Fin 35 ↪ Fin T) (same : regs.trans place = target)
    (record : List (Fin (prime+4))) (word : Fin ((prime^(w+1))^16*W) → ZMod 2) (S : Stacks T prime) :
    RecordReady (b := prime) (w := w) (d := 16) (W := W) regs (prime^(w+1)).size W.size record
      SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 word (embStk place S) ↔
    RecordReady (b := prime) (w := w) (d := 16) (W := W) target (prime^(w+1)).size W.size record
      SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 word S := by
  subst target
  constructor <;> rintro ⟨a,b,c,d,e,g,h,i,j⟩ <;> exact ⟨a,b,c,d,e,g,h,i,j⟩

private theorem recordPlacement {m n T : ℕ} (fits : 44+m ≤ n+35) (ports : Fin (n+35) ↪ Fin T) :
    ((Fin.castAddEmb 9 (n := 35)).trans (Fin.castAddEmb m)).trans ((Fin.castLEEmb fits).trans ports) =
      scheduledRecordPorts (n := n) ports := by
  apply Function.Embedding.ext
  intro i
  rfl

private theorem placedScratch {m k T : ℕ} (fits : m ≤ k) (ports : Fin k ↪ Fin T)
    (S F : Stacks T prime) (owner : Fin m) (low : owner.val < 35)
    (clean : ∀ j : Fin k, 35 ≤ j.val → S.L (ports j) = [] ∧ S.R (ports j) = [])
    (keep : ∀ i : Fin m, i ≠ owner → F.L (ports (i.castLE fits)) = S.L (ports (i.castLE fits)) ∧
      F.R (ports (i.castLE fits)) = S.R (ports (i.castLE fits)))
    (frame : ∀ t, (∀ i : Fin m, ports (i.castLE fits) ≠ t) → F.L t = S.L t ∧ F.R t = S.R t) :
    ∀ j : Fin k, 35 ≤ j.val → F.L (ports j) = [] ∧ F.R (ports j) = [] := by
  intro j hj
  have restored : F.L (ports j) = S.L (ports j) ∧ F.R (ports j) = S.R (ports j) := by
    by_cases h : j.val < m
    · exact keep ⟨j.val,h⟩ (fun eq => by have := congrArg Fin.val eq; change j.val = owner.val at this; omega)
    · exact frame _ (fun i eq => h ((congrArg Fin.val (ports.injective eq)) ▸
        (show (i.castLE fits).val < m from i.isLt)))
  exact ⟨restored.1.trans (clean j hj).1,restored.2.trans (clean j hj).2⟩

private theorem moveLeafFits [M8.Machine.Net] : 44+LeafCore.small ≤ rowSwapBlock.tapes+35 := by
  have h := copyLeafFitsRowSwap
  unfold LeafCore.small M8.Machine.ArbitraryWidthOriginalZeroBranch.count
      M8.Machine.ArbitraryWidthOriginalZeroBranch.highCount at *
  omega

private theorem moveLeafBill [M8.Machine.Net] (child : Descriptor) (w : ℕ) (pos : 0 < volume prime child)
    (clock : w < child.width) (core rate : ℝ) (room : 163+core ≤ rate) :
    let lane := packedDescriptor child.width (CopyChildLayout.spectators child)
    let V := volume prime child
    ((4*w+23*child.width+2*child.width.size+24 : ℕ) : ℝ) + descriptorHeaderCost lane +
      core*(V*((max 1 child.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) ≤
      (rate*(child.width : ℝ)^M8.Machine.BudgetBound.tau)*V := by
  intro lane V
  have equal : volume prime lane = V := by
    simp only [lane,V,volume,packedDescriptor,CopyChildLayout.spectators,one_mul,mul_one]
    ring
  have header := descriptorHeaderCost_le lane (LeafCore.positive_of_volume (equal ▸ pos))
  rw [equal] at header
  have h : child.width ≤ V := RecursiveHeaderBounds.values_le_volume Shared50ModularControl.prime_prime.two_le
    child (LeafCore.positive_of_volume pos) 3
  have size : child.width.size ≤ child.width := Nat.size_le.mpr Nat.lt_two_pow_self
  have setup : 4*w+23*child.width+2*child.width.size+24+descriptorHeaderCost lane ≤ 163*V := by
    change 0 < V at pos
    omega
  have positive : 1 ≤ child.width := by omega
  rw [max_eq_right positive]
  let power := (child.width : ℝ)^M8.Machine.BudgetBound.tau
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast positive) M8.Machine.BudgetBound.exponent_range.1.le
  have base := le_mul_of_one_le_right (Nat.cast_nonneg (α := ℝ) V) one
  have bound := mul_le_mul_of_nonneg_right room (le_trans (Nat.cast_nonneg (α := ℝ) V) base)
  have fixed : ((4*w+23*child.width+2*child.width.size+24 : ℕ) : ℝ) + descriptorHeaderCost lane ≤ 163*(V : ℝ) := by exact_mod_cast setup
  change _ + core*(V*power) ≤ rate*power*V
  linarith only [fixed,base,bound]

/-- Place the stopped MOVE on the caller's record and row-swap workspace.
The installed code depends only on rank, ports and state capacity. -/
theorem stoppedMoveProgram [M8.Machine.Net] {P U : Type} {T Q : ℕ}
    (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (capacity : columnCapacity ≤ Q) (rank : ℕ) (positiveRank : 0 < rank) :
    ∃ code : Pr P T Q prime U, ∀ (body : P → Pr P T Q prime U) (f : P), body f = code →
      ∀ (node child : Descriptor) (w W : ℕ), child.width = (w+1)*rank →
      ∀ position : Fin (volume prime child) ≃ Fin ((prime^(w+1))^16*W),
      (∀ i, (position i).val = (CopyChildLayout.packActive child i).val) → 0 < W →
      let core : ℝ := (LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|)
      ∀ rate : ℝ, 163+core ≤ rate → ScheduledChildExec node child w W ports
        (binSyms (CopyChildLayout.spectators child).size (CopyChildLayout.spectators child)) position body f
        ⌊(rate*(child.width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime child⌋₊ := by
  let bank := Fin.castAddEmb 9 (n := 35)
  let r : Fin 10 ↪ Fin 44 := ⟨fun i => ⟨33+i.val,by omega⟩,fun i j eq => Fin.ext (by
    have h := congrArg Fin.val eq
    change 33+i.val = 33+j.val at h
    omega)⟩
  let fits := moveLeafFits
  let slot :=  Fin.castLEEmb fits
  let place := slot.trans ports
  let work := r.trans (Fin.castAddEmb LeafCore.small)
  let src : Fin 6 → Fin 44 := ![bank 28,bank 28,bank 28,r 3,bank 28,bank 34]
  let leaf : Pr Empty (44+LeafCore.small) Q prime U :=
    ((moveWidthProgram work rank).seq (hostedStoppedDirectory capacity src (bank 24))).seq (bclear (work 3))
  refine ⟨embProg place Empty.elim leaf,?_⟩
  intro body f installed node child w W width position packed pos core rate room
  letI : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
  intro smaller u S word stored clean
  let regs := bank.trans (Fin.castAddEmb LeafCore.small)
  have align := recordPlacement (n := rowSwapBlock.tapes) fits ports
  have size := Fintype.card_congr position
  simp only [Fintype.card_fin] at size
  obtain ⟨v,D,t,y,run,paid,user,out,rest,reads⟩ := packedMoveLeaf_exec capacity
    (Empty.elim : Empty → Pr Empty (44+LeafCore.small) Q prime U) bank r rfl
    (fun i eq => by have h := congrArg Fin.val eq; change i.val = 36 at h; have := i.isLt; omega)
    rank child width position packed word (embDn place u) (embStk place S)
    (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) pos)
    (fun j hj => (clean (slot (work j)) (by change 35 ≤ 33+j.val; omega)).2)
    ((recordOnBank place regs _ align _ word S).2 stored) (fun j => clean (slot (j.natAdd 44)) (by change 35 ≤ 44+j.val; omega))
  obtain ⟨z,F,exec,_,same,view,frame⟩ := exec_emb (body' := body) (ι := Empty.elim) place.injective
    (fun i => nomatch i) run u rfl S rfl
  rw [← view] at out rest
  have live : 0 < volume prime child := size ▸ Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) pos
  have clock : w < child.width := by
    rw [width]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_mul_of_pos_right _ positiveRank)
  have bill := moveLeafBill child w live clock core rate room
  dsimp only [core] at bill
  rw [← size] at paid
  refine ⟨z,F,t,y,?_,Nat.le_floor (paid.trans bill),same.trans user,?_,?_,?_,reads⟩
  · rw [installed]
    exact exec
  · exact (recordOnBank place regs _ align _ y F).1 out
  · exact placedScratch fits ports S F ((bank 24).castAdd LeafCore.small) (show 24 < 35 by decide) clean rest frame
  · intro j away
    exact frame j (fun i => away (slot i))

end IntegerMultBounds.MathlibTM2.M6.BitNode
