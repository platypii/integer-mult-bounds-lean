module

public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedSweep
public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleLeaf

/-! Select the recursive or stopped worker from the tag on its scheduled record. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover.Fallback Stack Host
open RecursiveInterchangeLayout M8.RevMachine
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

private theorem replaceArchive {T w W : ℕ} [NeZero (prime^(w+1))] (bank : Fin 35 ↪ Fin T)
    (record next : List (Fin (prime+4))) (word : Fin ((prime^(w+1))^16*W) → ZMod 2) (S : Stacks T prime)
    (ready : RecordReady (b := prime) (w := w) (d := 16) (W := W) bank (prime^(w+1)).size W.size record
      SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 word S) :
    RecordReady (b := prime) (w := w) (d := 16) (W := W) bank (prime^(w+1)).size W.size next
      SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 word
      {S with R := Function.update S.R (bank 34) next} := by
  refine ⟨?_,?_,?_,?_,?_,Function.update_self ..,?_,?_,?_⟩
  all_goals try first
    | simpa [bank.injective.eq_iff] using ready.modulus
    | simpa [bank.injective.eq_iff] using ready.width
    | simpa [bank.injective.eq_iff] using ready.one
    | simpa [bank.injective.eq_iff] using ready.padded
    | simpa [bank.injective.eq_iff] using ready.clock
    | simpa [bank.injective.eq_iff] using ready.src
    | simpa [bank.injective.eq_iff] using ready.dst
  intro i hi
  have ne : i ≠ 34 := fun eq => (by decide : (34 : Fin 35) ∉ shearWork) (eq ▸ hi)
  simpa [Function.update_of_ne (bank.injective.ne ne)] using ready.scratch i hi

/-- Retire the five generated right-stack controls after a child returns.
The cost depends on their recorded lengths, independently of child runtime. -/
theorem retireWorkerControls {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin 35 ↪ Fin T) (w W : ℕ) (record : List (Fin (prime+4)))
    (word : Fin ((prime^(w+1))^16*W) → ZMod 2) (u : HS T Q prime U) (S : Stacks T prime)
    (ready : RecordReady (b := prime) (w := w) (d := 16) (W := W) bank (prime^(w+1)).size W.size record
      SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 word S) :
    let controls := ([2,27,28,32,33] : List (Fin 35)).map bank
    ∃ z, z.user = u.user ∧ Exec body (Mult.ShortConv.clearWords controls) (mk u S)
      (2*(2*(prime^(w+1)).size+W.size+w)+13)
      (mk z {S with R := fun k => if k ∈ controls then [] else S.R k}) := by
  intro controls
  obtain ⟨z,user,run⟩ := Mult.ShortConv.clearWords_exec (body := body) controls
    ((by decide : ([2,27,28,32,33] : List (Fin 35)).Nodup).map bank.injective) u S
  refine ⟨z,user,run.cast ?_ rfl⟩
  simp only [controls,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,
    ready.modulus,ready.width,ready.one,ready.padded,ready.clock,length_binSyms]
  omega

/-- Copy the inherited cutoff into an empty worker archive. The source and
the rest of the prepared record survive, including the live payload. -/
theorem inheritWorkerCutoff {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin 35 ↪ Fin T) (cut : Fin T) (off : ∀ i, bank i ≠ cut)
    (w W L cutoff : ℕ) (word : Fin ((prime^(w+1))^16*W) → ZMod 2)
    (u : HS T Q prime U) (S : Stacks T prime) (header : S.R cut = binSyms L cutoff) :
    let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) bank (prime^(w+1)).size W.size
    let F := {S with R := Function.update S.R (bank 34) (binSyms L cutoff)}
    stored [] SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 word S →
    ∃ z, Exec body (bcopy cut (bank 34) (bank 0) (bank 1)) (mk u S) (6*L+6) (mk z F) ∧
      z.user = u.user ∧ stored (binSyms L cutoff) SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 word F := by
  intro stored F ready
  obtain ⟨z,user,copy⟩ := bcopy_exec (body := body) (a := cut) (c := bank 34) (t₁ := bank 0) (t₂ := bank 1)
    (by simp [Ne.symm (off _)]) u S (ready.scratch 0 (by decide)).2 (ready.scratch 1 (by decide)).2
  rw [header,length_binSyms,ready.archive,List.append_nil] at copy
  exact ⟨z,copy,user,replaceArchive bank _ _ _ _ ready⟩

/-- A call on an empty archive borrows the caller's cutoff for the
duration of the execution. The return clears the archive and restores all
tapes outside the worker, including the inherited header. -/
theorem inheritedWorkerCall [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (body : P → Pr P T Q prime U) (f : P) (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T)
    (cut : Fin T) (apart : ∀ i, ports i ≠ cut)
    (node child : Descriptor) (w W L cutoff budget : ℕ)
    (position : Fin (volume prime child) ≃ Fin ((prime^(w+1))^16*W))
    (worker : ScheduledChildExec node child w W ports (binSyms L cutoff) position body f budget) :
    let bank := scheduledRecordPorts ports
    let code := (bcopy cut (bank 34) (bank 0) (bank 1)).seq ((Prog.call f).seq (bclear (bank 34)))
    let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) bank (prime^(w+1)).size W.size []
      SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
    let clean := fun (S : Stacks T prime) => ∀ i : Fin (rowSwapBlock.tapes+35), 35 ≤ i.val →
      S.L (ports i) = [] ∧ S.R (ports i) = []
    child.width < node.width → ∀ u S word, S.R cut = binSyms L cutoff → stored word S → clean S →
      ∃ z F n y, Exec body code (mk u S) n (mk z F) ∧ n ≤ budget+8*L+10 ∧ z.user = u.user ∧
        stored y F ∧ clean F ∧ (∀ j, (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        ∀ h, y (position h) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) h := by
  intro bank code stored clean smaller u S word header ready free
  let D := {S with R := Function.update S.R (bank 34) (binSyms L cutoff)}
  have off (i : Fin (rowSwapBlock.tapes+35)) (hi : 35 ≤ i.val) : ports i ≠ bank 34 := by
    intro eq
    have h := congrArg Fin.val (ports.injective eq)
    change i.val = 34 at h
    omega
  obtain ⟨v,copy,user,loaded⟩ := inheritWorkerCutoff body bank cut (fun i => apart _) w W L cutoff word u S header ready
  obtain ⟨z,F,n,y,run,paid,same,out,blank,frame,read⟩ := worker smaller v D word loaded
    (fun i hi => ⟨(free i hi).1,(Function.update_of_ne (off i hi) ..).trans (free i hi).2⟩)
  obtain ⟨q,done,_,erase⟩ := bclear_exec (body := body) (bank 34) z F
  rw [out.archive,length_binSyms] at erase
  refine ⟨q,_,_,y,Exec.seq copy (Exec.seq (Exec.call run) erase),by omega,done.trans (same.trans user),
    replaceArchive bank _ _ _ _ out,?_,?_,read⟩
  · exact fun i hi => ⟨(blank i hi).1,(Function.update_of_ne (off i hi) ..).trans (blank i hi).2⟩
  · intro j away
    have ne : j ≠ bank 34 := (away _).symm
    exact ⟨(frame j away).1,(Function.update_of_ne ne ..).trans ((frame j away).2.trans (Function.update_of_ne ne ..))⟩

/-- Prepare controls for a packed child, borrow the cutoff, and return the
transposed payload with an empty archive. -/
theorem inheritedPackedChildCall [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (body : P → Pr P T Q prime U) (f : P) (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T)
    (cut : Fin T) (outsideCut : ∀ i, ports i ≠ cut)
    (headers : Fin 127 → Fin 6 → Fin T) (apart : ∀ i j k, headers i j ≠ ports k) :
    let localPort := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let bank := localPort.trans ports
    ∃ code, ∀ (node desc : Descriptor) (w W L cutoff budget : ℕ),
    let M := prime^(w+1)
    let suffix := M^112*W
    ∀ (position : Fin (volume prime desc) ≃ Fin (M^16*suffix))
      (x : Fin (M^16*suffix) → ZMod 2) (u : HS T Q prime U) (S : Stacks T prime), desc.width < node.width →
    S.R cut = binSyms L cutoff → S.R (bank 34) = [] →
    (∀ i j, S.R (headers i j) = (Routines.hdr (helperAdjacentView (w+1) 1 W i) j).map bitSymbol) →
    (∀ i : Fin 35, i ≠ 24 → i ≠ 34 → S.L (bank i) = [] ∧ S.R (bank i) = []) →
    (∀ i : Fin (rowSwapBlock.tapes+35), 35 ≤ i.val → S.L (ports i) = [] ∧ S.R (ports i) = []) →
    (∀ z, readAt blank (S.L (bank 24)) (S.R (bank 24)) z = RadixToBinary.binaryEncoding.encode
      (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ x)) z)) →
    ScheduledChildExec node desc w suffix ports (binSyms L cutoff) position body f budget →
    ∃ z F t y, Exec body code (mk u S) t (mk z F) ∧
      t ≤ 14*M.size+6*suffix.size+6*(w+1)+11*(w+1).size+60+8*L+budget ∧ z.user = u.user ∧
      RecordReady (b := prime) (w := w) (d := 16) (W := suffix) bank M.size suffix.size []
        SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 y F ∧
      (∀ i : Fin (rowSwapBlock.tapes+35), 35 ≤ i.val → F.L (ports i) = [] ∧ F.R (ports i) = []) ∧
      (∀ j, (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
      ∀ h, y (position h) = Shared50RecursiveNodeRows.transpose (one_dvd desc.rows) (x ∘ position) h := by
  intro localPort bank
  obtain ⟨prepare,run⟩ := prepareWorkerRecord_exec body bank headers (fun i j k => apart i j (localPort k))
  refine ⟨.seq prepare ((bcopy cut (bank 34) (bank 0) (bank 1)).seq ((Prog.call f).seq (bclear (bank 34)))),?_⟩
  intro node desc w W L cutoff budget M suffix position x u S smaller header archive ready empty clean payload recurse
  obtain ⟨v,D,m,user,setup,cost,stored,left,off⟩ := run w W x u S ready empty payload
  have clear (i : Fin (rowSwapBlock.tapes+35)) (hi : 35 ≤ i.val) : D.L (ports i) = [] ∧ D.R (ports i) = [] := by
    have outside (k : Fin 35) : bank k ≠ ports i := by
      intro eq
      have h := congrArg Fin.val (ports.injective eq)
      change k.val = i.val at h
      omega
    exact ⟨(congrFun left _).trans (clean i hi).1,(off _ outside).trans (clean i hi).2⟩
  rw [archive] at stored
  have saved := (off cut (fun k => outsideCut (localPort k))).trans header
  obtain ⟨z,F,n,y,exec,paid,same,done,blank,frame,action⟩ :=
    inheritedWorkerCall body f ports cut outsideCut node desc w suffix L cutoff budget position recurse
      smaller v D x saved stored clear
  refine ⟨z,F,_,y,Exec.seq setup exec,?_,same.trans user,done,blank,?_,action⟩
  · change m ≤ 14*M.size+6*suffix.size+6*(w+1)+11*(w+1).size+50 at cost
    omega
  · intro j outside
    have h := frame j outside
    exact ⟨h.1.trans (congrFun left j),h.2.trans (off j (fun k => outside (localPort k)))⟩

/-- The trailing header for adjacent exchange number twice the rank minus
two already holds the MOVE leaf's spectator count. -/
theorem moveSpectatorHeader (child : Descriptor) (w W rank : ℕ) (positive : 0 < rank) (bound : rank ≤ 64)
    (width : child.width = (w+1)*rank)
    (size : volume prime child = (prime^(w+1))^16*((prime^(w+1))^112*W)) :
    let i : Fin 127 := ⟨2*rank-2,by omega⟩
    let count := CopyChildLayout.spectators child
    (Routines.hdr (helperAdjacentView (w+1) 1 W i) 5).map (bitSymbol (a := prime)) =
      binSyms count.size count := by
  intro i count
  let M := prime^(w+1)
  have exp : 2*rank + (126-i.val) = 128 := by dsimp [i]; omega
  have eq : M^(2*rank)*count = M^(2*rank)*(M^(126-i.val)*W) := by
    calc
      _ = volume prime child := by
        rw [show 2*rank = rank+rank by omega,pow_add,show M^rank = prime^child.width by rw [width,pow_mul]]
        unfold count volume CopyChildLayout.spectators
        ring
      _ = _ := by
        rw [size]
        change M^16*(M^112*W) = _
        simp only [← Nat.mul_assoc,← pow_add,exp]
  have same := Nat.eq_of_mul_eq_mul_left (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) eq
  rw [same]
  simpa [Routines.hdr,RecursiveDimensionBank.values,helperAdjacentView,M] using
    canonicalBits_symbols (A := prime) (M^(126-i.val)*W)

/-- On a prepared MOVE record, select the worker and its archive source
together. Both branches return the archive empty. -/
theorem moveCutoffCall [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (body : P → Pr P T Q prime U) (large leaf : P) (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T)
    (cut spectatorPort : Fin T) (off : ∀ i, ports i ≠ cut) (apart : ∀ i, ports i ≠ spectatorPort)
    (rank : ℕ) :
    ∃ code, ∀ (node child : Descriptor) (w W L cutoff recursiveTime leafTime : ℕ)
      (position : Fin (volume prime child) ≃ Fin ((prime^(w+1))^16*W)),
    child.width = (w+1)*rank → cutoff < 2^L → child.width.size ≤ L →
    let bank := scheduledRecordPorts ports
    let spectators := CopyChildLayout.spectators child
    let active := cutoff < child.width
    let price := if active then recursiveTime else leafTime
    let digits := if active then L else spectators.size
    (active → ScheduledChildExec node child w W ports (binSyms L cutoff) position body large recursiveTime) →
    (¬active → ScheduledChildExec node child w W ports (binSyms spectators.size spectators) position body leaf leafTime) →
    let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) bank (prime^(w+1)).size W.size []
      SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
    let clean := fun (S : Stacks T prime) => ∀ i : Fin (rowSwapBlock.tapes+35), 35 ≤ i.val →
      S.L (ports i) = [] ∧ S.R (ports i) = []
    child.width < node.width → ∀ u S word, S.R cut = binSyms L cutoff → S.R spectatorPort = binSyms spectators.size spectators → stored word S → clean S →
      ∃ z F n y, Exec body code (mk u S) n (mk z F) ∧ n ≤ price+8*digits+4*w+23*child.width+22*L+61 ∧ z.user = u.user ∧
        stored y F ∧ clean F ∧ (∀ j, (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        ∀ h, y (position h) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) h := by
  let bank := scheduledRecordPorts ports
  let cmp := ordinaryCutoffPorts bank cut (fun i => off _)
  let call : Fin T → P → Pr P T Q prime U := fun src f => (bcopy src (bank 34) (bank 0) (bank 1)).seq ((Prog.call f).seq (bclear (bank 34)))
  refine ⟨(ordinaryCutoffTest cmp rank).seq (.cond (fun z => symBit (z.scan (cmp 7))) (call cut large) (call spectatorPort leaf)),?_⟩
  intro node child w W L cutoff recursiveTime leafTime position width cutFits fits _ spectators active price digits recurse stop stored clean smaller u S word header spectator ready free
  have scratch : ∀ k : Fin 10, 2 ≤ k.val → cutoffColumnSlots k ∈ shearWork := by decide
  have clear (k : Fin 10) (hk : 2 ≤ k.val) : S.R (cmp k) = [] := by
    have ne : k ≠ 1 := by intro eq; subst k; contradiction
    simpa [cmp,ordinaryCutoffPorts,ne] using (ready.scratch _ (scratch k hk)).2
  obtain ⟨v,m,user,flag,paid,test⟩ := ordinaryCutoffTest_exec body cmp rank w L cutoff cutFits
    (width ▸ fits) u S ready.clock (by simpa [cmp,ordinaryCutoffPorts] using header) clear
  rw [← width] at flag paid
  by_cases h : active
  · obtain ⟨z,F,n,y,run,cost,same,rest⟩ := inheritedWorkerCall body large ports cut off node child w W L cutoff
      recursiveTime position (recurse h) smaller v S word header ready free
    refine ⟨z,F,_,y,Exec.seq test (Exec.cond_true (by simpa [mk_var,flag,active] using h) run),?_,same.trans user,rest⟩
    simp only [price,digits,ite_eq_left h]
    omega
  · obtain ⟨z,F,n,y,run,cost,same,rest⟩ := inheritedWorkerCall body leaf ports spectatorPort apart node child w W spectators.size spectators
      leafTime position (stop h) smaller v S word spectator ready free
    refine ⟨z,F,_,y,Exec.seq test (Exec.cond_false (by simpa [mk_var,flag,active] using h) run),?_,same.trans user,rest⟩
    simp only [price,digits,ite_eq_right h]
    omega

/-- At an active aligned parent the inherited precision fits the parent
width. All MOVE dispatch and return work is then linear in child volume. -/
private theorem moveOverhead_volume (child : Descriptor) (w W rank L digits : ℕ)
    (pos : 0 < W) (rankBound : rank ≤ 64) (width : child.width = (w+1)*rank)
    (precision : L ≤ 64*(w+1)) (word : digits ≤ max L (CopyChildLayout.spectators child).size) :
    let M := prime^(w+1)
    let suffix := M^112*W
    volume prime child = M^16*suffix →
    18*M.size+8*suffix.size+6*(w+1)+11*(w+1).size+124+8*digits+6*w+23*child.width+22*L ≤
      5000*volume prime child := by
  intro M suffix eq
  let V := volume prime child
  have base : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have tail : 0 < suffix := Nat.mul_pos (pow_pos base _) pos
  have live : 0 < V := by rw [show V = M^16*suffix from eq]; exact Nat.mul_pos (pow_pos base _) tail
  have mBound : M ≤ V := by rw [show V = M^16*suffix from eq]; exact (Nat.le_self_pow (by decide : 16 ≠ 0) M).trans (Nat.le_mul_of_pos_right _ tail)
  have sBound : suffix ≤ V := by rw [show V = M^16*suffix from eq]; exact Nat.le_mul_of_pos_left _ (pow_pos base _)
  have atom : w+1 ≤ V := (Nat.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_left Shared50ModularControl.prime_prime.two_le (w+1))).trans mBound
  have spec : CopyChildLayout.spectators child ≤ V := by
    have factor : V = (prime^child.width*prime^child.width)*CopyChildLayout.spectators child := by
      dsimp [V,volume,CopyChildLayout.spectators]
      ring
    rw [factor]
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (pow_pos Shared50ModularControl.prime_prime.pos _) (pow_pos Shared50ModularControl.prime_prime.pos _))
  have size (k : ℕ) : k.size ≤ k := Nat.size_le.mpr Nat.lt_two_pow_self
  have cw := Nat.mul_le_mul_left (w+1) rankBound
  rw [← width,Nat.mul_comm] at cw
  change _ ≤ 5000*V
  have := size M
  have := size suffix
  have := size (w+1)
  have := size (CopyChildLayout.spectators child)
  omega

/-- Prepare and dispatch a packed MOVE from the caller's cutoff. Only the
above-cutoff branch requires a child execution witness. -/
theorem packedMixedMoveCall [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (workerPorts : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (capacity : columnCapacity ≤ Q)
    (rank : ℕ) (positive : 0 < rank) (bound : rank ≤ 64)
    {N H : ℕ} (record : Fin 35 ↪ Fin N) (host : Fin (N+(T+273)) ↪ Fin H) :
    let parent := record.trans ((Fin.castAddEmb (T+273)).trans host)
    let payload := ((scheduledRecordPorts workerPorts) 24).castAdd 273
    let stage := (Record.payloadBank (record 24) payload).trans host
    let worker := (Fin.castAddEmb 273 (n := T)).trans stage
    let ports := workerPorts.trans worker
    let cut := parent 34
    let headers := fun i j => stage (borrowedHeaders T i j)
    ∃ leaf : Pr P H Q prime U, ∀ (body : P → Pr P H Q prime U) (large f : P), body f = leaf →
    let localPort := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let bank := localPort.trans ports
    ∃ code, ∀ (node desc : Descriptor) (w W L cutoff recursiveTime : ℕ),
    let M := prime^(w+1)
    let suffix := M^112*W
    desc.width = (w+1)*rank → cutoff < 2^L → desc.width.size ≤ L → L ≤ 64*(w+1) → 0 < W → ∀ (position : Fin (volume prime desc) ≃ Fin (M^16*suffix))
      (x : Fin (M^16*suffix) → ZMod 2) (u : HS H Q prime U) (S : Stacks H prime), desc.width < node.width →
    (∀ h, (position h).val = (CopyChildLayout.packActive desc h).val) → S.R cut = binSyms L cutoff → S.R (bank 34) = [] →
    (∀ i j, S.R (headers i j) = (Routines.hdr (helperAdjacentView (w+1) 1 W i) j).map bitSymbol) →
    (∀ i : Fin 35, i ≠ 24 → i ≠ 34 → S.L (bank i) = [] ∧ S.R (bank i) = []) →
    (∀ i : Fin (rowSwapBlock.tapes+35), 35 ≤ i.val → S.L (ports i) = [] ∧ S.R (ports i) = []) →
    (∀ z, readAt blank (S.L (parent 24)) (S.R (parent 24)) z = RadixToBinary.binaryEncoding.encode
      (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ x)) z)) →
    let core : ℝ := (LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|)
    ∀ rate : ℝ, 163+core ≤ rate →
    let budget := ⌊(rate*(desc.width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime desc⌋₊
    let active := cutoff < desc.width
    let price := if active then recursiveTime else budget
    (active → ScheduledChildExec node desc w suffix ports (binSyms L cutoff) position body large recursiveTime) →
    ∃ z F t y, Exec body code (mk u S) t (mk z F) ∧
      t ≤ 5000*volume prime desc+price ∧ z.user = u.user ∧
      (∀ k ∈ ([2,27,28,32,33,34] : List (Fin 35)), F.R (bank k) = []) ∧
      (∀ z, readAt blank (F.L (parent 24)) (F.R (parent 24)) z = RadixToBinary.binaryEncoding.encode
        (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ y)) z)) ∧
      (∀ i : Fin (rowSwapBlock.tapes+35), 35 ≤ i.val → F.L (ports i) = [] ∧ F.R (ports i) = []) ∧
      (∀ j, (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
      (∀ H J, let caller := RecordReady (b := prime) (w := w) (d := 16) (W := suffix) parent H J (binSyms L cutoff) SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
        caller x S → caller y F) ∧
      ∀ h, y (position h) = Shared50RecursiveNodeRows.transpose (one_dvd desc.rows) (x ∘ position) h := by
  intro parent payload stage worker ports cut headers
  have shared : scheduledRecordPorts ports 24 = parent 24 := congrArg host (Record.payloadBank_shared (record 24) payload)
  have apartParent (i : Fin T) (j : Fin 35) (hj : j ≠ 24) : stage (i.castAdd 273) ≠ parent j := by
    change host (Record.payloadBank (record 24) payload (i.castAdd 273)) ≠ host ((record j).castAdd _)
    apply host.injective.ne
    by_cases eq : i.castAdd 273 = payload
    · rw [eq,Record.payloadBank_shared]
      exact (Fin.castAddEmb _).injective.ne (record.injective.ne hj.symm)
    · rw [Record.payloadBank_private _ _ _ eq]
      intro same
      have h := congrArg Fin.val same
      simp only [Fin.val_natAdd,Fin.val_castAdd] at h
      have := (record j).isLt
      omega
  have cutOff (i) : ports i ≠ cut := apartParent (workerPorts i) 34 (by decide)
  have apart (i j k) : headers i j ≠ ports k := by
    intro eq
    exact borrowedHeaders_apart i j (workerPorts k) (stage.injective eq)
  obtain ⟨leaf,move⟩ := stoppedMoveProgram (P := P) (U := U) ports capacity rank positive
  refine ⟨leaf,?_⟩
  intro body large f installed localPort bank
  let i : Fin 127 := ⟨2*rank-2,by omega⟩
  obtain ⟨prepare,setup⟩ := prepareWorkerRecord_exec body bank headers (fun i j k => apart i j (localPort k))
  obtain ⟨dispatch,call⟩ := moveCutoffCall body large f ports cut (headers i 5) cutOff (fun k => (apart i 5 k).symm) rank
  let fields : List (Fin 35) := [2,27,28,32,33]
  let controls := fields.map bank
  refine ⟨prepare.seq (dispatch.seq (Mult.ShortConv.clearWords controls)),?_⟩
  intro node desc w W L cutoff recursiveTime M suffix width cutFits fits precision pos position x u S smaller coords header archive ready empty clean payload core rate room budget active price recurse
  let digits := if active then L else (CopyChildLayout.spectators desc).size
  obtain ⟨v,D,m,user,run,cost,stored,left,off⟩ := setup w W x u S ready empty (by simpa only [show bank 24 = parent 24 from shared] using payload)
  rw [archive] at stored
  have size := Fintype.card_congr position
  simp only [Fintype.card_fin] at size
  have spectator := ((off (headers i 5) (fun k => (apart i 5 (localPort k)).symm)).trans (ready i 5)).trans
    (moveSpectatorHeader desc w W rank positive bound width size)
  have clear (j : Fin (rowSwapBlock.tapes+35)) (hj : 35 ≤ j.val) : D.L (ports j) = [] ∧ D.R (ports j) = [] := by
    have outside (k : Fin 35) : bank k ≠ ports j := by
      intro eq
      change ports (localPort k) = ports j at eq
      have h := congrArg Fin.val (ports.injective eq)
      change k.val = j.val at h
      omega
    exact ⟨(congrFun left _).trans (clean j hj).1,(off _ outside).trans (clean j hj).2⟩
  obtain ⟨z,F,n,y,exec,paid,same,out,free,frame,read⟩ := call node desc w suffix L cutoff recursiveTime budget position
    width cutFits fits recurse (fun _ => move body f installed node desc w suffix width position coords
      (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) pos) rate room)
    smaller v D x ((off cut (fun k => cutOff (localPort k))).trans header) spectator stored clear
  have keep (j) (outside : ∀ i, ports i ≠ j) : F.L j = S.L j ∧ F.R j = S.R j :=
    ⟨(frame j outside).1.trans (congrFun left j),(frame j outside).2.trans (off j (fun k => outside (localPort k)))⟩
  obtain ⟨q,final,erase⟩ := retireWorkerControls body bank w suffix [] y z F out
  let G := {F with R := fun k => if k ∈ controls then [] else F.R k}
  have untouched (j) (away : ∀ k ∈ fields, bank k ≠ j) : G.R j = F.R j := by
    apply ite_eq_right
    intro mem
    obtain ⟨k,hk,eq⟩ := List.mem_map.mp mem
    exact away k hk eq
  have preserved (j) (outside : ∀ i, ports i ≠ j) : G.L j = S.L j ∧ G.R j = S.R j :=
    ⟨(keep j outside).1,(untouched j (fun k _ => outside (localPort k))).trans (keep j outside).2⟩
  have payloadAt : G.R (parent 24) = F.R (parent 24) := by
    apply untouched
    intro k hk
    rw [← shared]
    exact bank.injective.ne (fun eq => (by decide : (24 : Fin 35) ∉ [2,27,28,32,33]) (eq ▸ hk))
  have result z := out.src z
  simp only [shared,sub_zero] at result
  refine ⟨q,G,_,y,Exec.seq run (Exec.seq exec erase),?_,final.trans (same.trans user),?_,?_,?_,preserved,?_,read⟩
  · change m ≤ 14*M.size+6*suffix.size+6*(w+1)+11*(w+1).size+50 at cost
    change n ≤ price+8*digits+4*w+23*desc.width+22*L+61 at paid
    have overhead := moveOverhead_volume desc w W rank L digits pos bound width precision
      (by dsimp only [digits]; split <;> first | exact le_max_left .. | exact le_max_right ..) size
    change 18*M.size+8*suffix.size+6*(w+1)+11*(w+1).size+124+8*digits+6*w+23*desc.width+22*L ≤ _ at overhead
    change m+(n+(2*(2*M.size+suffix.size+w)+13)) ≤ _
    omega
  · intro k hk
    by_cases h : k ∈ fields
    · exact ite_eq_left (List.mem_map.mpr ⟨k,h,rfl⟩)
    · have eq : k = 34 := by simp [fields] at h hk; tauto
      subst k
      exact (untouched (bank 34) (fun k hk => bank.injective.ne (fun eq => h (eq ▸ hk)))).trans out.archive
  · intro z
    rw [payloadAt]
    exact result z
  · intro k hk
    refine ⟨(free k hk).1,(untouched _ ?_).trans (free k hk).2⟩
    intro j _ eq
    change ports (localPort j) = ports k at eq
    have val := congrArg Fin.val (ports.injective eq)
    change j.val = k.val at val
    omega
  · intro H J caller start
    apply start.returnPayload (fun j hj => preserved (parent j) (fun k => apartParent (workerPorts k) j hj))
    intro z
    rw [payloadAt,sub_zero]
    exact (result z).symm

/-- Compute the worker tag from its predecessor clock and an external cutoff
word, then prepend it to the archive. The comparison restores all its tapes. -/
theorem prepareWorkerTag {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin 35 ↪ Fin T) (cut : Fin T) (off : ∀ i, bank i ≠ cut) (rank : ℕ) :
    ∃ code, ∀ (w W L cutoff : ℕ) (record : List (Fin (prime+4)))
      (word : Fin ((prime^(w+1))^16*W) → ZMod 2) (u : HS T Q prime U) (S : Stacks T prime),
      cutoff < 2^L → ((w+1)*rank).size ≤ L → S.R cut = binSyms L cutoff →
      let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) bank (prime^(w+1)).size W.size
      let tag : Fin (prime+4) := bitSymbol (decide (cutoff < (w+1)*rank))
      let F := {S with R := Function.update S.R (bank 34) (tag :: record)}
      stored record SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 word S →
      ∃ z n, Exec body code (mk u S) n (mk z F) ∧ z.user = u.user ∧
        n ≤ 4*w+23*((w+1)*rank)+22*L+51 ∧
        stored (tag :: record) SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 word F := by
  let cmp := ordinaryCutoffPorts bank cut off
  let push : Pr P T Q prime U := .act (.push (.rt (bank 34)) (fun v => v.scan (cmp 7)) .done)
  refine ⟨(ordinaryCutoffTest cmp rank).seq push,?_⟩
  intro w W L cutoff record word u S cutFits fits header stored tag F ready
  have scratch : ∀ k : Fin 10, 2 ≤ k.val → cutoffColumnSlots k ∈ shearWork := by decide
  have clear (k : Fin 10) (hk : 2 ≤ k.val) : S.R (cmp k) = [] := by
    have ne : k ≠ 1 := by intro eq; subst k; contradiction
    simpa [cmp,ordinaryCutoffPorts,ne] using (ready.scratch _ (scratch k hk)).2
  obtain ⟨z,n,user,flag,paid,test⟩ := ordinaryCutoffTest_exec body cmp rank w L cutoff cutFits fits u S
    ready.clock (by simpa [cmp,ordinaryCutoffPorts] using header) clear
  have append : Exec body push (mk z S) 1 (mk z F) := by
    apply (Exec.act _ _).cast rfl
    simp [Action.run,F,tag,update_rt,flag,ready.archive]
  exact ⟨z,_,Exec.seq test append,user,by omega,replaceArchive bank _ _ _ _ ready⟩

/-- COPY accepts arbitrary archive contents. With the cutoff itself as
the archive, its worker can compare and branch in place. -/
theorem archiveCutoffDispatch [M8.Machine.Net] {P U : Type} {T Q : ℕ}
    (body : P → Pr P T Q prime U) (entry large leaf : P)
    (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (rank : ℕ) :
    let bank := scheduledRecordPorts ports
    let cmp := cutoffColumnSlots.trans bank
    body entry = (ordinaryCutoffTest cmp rank).seq
      (.cond (fun z => symBit (z.scan (cmp 7))) (body large) (body leaf)) →
    ∀ (node child : Descriptor) (w W L cutoff price : ℕ),
      child.width = (w+1)*rank → cutoff < 2^L → child.width.size ≤ L →
      ∀ position : Fin (volume prime child) ≃ Fin ((prime^(w+1))^16*W),
      let worker := ScheduledChildExec node child w W ports (binSyms L cutoff) position body
      worker (if cutoff < child.width then large else leaf) price →
      worker entry (4*w+23*child.width+22*L+51+price) := by
  intro bank cmp installed node child w W L cutoff price width cutFits fits position worker branch smaller u S word ready clean
  have scratch : ∀ k : Fin 10, 2 ≤ k.val → cutoffColumnSlots k ∈ shearWork := by decide
  obtain ⟨v,m,user,flag,paid,test⟩ := ordinaryCutoffTest_exec body cmp rank w L cutoff cutFits
    (width ▸ fits) u S ready.clock ready.archive (fun k hk => (ready.scratch _ (scratch k hk)).2)
  obtain ⟨z,F,n,y,run,cost,same,out,free,frame,read⟩ := branch smaller v S word ready clean
  have select : Exec body (.cond (fun z => symBit (z.scan (cmp 7))) (body large) (body leaf))
      (mk v S) (n+1) (mk z F) := by
    rw [← width] at flag
    by_cases active : cutoff < child.width
    · exact Exec.cond_true (by simp [mk_var,flag,active]) (by simpa [active] using run)
    · exact Exec.cond_false (by simp [mk_var,flag,active]) (by simpa [active] using run)
  refine ⟨z,F,_,y,installed ▸ Exec.seq test select,?_,same.trans user,out,free,frame,read⟩
  rw [← width] at paid
  omega

noncomputable def scheduledDispatch {T Q : ℕ} {P U : Type} (archive : Fin T) (large leaf : Pr P T Q prime U) : Pr P T Q prime U :=
  let select := Prog.act (.pop (.rt archive) (fun v o => { v with flag := symBit (o.getD blank) }) .done)
  let restore := fun b => Prog.act (.push (.rt archive) (fun _ => bitSymbol b) .done)
  select.seq (.cond (·.flag) (large.seq (restore true)) (leaf.seq (restore false)))

/-- The branch sees its original record. The caller gets its tagged record back
with three steps charged for reading, selecting and restoring the tag. -/
theorem scheduledDispatch_exec [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (body : P → Pr P T Q prime U) (entry large leaf : P)
    (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T)
    (installed : body entry = scheduledDispatch (scheduledRecordPorts ports 34) (body large) (body leaf))
    (node child : Descriptor) (w W cutoff : ℕ) (record : List (Fin (prime+4)))
    (position : Fin (volume prime child) ≃ Fin ((prime^(w+1))^16*W)) (price : ℕ)
    (branch : ScheduledChildExec node child w W ports record position body
      (if cutoff < child.width then large else leaf) price) :
    ScheduledChildExec node child w W ports (bitSymbol (decide (cutoff < child.width)) :: record)
      position body entry (price+3) := by
  intro smaller u S word ready clean
  let bank := scheduledRecordPorts ports
  let active := decide (cutoff < child.width)
  let src := bank 34
  let D := {S with R := Function.update S.R src record}
  let v := {u with flag := active}
  have pop : Exec body (.act (.pop (.rt src) (fun v o => {v with flag := symBit (o.getD blank)}) .done))
      (mk u S) 1 (mk v D) := by
    apply (Exec.act _ _).cast rfl
    simp [Action.run,src,bank,ready.archive,v,D,active,update_rt]
  have off (j : Fin (rowSwapBlock.tapes+35)) (hj : 35 ≤ j.val) : ports j ≠ src := by
    intro eq
    have h := congrArg Fin.val (ports.injective eq)
    change j.val = 34 at h
    omega
  obtain ⟨z,F,t,y,run,paid,user,out,free,frame,read⟩ := branch smaller v D word
    (replaceArchive bank _ _ _ _ ready) (fun j hj => ⟨(clean j hj).1,(Function.update_of_ne (off j hj) ..).trans (clean j hj).2⟩)
  let G := {F with R := Function.update F.R src (bitSymbol active :: record)}
  have push : Exec body (.act (.push (.rt src) (fun _ => bitSymbol active) .done)) (mk z F) 1 (mk z G) := by
    apply (Exec.act _ _).cast rfl
    simp [Action.run,G,src,bank,out.archive,update_rt]
  refine ⟨z,G,1+(t+1+1),y,?_,by omega,user,replaceArchive bank _ _ _ _ out,?_,?_,read⟩
  · rw [installed]
    apply Exec.seq pop
    by_cases above : cutoff < child.width
    · apply Exec.cond_true (by simp [mk_var,v,active,above])
      simp only [active,above,decide_true,ite_true] at run push ⊢
      exact Exec.seq run push
    · apply Exec.cond_false (by simp [mk_var,v,active,above])
      simp only [active,above,decide_false,ite_false] at run push ⊢
      exact Exec.seq run push
  · intro j hj
    exact ⟨(free j hj).1,(Function.update_of_ne (off j hj) ..).trans (free j hj).2⟩
  · intro j away
    have ne : j ≠ src := (away ⟨34,by omega⟩).symm
    have keep := frame j away
    exact ⟨keep.1,(Function.update_of_ne ne ..).trans (keep.2.trans (Function.update_of_ne ne ..))⟩

/-- The MOVE table installs a single dispatcher per rank. Only the branch
above the cutoff needs a recursive execution witness. -/
theorem mixedMoveProgram [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (capacity : columnCapacity ≤ Q)
    (rank : ℕ) (positive : 0 < rank) :
    ∃ leafCode : Pr P T Q prime U, ∀ (body : P → Pr P T Q prime U) (entry large leaf : P),
      body leaf = leafCode →
      body entry = scheduledDispatch (scheduledRecordPorts ports 34) (body large) leafCode →
      ∀ (node child : Descriptor) (w W cutoff : ℕ), child.width = (w+1)*rank →
      ∀ position : Fin (volume prime child) ≃ Fin ((prime^(w+1))^16*W),
      (∀ i, (position i).val = (CopyChildLayout.packActive child i).val) → 0 < W →
      let core : ℝ := (LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|)
      ∀ (rate : ℝ) (recursiveTime : ℕ) (recursiveRecord : List (Fin (prime+4))), 163+core ≤ rate →
      let active := cutoff < child.width
      let record := if active then recursiveRecord else
        binSyms (CopyChildLayout.spectators child).size (CopyChildLayout.spectators child)
      let price := if active then recursiveTime else
        ⌊(rate*(child.width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime child⌋₊
      (active → ScheduledChildExec node child w W ports recursiveRecord position body large recursiveTime) →
      ScheduledChildExec node child w W ports (bitSymbol (decide active)::record) position body entry (price+3) := by
  obtain ⟨code,stopped⟩ := stoppedMoveProgram (P := P) (U := U) ports capacity rank positive
  refine ⟨code,?_⟩
  intro body entry large leaf installed dispatch node child w W cutoff width position packed pos core rate time archive room active record price recurse
  apply scheduledDispatch_exec body entry large leaf ports (installed ▸ dispatch) node child w W cutoff
  by_cases h : cutoff < child.width
  · simpa only [record,price,active,ite_eq_left h] using recurse h
  · simpa only [record,price,active,ite_eq_right h] using
      stopped body leaf installed node child w W width position packed pos rate room

open Certificates.PR589

/-- COPY uses its archive as the persistent cutoff. Only above-cutoff
children need an execution witness; the stopped program accepts this archive. -/
theorem cutoffCopyProgram [M8.Machine.Net] :
    ∃ C : ℝ, ∀ {P U : Type} {T Q : ℕ} (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T)
      (fits : stoppedCopyMachine.1 ≤ Q) (body : P → Pr P T Q prime U) (entry large leaf : P),
      body leaf = stoppedCopyProgram ports fits →
      let cmp := cutoffColumnSlots.trans (scheduledRecordPorts ports)
      body entry = (ordinaryCutoffTest cmp 7).seq
        (.cond (fun z => symBit (z.scan (cmp 7))) (body large) (body leaf)) →
      ∀ (node : Descriptor) (n : Fin 9) (p : Fin 32 × Fin 5) (j : Fin Copy.lifecycles.length)
        (w W rows L cutoff : ℕ), node.width = 64*(w+1) → node.rows = 142080*rows →
      let child := scheduledChild prime node (copyChildPosition (n,p,j))
      cutoff < 2^L → child.width.size ≤ L →
      ∀ position : Fin (volume prime child) ≃ Fin ((prime^(w+1))^16*W),
      CopyIntervalPositions child (w+1) W position → 0 < W →
      ∀ (rate : ℝ) (recursiveTime : ℕ), C ≤ rate →
      let worker := ScheduledChildExec node child w W ports (binSyms L cutoff) position body
      let price := if cutoff < child.width then recursiveTime else
        ⌊(rate*(child.width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime child⌋₊
      (cutoff < child.width → worker large recursiveTime) →
      worker entry (4*w+23*child.width+22*L+51+price) := by
  obtain ⟨C,stopped⟩ := stoppedCopyChild_budget
  refine ⟨C,?_⟩
  intro P U T Q ports fits body entry large leaf installed cmp dispatch node n p j w W rows L cutoff width split child cutFits room position coords pos rate time enough worker price recurse
  have size := (scheduledChild_measures prime node ⟨_,width⟩ ⟨_,split⟩ (copyChildPosition (n,p,j))).1
  rw [copyChildPosition_rank n p.1 p.2 j,width] at size
  change child.width*64 = _ at size
  apply archiveCutoffDispatch body entry large leaf ports 7 dispatch node child w W L cutoff price (by omega) cutFits room position
  by_cases active : cutoff < child.width
  · simpa only [price,ite_eq_left active] using recurse active
  · simpa only [price,ite_eq_right active] using
      stopped ports fits body leaf installed node n p j w W rows width split _ position coords pos rate enough

-- The tagged COPY variant is available in 337331f6.

/-- Labels private to a mixed worker, with the recursive procedure's labels
embedded in the active branch. -/
inductive WorkerLabel (P : Type)
  | entry | leaf | active (f : P)

noncomputable def workerTable {P U : Type} {T Q : ℕ} (dispatch : Pr (WorkerLabel P) T Q prime U → Pr (WorkerLabel P) T Q prime U → Pr (WorkerLabel P) T Q prime U)
    (leaf : Pr (WorkerLabel P) T Q prime U) (large : P → Pr (WorkerLabel P) T Q prime U)
    (f : P) : WorkerLabel P → Pr (WorkerLabel P) T Q prime U
  | .entry => dispatch (large f) leaf
  | .leaf => leaf
  | .active g => large g

/-- Install mixed workers throughout the stage. The stage needs execution
witnesses only for the occurrences above the cutoff. -/
theorem mixedPackedSweep [M8.Machine.Net] (n : Fin 9) :
    ∃ (mt : StageRun → MoveIndex → ℕ) (ct : StageRun → CopyIndex → ℕ)
      (mr : ∀ p i, Fin (rowSwapBlock.tapes+35) ↪ Fin (mt p i))
      (cr : ∀ p j, Fin (rowSwapBlock.tapes+35) ↪ Fin (ct p j)) (states : ℕ) (leafRate : ℝ),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q →
    ∀ (ml : ∀ p i, P → Pr (WorkerLabel P) (mt p i) Q prime U) (mf : StageRun → MoveIndex → P)
      (cl : ∀ p j, P → Pr (WorkerLabel P) (ct p j) Q prime U) (cf : StageRun → CopyIndex → P),
    ∃ (mb : ∀ p i, WorkerLabel P → Pr (WorkerLabel P) (mt p i) Q prime U)
      (cb : ∀ p j, WorkerLabel P → Pr (WorkerLabel P) (ct p j) Q prime U) (coeff : StageRun → ℝ),
      (∀ p i f, mb p i (.active f) = ml p i f) ∧ (∀ p j f, cb p j (.active f) = cl p j f) ∧
      ∀ (node : Descriptor) (w B rows cutoff : ℕ), node.width = 64*(w+1) → node.rows = 142080*rows →
      node.beforeH = B*prime^(64*((w+1)*64)) →
      let K := node.beforeRows*rows*node.between*node.afterD
      let W := ((prime^(w+1))^112*B)*prime^(64*((w+1)*64))*K
      0 < W → ∀ rate : ℝ, leafRate ≤ rate →
      let mi := fun (p : StageRun) (i : MoveIndex) => phaseChildPositions.choose (n,p,i)
      let ci := fun (p : StageRun) (j : CopyIndex) => copyChildPosition (n,p,j)
      let child := scheduledChild prime node
      ∀ (record : Fin nodeChildren5.length → List (Fin (prime+4))) (budget : Fin nodeChildren5.length → ℕ),
      ∀ L : ℕ, cutoff < 2^L → (∀ p j, (child (ci p j)).width.size ≤ L) →
      let price := fun i => if cutoff < (child i).width then budget i else
        ⌊(rate*((child i).width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime (child i)⌋₊
      ∃ (mp : ∀ p i, Fin (volume prime (child (mi p i))) ≃ Fin ((prime^(w+1))^16*W))
        (cp : ∀ p j, Fin (volume prime (child (ci p j))) ≃ Fin ((prime^(w+1))^16*W)),
      (∀ p i h, (mp p i h).val = (CopyChildLayout.packActive (child (mi p i)) h).val) ∧
      (∀ p j, CopyIntervalPositions (child (ci p j)) (w+1) W (cp p j)) ∧
      ∃ (Label : Type) (tapes : StageRun → ℕ) (body : ∀ p, Label → Pr Label (tapes p) Q prime U),
        PackedStageExecution (w := w+1) (B := B) (K := K) n tapes body coeff (fun time =>
          ((∀ p i, time (mi p i).val = price (mi p i)+3) ∧
           (∀ p j, let k := ci p j; time k.val = 4*w+23*(child k).width+22*L+51+price k)) ∧
          (∀ p i, let k := mi p i; cutoff < (child k).width →
            ScheduledChildExec node (child k) w W (mr p i) (record k) (mp p i) (mb p i) (.active (mf p i)) (budget k)) ∧
          (∀ p j, let k := ci p j; cutoff < (child k).width →
            ScheduledChildExec node (child k) w W (cr p j) (binSyms L cutoff) (cp p j) (cb p j) (.active (cf p j)) (budget k))) := by
  classical
  obtain ⟨mt,ct,mr,cr,mT,cT,mBank,cBank,states,build⟩ := scheduledInvocationFamily n
  obtain ⟨copyRate,copy⟩ := cutoffCopyProgram
  let core : ℝ := (LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|)
  refine ⟨mt,ct,mr,cr,max states (max columnCapacity stoppedCopyMachine.1),max (163+core) copyRate,?_⟩
  intro P U Q room ml mf cl cf
  have caps := (le_max_right _ _).trans room
  let mi := fun (p : StageRun) (i : MoveIndex) => phaseChildPositions.choose (n,p,i)
  let ci := fun (p : StageRun) (j : CopyIndex) => copyChildPosition (n,p,j)
  choose leaf move using fun (p : StageRun) (i : MoveIndex) =>
    mixedMoveProgram (P := WorkerLabel P) (U := U) (mr p i) ((le_max_left _ _).trans caps)
      (nodeChildren5[(mi p i).val]) (nodeChildren5_bounds (mi p i)).1
  let mb := fun p i => workerTable (scheduledDispatch (scheduledRecordPorts (mr p i) 34)) (leaf p i) (ml p i) (mf p i)
  let cb := fun p j => let cmp := cutoffColumnSlots.trans (scheduledRecordPorts (cr p j))
                       workerTable (fun large leaf => (ordinaryCutoffTest cmp 7).seq (.cond (fun z => symBit (z.scan (cmp 7))) large leaf))
                         (stoppedCopyProgram (cr p j) ((le_max_right _ _).trans caps)) (cl p j) (cf p j)
  obtain ⟨coeff,stage⟩ := build ((le_max_left _ _).trans room) mb (fun _ _ => .entry) cb (fun _ _ => .entry)
  refine ⟨mb,cb,coeff,fun _ _ _ => rfl,fun _ _ _ => rfl,?_⟩
  intro node w B rows cutoff width split label K W pos rate large _ _ child record budget L cutFits copyFits price
  let active := fun k => cutoff < (child k).width
  let mrec := fun p i => let k := mi p i; let s := CopyChildLayout.spectators (child k)
                         bitSymbol (decide (active k)) :: (if active k then record k else binSyms s.size s)
  let crec := fun (_ : StageRun) (_ : CopyIndex) => binSyms (A := prime) L cutoff
  obtain ⟨mp,cp,banks,mc,cc,T,fan,bank,run⟩ := stage node w B rows width split label pos mrec crec
  refine ⟨mp,cp,mc,cc,_,fun p => (banks p).tapes,fun p => (banks p).body (mBank p) (cBank p) (mb p) (cb p),T,fan,bank,?_⟩
  intro scratch owner worker host blocks V time ready
  apply run time
  constructor
  · intro p i
    rw [ready.1.1 p i]
    have shape : (child (mi p i)).width = (w+1)*nodeChildren5[(mi p i).val] := by
      change nodeChildren5[(mi p i).val]*(node.width/64) = _
      rw [width,Nat.mul_div_cancel_left _ (by decide),Nat.mul_comm]
    exact move p i (mb p i) .entry (.active (mf p i)) .leaf rfl rfl node _ w W cutoff shape
      (mp p i) (mc p i) pos rate _ _ ((le_max_left _ _).trans large) (ready.2.1 p i)
  · intro p j
    rw [ready.1.2 p j]
    exact copy (cr p j) _ (cb p j) .entry (.active (cf p j)) .leaf rfl rfl node n p j w W rows L cutoff
      width split cutFits (copyFits p j) (cp p j) (cc p j) pos rate _ ((le_max_right _ _).trans large) (ready.2.2 p j)

end IntegerMultBounds.MathlibTM2.M6.BitNode
