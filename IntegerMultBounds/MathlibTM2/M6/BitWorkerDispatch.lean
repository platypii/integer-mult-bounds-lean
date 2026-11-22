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

/-- Produce the sweep's helper headers inside a caller placement. Every
tape outside the archive producer retains both stacks, including a shared
payload or cutoff on the surrounding host. -/
theorem placedMoveHeaders {H Q : ℕ} {P U : Type}
    (e : Fin (80+273) ↪ Fin H) (body : P → Pr P H Q prime U)
    (capacity : (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q) :
    ∃ code, ∀ (node : Descriptor) (w B rows : ℕ),
      node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
      ({node with rows := rows} : Descriptor).Positive →
      let W := node.beforeRows*rows*node.beforeH*node.between*node.afterD
      let M := prime^(w+1)
      ∀ u S, ParentArchiveInput node w (embStk e S) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        t ≤ ((RecursiveRowsQuotient.constant 142080+30)*142080*43+152402152)*(M^16*(M^112*W)) ∧
        (∀ i j, F.R (e (borrowedHeaders 80 i j)) =
          (Routines.hdr (helperAdjacentView (w+1) 1 W i) j).map bitSymbol) ∧
        ∀ j, (∀ k, e k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  let slots := Fin.castAddEmb 42 (n := 38)
  let hdr := (Fin.natAddEmb 38 (m := 6)).trans (Fin.castAddEmb 36)
  let tmp := (44 : Fin 80)
  let regs := Fin.natAddEmb 45 (m := 35)
  obtain ⟨prog,prepare⟩ := parentRoleArchive_exec (P := Empty) (U := U) Empty.elim slots hdr tmp regs
    (by intro i j eq; have h := congrArg Fin.val eq; change i.val = 38+j.val at h; omega)
    (by intro i eq; have h := congrArg Fin.val eq; change i.val = 44 at h; omega)
    (by intro j eq; have h := congrArg Fin.val eq; change 44 = 38+j.val at h; omega)
    (by intro i j eq; have h := congrArg Fin.val eq; change i.val = 45+j.val at h; omega)
    (by intro i j eq; have h := congrArg Fin.val eq; change 38+i.val = 45+j.val at h; omega) capacity
  refine ⟨embProg e Empty.elim prog,?_⟩
  intro node w B rows width split label pos W M u S input
  obtain ⟨rep,tl,tr,empty,base,unit,clock,free⟩ := input
  obtain ⟨v,D,t,user,run,bill,headers,_⟩ := prepare node w B rows width split label pos (embDn e u) (embStk e S)
    rep tl tr empty base unit clock free
  obtain ⟨z,F,exec,_,same,view,off⟩ := exec_emb (body' := body) (ι := Empty.elim) e.injective (fun f => nomatch f)
    run u rfl S rfl
  have eq : B*prime^(64*((w+1)*64))*(node.beforeRows*rows*node.between*node.afterD) = W := by
    dsimp only [W]; rw [label]; ring
  refine ⟨z,F,t,exec,same.trans user,?_,?_,off⟩
  · rw [← eq]
    convert bill using 1
    dsimp only [M]
    ring
  · intro i j
    exact (congrArg (fun X => Stacks.R X (borrowedHeaders 80 i j)) view).trans (by simpa only [eq] using headers i j)

/-- The private stacks read by one scheduled MOVE before dispatch. Port
24 belongs to the live payload and may have changed since initialization. -/
def MovePrivateStock {H K : ℕ} (archive : Fin (80+273) ↪ Fin H) (ports : Fin K ↪ Fin H)
    (seed S : Stacks H prime) : Prop :=
  (∀ k, S.L (archive k) = seed.L (archive k) ∧ S.R (archive k) = seed.R (archive k)) ∧
  ∀ k : Fin K, k.val ≠ 24 → S.L (ports k) = seed.L (ports k) ∧ S.R (ports k) = seed.R (ports k)

/-- A completed occurrence preserves a later occurrence's stock whenever
its writes miss that occurrence's archive and private ports. -/
theorem MovePrivateStock.frame {H K : ℕ} {archive : Fin (80+273) ↪ Fin H} {ports : Fin K ↪ Fin H}
    {seed S F : Stacks H prime} (stock : MovePrivateStock archive ports seed S)
    (untouched : Fin H → Prop) (keep : ∀ j, untouched j → F.L j = S.L j ∧ F.R j = S.R j)
    (archiveFree : ∀ k, untouched (archive k)) (privateFree : ∀ k : Fin K, k.val ≠ 24 → untouched (ports k)) :
    MovePrivateStock archive ports seed F := by
  constructor
  · intro k
    have h := keep _ (archiveFree k)
    exact ⟨h.1.trans (stock.1 k).1,h.2.trans (stock.1 k).2⟩
  · intro k hk
    have h := keep _ (privateFree k hk)
    exact ⟨h.1.trans (stock.2 k hk).1,h.2.trans (stock.2 k hk).2⟩

open Certificates.PR589

/-- Pair each paid MOVE with the scalar gates since the previous MOVE.
The second component holds the gates after the final paid edge. -/
noncomputable def phaseMoveBlocks : List RawGate → (ℕ → ℕ) →
    List (List RawGate × (ℕ × ℕ)) × List RawGate
  | [], _ => ([], [])
  | g :: gs, current =>
    let moves := ((Frames.edges [g] current).filter positiveMove).map fun edge => ([],edge)
    let (blocks,suffix) := phaseMoveBlocks gs (Frames.run [g] current)
    match blocks with
    | [] => (moves,g :: suffix)
    | (gates,edge) :: rest => (moves ++ (g :: gates,edge) :: rest,suffix)

/-- Projecting the block schedule recovers every original scalar gate
and exactly the positive-rank edge list, both in execution order. -/
theorem phaseMoveBlocks_spec (gs : List RawGate) (current : ℕ → ℕ) :
    let (blocks,suffix) := phaseMoveBlocks gs current
    blocks.map Prod.snd = (Frames.edges gs current).filter positiveMove ∧
      blocks.flatMap Prod.fst ++ suffix = gs := by
  induction gs generalizing current with
  | nil => exact ⟨rfl,rfl⟩
  | cons g gs ih =>
    have edges := Frames.edges_append [g] gs current
    simp only [List.singleton_append] at edges
    have emptyBlocks (es : List (ℕ × ℕ)) :
        (es.map (fun e => (([] : List RawGate),e))).flatMap Prod.fst = [] := by
      induction es with
      | nil => rfl
      | cons _ _ ih => simpa only [List.map_cons,List.flatMap_cons,List.nil_append] using ih
    have tail := ih (Frames.run [g] current)
    cases eq : phaseMoveBlocks gs (Frames.run [g] current) with
    | mk blocks suffix =>
      rw [eq] at tail
      cases blocks with
      | nil =>
        obtain ⟨moveOrder,gateOrder⟩ := tail
        change suffix = gs at gateOrder
        simp [phaseMoveBlocks,eq,edges,List.filter_append,Function.comp_def,← moveOrder,gateOrder,emptyBlocks]
      | cons head rest =>
        obtain ⟨gates,edge⟩ := head
        obtain ⟨moveOrder,gateOrder⟩ := tail
        simp only [List.map_cons,List.flatMap_cons,List.append_assoc] at moveOrder gateOrder
        simp [phaseMoveBlocks,eq,edges,List.filter_append,Function.comp_def,← moveOrder,gateOrder,List.append_assoc,emptyBlocks]

/-- Every block selected by its MOVE occurrence, and the final suffix,
can be passed directly to the selected-word gate compiler. -/
theorem phaseMoveBlocks_allowed (gs : List RawGate) (current : ℕ → ℕ)
    (allowed : ∀ g ∈ gs, g ∈ program) :
    let schedule := phaseMoveBlocks gs current
    (∀ i : Fin schedule.1.length, ∀ g ∈ schedule.1[i].1, g ∈ program) ∧
      (∀ g ∈ schedule.2, g ∈ program) := by
  have gates := (phaseMoveBlocks_spec gs current).2
  constructor
  · intro i g hg
    apply allowed
    rw [← gates]
    exact List.mem_append_left _ (List.mem_flatMap.mpr
      ⟨_,List.getElem_mem (n := i.val) i.isLt,hg⟩)
  · intro g hg
    apply allowed
    rw [← gates]
    exact List.mem_append_right _ hg

/-- Splitting the scalar word at MOVE boundaries charges every gate once. -/
theorem phaseMoveBlocks_charge (gs : List RawGate) (current : ℕ → ℕ) (charge : RawGate → ℕ) :
    let schedule := phaseMoveBlocks gs current
    (schedule.1.map (fun block => (block.1.map charge).sum)).sum +
      (schedule.2.map charge).sum = (gs.map charge).sum := by
  have sumBlocks (blocks : List (List RawGate × (ℕ × ℕ))) :
      (blocks.map (fun block => (block.1.map charge).sum)).sum =
        ((blocks.flatMap Prod.fst).map charge).sum := by
    induction blocks with
    | nil => rfl
    | cons block rest ih => simp [ih]
  dsimp only
  rw [sumBlocks,← List.sum_append,← List.map_append,(phaseMoveBlocks_spec gs current).2]

/-- The two scalar phases meet at the COPY boundary with precisely the
MOVE order indexed by the invocation directory. -/
theorem invocationMoveBlocks_order :
    let before := phaseMoveBlocks (sectionD ++ sectionA) (Frames.snapshot Frames.initialRefs)
    let after := phaseMoveBlocks (sectionB ++ sectionC) (Frames.scatterFinish Frames.beforeScatter)
    (before.1 ++ after.1).map Prod.snd = Geometry.Moves.phaseEdges.filter positiveMove := by
  dsimp only
  rw [List.map_append,(phaseMoveBlocks_spec _ _).1,(phaseMoveBlocks_spec _ _).1]
  exact (List.filter_append ..).symm

/-- Locate each phase-local MOVE in the worker directory. Positions after
COPY start immediately after the last pre-COPY occurrence. -/
theorem invocationMoveIndices :
    let before := (phaseMoveBlocks (sectionD ++ sectionA) (Frames.snapshot Frames.initialRefs)).1
    let after := (phaseMoveBlocks (sectionB ++ sectionC) (Frames.scatterFinish Frames.beforeScatter)).1
    let edges := Geometry.Moves.phaseEdges.filter positiveMove
    ∃ (pre : Fin before.length → MoveIndex) (post : Fin after.length → MoveIndex),
      (∀ i, (pre i).val = i.val ∧ edges[pre i] = before[i].2) ∧
      (∀ i, (post i).val = before.length+i.val ∧ edges[post i] = after[i].2) := by
  intro before after edges
  have order : (before ++ after).map Prod.snd = edges := invocationMoveBlocks_order
  have size := congrArg List.length order
  simp only [List.length_map,List.length_append] at size
  let pre (i : Fin before.length) : Fin edges.length := ⟨i.val,by rw [← size]; omega⟩
  let post (i : Fin after.length) : Fin edges.length := ⟨before.length+i.val,by rw [← size]; omega⟩
  have atIndex (i : Fin edges.length) :
      edges[i] = ((before ++ after)[i.val]'(by rw [List.length_append,size]; exact i.isLt)).2 := by
    change edges[i.val] = _
    exact (List.getElem_of_eq order.symm i.isLt).trans (List.getElem_map Prod.snd)
  refine ⟨pre,post,fun i => ⟨rfl,?_⟩,fun i => ⟨rfl,?_⟩⟩
  · rw [atIndex, List.getElem_append_left i.isLt]
    rfl
  · rw [atIndex, List.getElem_append_right (show before.length ≤ (post i).val by dsimp [post]; omega)]
    simp [post]

open Certificates.PR589 in
/-- Compile a block of the selected PR589 scalar word on the shared
owner tapes, with the state transition needed between scheduled MOVEs. -/
theorem scalarOwnerBlock {k : ℕ} (owner : Fin 661 ↪ Fin k) :
    ∃ states, ∀ {Q V : ℕ} {U : Type}, states ≤ Q → 0 < V →
    let fan := Function.Embedding.refl (Fin (k+2))
    ∃ effect : (Fin k → Fin V → ZMod 2) → RawGate → Fin k → Fin V → ZMod 2,
      (∀ x g j h, effect x g (owner j) h =
        g.toCircuit.run (Copy.extendStored (fun j => x (owner j) h)) j.val) ∧
      (∀ x g i, (∀ j, owner j ≠ i) → effect x g i = x i) ∧
      ∀ gates : List RawGate, (∀ g ∈ gates, g ∈ program) →
      ∃ code : Pr Empty (k+2) Q prime U, ∀ x u S, HelperFan fan x S →
        ∃ z F n, Exec Empty.elim code (mk u S) n (mk z F) ∧
          n ≤ (gates.map (fun g => 76*g.toCircuit.terms.length*V*(k+7)+6)).sum+1 ∧
          z.user = u.user ∧ HelperFan fan (gates.foldl effect x) F := by
  classical
  obtain ⟨states,build⟩ := scheduledGates_host owner
  refine ⟨states,?_⟩
  intro Q V U capacity pos fan
  let effect := fun (x : Fin k → Fin V → ZMod 2) (g : RawGate) i =>
    if h : ∃ j, owner j = i then fun a =>
      g.toCircuit.run (Copy.extendStored (fun j => x (owner j) a)) h.choose.val else x i
  have atOwner x g j a : effect x g (owner j) a = g.toCircuit.run (Copy.extendStored (fun j => x (owner j) a)) j.val := by
    dsimp only [effect]
    rw [dite_eq_left (show ∃ l, owner l = owner j from ⟨j,rfl⟩)]
    rw [owner.injective (Exists.choose_spec (show ∃ l, owner l = owner j from ⟨j,rfl⟩))]
  have outside x g i (off : ∀ j, owner j ≠ i) : effect x g i = x i := by
    simp [effect,show ¬∃ j, owner j = i from fun ⟨j,h⟩ => off j h]
  refine ⟨effect,atOwner,outside,?_⟩
  intro gates included
  induction gates with
  | nil => exact ⟨.act .done,fun x u S live => ⟨u,S,1,Exec.act _ _,by simp,rfl,live⟩⟩
  | cons g gs ih =>
    obtain ⟨code,one⟩ := build (P := Empty) (U := U) capacity pos fan Empty.elim (fun _ => True)
      (by intros; trivial) g (included _ (by simp))
    obtain ⟨tail,rest⟩ := ih (fun h hm => included h (List.mem_cons_of_mem _ hm))
    refine ⟨code.seq tail,?_⟩
    intro x u S live
    obtain ⟨v,D,n,y,run,paid,user,ready,keep,update⟩ := one x u S ⟨live,trivial⟩
    have eq : y = effect x g := by
      funext i
      by_cases h : ∃ j, owner j = i
      · obtain ⟨j,rfl⟩ := h
        exact funext fun a => (update j a).trans (atOwner x g j a).symm
      · have off j := fun eq => h (Exists.intro j eq)
        exact (keep i off).trans (outside x g i off).symm
    obtain ⟨z,F,m,exec,cost,same,out⟩ := rest (effect x g) v D (eq ▸ ready.1)
    exact ⟨z,F,_,Exec.seq run exec,by simp only [List.map_cons,List.sum_cons]; omega,same.trans user,by simpa only [List.foldl_cons] using out⟩

/-- The private tapes of an occurrence still contain its initial stock,
outside the shared owner and cutoff bank. -/
def PrivateTapes {k T : ℕ} (owner : Fin k ↪ Fin T) (seed S : Stacks T prime) : Prop :=
  ∀ j, (∀ i, owner i ≠ j) → S.L j = seed.L j ∧ S.R j = seed.R j

theorem PrivateTapes.moveStock {k T K : ℕ} {owner : Fin k ↪ Fin T}
    (archive : Fin (80+273) ↪ Fin T) (ports : Fin K ↪ Fin T)
    (archiveFree : ∀ a j, owner j ≠ archive a) (portsFree : ∀ i : Fin K, i.val ≠ 24 → ∀ j, owner j ≠ ports i)
    {seed S : Stacks T prime} (ready : PrivateTapes owner seed S) : MovePrivateStock archive ports seed S :=
  ⟨fun a => ready _ (archiveFree a),fun i hi => ready _ (portsFree i hi)⟩

/-- Run a scalar gate block on the shared owners before a MOVE. The MOVE
sees the gate output and the original private seed. -/
theorem moveAfterOwnerGates {α P U : Type} {T owners Q : ℕ}
    (body : P → Pr P T Q prime U) (owner : Fin owners ↪ Fin T)
    (gates : Pr Empty owners Q prime U) (move : Pr P T Q prime U)
    (rep : α → Stacks owners prime → Prop) (gateEffect moveEffect : α → α)
    (gateBudget moveBudget : ℕ) (seed : Stacks T prime)
    (gateRun : ∀ x u S, rep x S → ∃ z F n, Exec Empty.elim gates (mk u S) n (mk z F) ∧
      n ≤ gateBudget ∧ z.user = u.user ∧ rep (gateEffect x) F)
    (moveRun : ∀ x u S, rep x (embStk owner S) → PrivateTapes owner seed S →
      ∃ z F n, Exec body move (mk u S) n (mk z F) ∧ n ≤ moveBudget ∧
        z.user = u.user ∧ rep (moveEffect x) (embStk owner F)) :
    ∀ x u S, rep x (embStk owner S) → PrivateTapes owner seed S →
      ∃ z F n, Exec body ((embProg owner Empty.elim gates).seq move) (mk u S) n (mk z F) ∧
        n ≤ gateBudget+moveBudget ∧ z.user = u.user ∧ rep (moveEffect (gateEffect x)) (embStk owner F) := by
  intro x u S live stock
  obtain ⟨v,D,n,run,paid,user,next⟩ := gateRun x (embDn owner u) (embStk owner S) live
  obtain ⟨q,G,placed,_,same,view,off⟩ := exec_emb (body' := body) (ι := Empty.elim) owner.injective
    (fun f => nomatch f) run u rfl S rfl
  obtain ⟨z,F,m,exec,cost,final,out⟩ := moveRun (gateEffect x) q G (view ▸ next)
    (fun j outside => ⟨(off j outside).1.trans (stock j outside).1, (off j outside).2.trans (stock j outside).2⟩)
  exact ⟨z,F,_,Exec.seq placed exec,Nat.add_le_add paid cost,final.trans (same.trans user),out⟩

/-- Allocate the MOVE occurrences together. Their owner tapes coincide;
all not-yet-run occurrences retain their seed across an embedded call. -/
theorem allocateMoveStock {I : Type} [Fintype I] {owners : ℕ} (tapes : I → ℕ)
    (owner : ∀ i, Fin owners ↪ Fin (tapes i)) :
    ∃ (T : ℕ) (fan : Fin owners ↪ Fin T) (bank : ∀ i, Fin (tapes i) ↪ Fin T),
      (∀ i j, bank i (owner i j) = fan j) ∧
      ∀ seed : ∀ i, Stacks (tapes i) prime,
      let ready := fun i (S : Stacks T prime) => PrivateTapes (owner i) (seed i) (embStk (bank i) S)
      (∀ shared, ∃ S, embStk fan S = shared ∧ ∀ i, ready i S) ∧
      ∀ {P U : Type} {Q : ℕ} (body : ∀ i, P → Pr P (tapes i) Q prime U) i code u S z F n,
        Exec (body i) code (mk (embDn (bank i) u) (embStk (bank i) S)) n (mk z F) →
        let host := fun f : I × P => embProg (bank f.1) (Prod.mk f.1) (body f.1 f.2)
        ∃ v G, Exec host (embProg (bank i) (Prod.mk i) code) (mk u S) n (mk v G) ∧
          v.user = z.user ∧ embStk (bank i) G = F ∧ ∀ j, j ≠ i → ready j S → ready j G := by
  obtain ⟨T,fan,bank,shared,join,apart⟩ := copyWindowBanks tapes owner
  refine ⟨T,fan,bank,shared,?_⟩
  intro seed ready
  constructor
  · intro X
    obtain ⟨S,view,loaded⟩ := join X seed
    exact ⟨S,view,loaded⟩
  · intro P U Q body i code u S z F n run host
    obtain ⟨v,G,exec,_,user,view,off⟩ := exec_emb (body' := host) (ι := Prod.mk i) (bank i).injective
      (fun _ => rfl) run u rfl S rfl
    refine ⟨v,G,exec,user,view,?_⟩
    intro j ne stock
    have keep (k : Fin (tapes j)) (outside : ∀ h, owner j h ≠ k) := off (bank j k) ((apart j k outside).2 i ne.symm)
    exact fun k outside => ⟨(keep k outside).1.trans (stock k outside).1, (keep k outside).2.trans (stock k outside).2⟩

/-- Sequence allocated MOVE calls in the supplied order. Only occurrences
remaining in the list need their private seed. The shared owner state follows
the same left fold, and each local execution budget is charged once. -/
theorem moveStockSequence {I α P U : Type} [Fintype I] {owners Q : ℕ} (tapes : I → ℕ)
    (owner : ∀ i, Fin owners ↪ Fin (tapes i))
    (body : ∀ i, P → Pr P (tapes i) Q prime U) (code : ∀ i, Pr P (tapes i) Q prime U)
    (gates : I → Pr Empty owners Q prime U) (lastGates : Pr Empty owners Q prime U) (order : List I) (distinct : order.Nodup) :
    ∃ (T : ℕ) (fan : Fin owners ↪ Fin T) (host : I × P → Pr (I × P) T Q prime U)
      (program : Pr (I × P) T Q prime U),
    ∀ (rep : α → Stacks owners prime → Prop) (gateStep step : α → I → α) (lastStep : α → α) (gateBudget budget : I → ℕ) (lastBudget : ℕ)
      (seed : ∀ i, Stacks (tapes i) prime),
    (∀ x u S, rep x S → ∃ z F n, Exec Empty.elim lastGates (mk u S) n (mk z F) ∧
      n ≤ lastBudget ∧ z.user = u.user ∧ rep (lastStep x) F) →
    (∀ i ∈ order, ∀ x u S, rep x S → ∃ z F n, Exec Empty.elim (gates i) (mk u S) n (mk z F) ∧
      n ≤ gateBudget i ∧ z.user = u.user ∧ rep (gateStep x i) F) →
    (∀ i ∈ order, ∀ x u S, rep x (embStk (owner i) S) → PrivateTapes (owner i) (seed i) S →
      ∃ z F n, Exec (body i) (code i) (mk u S) n (mk z F) ∧ n ≤ budget i ∧ z.user = u.user ∧
        rep (step x i) (embStk (owner i) F)) →
    ∀ shared, ∃ S, embStk fan S = shared ∧ ∀ x u, rep x shared →
      ∃ z F n, Exec host program (mk u S) n (mk z F) ∧ n ≤ (order.map fun i => gateBudget i+budget i).sum+lastBudget ∧
        z.user = u.user ∧ rep (lastStep (order.foldl (fun x i => step (gateStep x i) i) x)) (embStk fan F) := by
  obtain ⟨T,fan,bank,shared,allocate⟩ := allocateMoveStock tapes owner
  let host := fun f : I × P => embProg (bank f.1) (Prod.mk f.1) (body f.1 f.2)
  let block := fun i => (embProg (owner i) Empty.elim (gates i)).seq (code i)
  let seq := fun (is : List I) => is.foldr (fun i tail => (embProg (bank i) (Prod.mk i) (block i)).seq tail) (embProg fan Empty.elim lastGates)
  refine ⟨T,fan,host,seq order,?_⟩
  intro rep gateStep step lastStep gateBudget budget lastBudget seed lastRun gateRun localRun X
  obtain ⟨join,place⟩ := allocate seed
  obtain ⟨S,view,stock⟩ := join X
  refine ⟨S,view,?_⟩
  intro x u live
  rw [← view] at live
  have project (i) (D : Stacks T prime) : embStk (owner i) (embStk (bank i) D) = embStk fan D := by
    simp only [embStk,Function.comp_def,shared]
  have ready (i) (_ : i ∈ order) := stock i
  clear stock view
  induction order generalizing u S x with
  | nil =>
    obtain ⟨z,F,n,run,cost,user,out⟩ := lastRun x (embDn fan u) (embStk fan S) live
    obtain ⟨v,G,placed,_,same,view,_⟩ := exec_emb (body' := host) (ι := Empty.elim) fan.injective
      (fun f => nomatch f) run u rfl S rfl
    exact ⟨v,G,n,placed,by simpa using cost,same.trans user,view ▸ out⟩
  | cons i rest ih =>
    obtain ⟨fresh,nodup⟩ := List.nodup_cons.mp distinct
    obtain ⟨z,F,n,run,cost,user,next⟩ := moveAfterOwnerGates (body i) (owner i) (gates i) (code i) rep (fun x => gateStep x i) (fun x => step x i)
      (gateBudget i) (budget i) (seed i) (gateRun i (by simp)) (localRun i (by simp)) x (embDn (bank i) u) (embStk (bank i) S)
      (by rwa [project]) (ready i (by simp))
    obtain ⟨v,D,placed,same,returned,kept⟩ := place body i (block i) u S z F n run
    rw [← returned,project] at next
    obtain ⟨q,G,m,tail,paid,final,out⟩ := ih nodup (fun j hj => gateRun j (List.mem_cons_of_mem _ hj)) (fun j hj => localRun j (List.mem_cons_of_mem _ hj))
      D (step (gateStep x i) i) v next (fun j hj => kept j (fun eq => fresh (eq ▸ hj)) (ready j (List.mem_cons_of_mem _ hj)))
    exact ⟨q,G,_,Exec.seq placed tail,by simp only [List.map_cons,List.sum_cons]; omega,final.trans (same.trans user),out⟩

open Certificates.PR589 in
/-- Execute PR589 scalar blocks interleaved with MOVE occurrences, including
the scalar suffix after the last MOVE. Only the MOVE executions are premises. -/
theorem scalarMoveSequence {P U : Type} {k : ℕ} (layout : Fin 661 ↪ Fin k)
    (gs : List RawGate) (current : ℕ → ℕ) (allowed : ∀ g ∈ gs, g ∈ program)
    (tapes : Fin (phaseMoveBlocks gs current).1.length → ℕ) (owner : ∀ i, Fin (k+2+1) ↪ Fin (tapes i)) :
    let schedule := phaseMoveBlocks gs current
    let I := Fin schedule.1.length
    let blocks := fun i : I => schedule.1[i].1
    let suffix := schedule.2
    let order := List.finRange schedule.1.length
    ∃ states, ∀ {Q V : ℕ}, states ≤ Q → 0 < V →
    let dataBank := Fin.castAddEmb 1 (n := k+2)
    let rep := fun word (x : Fin k → Fin V → ZMod 2) (S : Stacks (k+2+1) prime) =>
      HelperFan dataBank x S ∧ S.R (Fin.last (k+2)) = word
    ∃ effect : (Fin k → Fin V → ZMod 2) → RawGate → Fin k → Fin V → ZMod 2,
    (∀ x g j h, effect x g (layout j) h = g.toCircuit.run (Copy.extendStored (fun j => x (layout j) h)) j.val) ∧
    (∀ x g j, (∀ r, layout r ≠ j) → effect x g j = x j) ∧
    ∀ (body : ∀ i, P → Pr P (tapes i) Q prime U) (move : ∀ i, Pr P (tapes i) Q prime U),
    ∃ T fan host code, ∀ word (step : (Fin k → Fin V → ZMod 2) → I → Fin k → Fin V → ZMod 2) (budget : I → ℕ) (seed : ∀ i, Stacks (tapes i) prime),
      (∀ i, ∀ x u S, rep word x (embStk (owner i) S) → PrivateTapes (owner i) (seed i) S →
        ∃ z F n, Exec (body i) (move i) (mk u S) n (mk z F) ∧ n ≤ budget i ∧ z.user = u.user ∧ rep word (step x i) (embStk (owner i) F)) →
      let bill := fun gs : List RawGate => (gs.map fun g => 76*g.toCircuit.terms.length*V*(k+7)+6).sum+1
      ∀ shared, ∃ S : Stacks T prime, embStk fan S = shared ∧ ∀ x u, rep word x shared →
        ∃ z F n, Exec (host : I × P → Pr (I × P) T Q prime U) code (mk u S) n (mk z F) ∧
          n ≤ (order.map fun i => bill (blocks i)+budget i).sum+bill suffix ∧ z.user = u.user ∧
          rep word (suffix.foldl effect (order.foldl (fun x i => step ((blocks i).foldl effect x) i) x)) (embStk fan F) := by
  classical
  intro schedule I blocks suffix order
  obtain ⟨states,build⟩ := scalarOwnerBlock layout
  refine ⟨states,?_⟩
  intro Q V capacity pos dataBank rep
  obtain ⟨effect,act,off,compile⟩ := build (U := U) capacity pos
  refine ⟨effect,act,off,?_⟩
  intro body move
  obtain ⟨blockAllowed,lastAllowed⟩ := phaseMoveBlocks_allowed gs current allowed
  choose gates runs using fun i => compile (blocks i) (blockAllowed i)
  obtain ⟨last,lastRun⟩ := compile suffix lastAllowed
  let lift : Pr Empty (k+2) Q prime U → Pr Empty (k+2+1) Q prime U := embProg dataBank (id : Empty → Empty)
  have keep {g : Pr Empty (k+2) Q prime U} {x y : Fin k → Fin V → ZMod 2} {cost : ℕ}
      (localRun : ∀ u S, HelperFan (Function.Embedding.refl _) x S →
        ∃ z F n, Exec Empty.elim g (mk u S) n (mk z F) ∧ n ≤ cost ∧ z.user = u.user ∧
          HelperFan (Function.Embedding.refl _) y F) :
      ∀ word u S, rep word x S → ∃ z F n, Exec Empty.elim (lift g) (mk u S) n (mk z F) ∧
        n ≤ cost ∧ z.user = u.user ∧ rep word y F := by
    intro word u S live
    obtain ⟨v,D,n,run,paid,user,out⟩ := localRun (embDn dataBank u) (embStk dataBank S) live.1
    obtain ⟨z,F,placed,_,same,view,frame⟩ := exec_emb (body' := Empty.elim) (ι := id) dataBank.injective
      (fun f => nomatch f) run u rfl S rfl
    have away (i : Fin (k+2)) : dataBank i ≠ Fin.last (k+2) := by
      intro eq
      exact i.isLt.ne (congrArg Fin.val eq)
    refine ⟨z,F,n,placed,paid,same.trans user,?_,(frame _ away).2.trans live.2⟩
    change HelperFan (Function.Embedding.refl _) y (embStk dataBank F)
    exact view ▸ out
  obtain ⟨T,fan,host,code,run⟩ := moveStockSequence tapes owner body move (fun i => lift (gates i)) (lift last) order (List.nodup_finRange _)
  refine ⟨T,fan,host,code,?_⟩
  intro word step budget seed moves bill
  exact run (rep word) (fun x i => (blocks i).foldl effect x) step (fun x => suffix.foldl effect x)
    (fun i => bill (blocks i)) budget (bill suffix) seed (fun x => keep (lastRun x) word) (fun i _ x => keep (runs i x) word) (fun i _ => moves i)

open Certificates.PR589 in
/-- Prepare and dispatch a packed MOVE from the caller's cutoff. Only the
above-cutoff branch requires a child execution witness. -/
theorem packedMixedMoveCall [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (workerPorts : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (capacity : columnCapacity ≤ Q)
    (n : Fin 9) (p : StageRun) (moveIndex : MoveIndex)
    {N H : ℕ} (record : Fin 35 ↪ Fin N) (host : Fin (N+(80+((T+273)+0))) ↪ Fin H) :
    let occurrence := phaseChildPositions.choose (n,p,moveIndex)
    let parent := record.trans ((Fin.castAddEmb (80+((T+273)+0))).trans host)
    let payload := ((scheduledRecordPorts workerPorts) 24).castAdd 273
    let slots := (Fin.castAddEmb 0 (n := T+273)).trans (Fin.natAddEmb 80)
    let placed := (Record.payloadBank (record 24) (slots payload)).trans host
    let stage := slots.trans placed
    let worker := (Fin.castAddEmb 273 (n := T)).trans stage
    let ports := workerPorts.trans worker
    let cut := parent 34
    let e := (archiveSetupPlacement 80 T 0).trans placed
    (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q →
    (∀ k j, parent j ≠ e k) ∧ (∀ k : Fin (rowSwapBlock.tapes+35), k.val ≠ 24 → ∀ j, parent j ≠ ports k) ∧
    ∃ leaf : Pr P H Q prime U, ∀ (body : P → Pr P H Q prime U) (large f : P), body f = leaf →
    let localPort := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let bank := localPort.trans ports
    ∃ code, ∀ (node : Descriptor) (w B rows L cutoff recursiveTime : ℕ),
    let W := node.beforeRows*rows*node.beforeH*node.between*node.afterD
    let desc := scheduledChild prime node occurrence
    let M := prime^(w+1)
    let suffix := M^112*W
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    ({node with rows := rows} : Descriptor).Positive → cutoff < 2^L → desc.width.size ≤ L → L ≤ 64*(w+1) → 0 < W → ∃ position : Fin (volume prime desc) ≃ Fin (M^16*suffix),
    (∀ h, (position h).val = (CopyChildLayout.packActive desc h).val) ∧
    ∃ seed : Stacks H prime, ∀ (x : Fin (M^16*suffix) → ZMod 2) (u : HS H Q prime U) (S : Stacks H prime),
    MovePrivateStock e ports seed S →
    S.R cut = binSyms L cutoff →
    (∀ z, readAt blank (S.L (parent 24)) (S.R (parent 24)) z = RadixToBinary.binaryEncoding.encode
      (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ x)) z)) →
    let core : ℝ := (LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|)
    ∀ rate : ℝ, 163+core ≤ rate →
    let budget := ⌊(rate*(desc.width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime desc⌋₊
    let active := cutoff < desc.width
    let price := if active then recursiveTime else budget
    (active → ScheduledChildExec node desc w suffix ports (binSyms L cutoff) position body large recursiveTime) →
    ∃ z F t y, Exec body code (mk u S) t (mk z F) ∧
      t ≤ (((RecursiveRowsQuotient.constant 142080+30)*142080*43+152402152)+5000)*volume prime desc+price ∧ z.user = u.user ∧
      F.R cut = binSyms L cutoff ∧
      (∀ k ∈ ([2,27,28,32,33,34] : List (Fin 35)), F.R (bank k) = []) ∧
      (∀ z, readAt blank (F.L (parent 24)) (F.R (parent 24)) z = RadixToBinary.binaryEncoding.encode
        (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ y)) z)) ∧
      (∀ i : Fin (rowSwapBlock.tapes+35), 35 ≤ i.val → F.L (ports i) = [] ∧ F.R (ports i) = []) ∧
      (∀ j, (∀ k, e k ≠ j) → (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
      (∀ {K} (nextArchive : Fin (80+273) ↪ Fin H) (nextPorts : Fin K ↪ Fin H) nextSeed,
        let untouched := fun j => (∀ k, e k ≠ j) ∧ (∀ k, ports k ≠ j)
        (∀ k, untouched (nextArchive k)) → (∀ k : Fin K, k.val ≠ 24 → untouched (nextPorts k)) →
        MovePrivateStock nextArchive nextPorts nextSeed S → MovePrivateStock nextArchive nextPorts nextSeed F) ∧
      (∀ {k} (fan : Fin (k+2) ↪ Fin H) (owner : Fin k) data,
        fan (owner.castAdd 2) = parent 24 →
        (∀ j, j ≠ owner.castAdd 2 → (∀ a, e a ≠ fan j) ∧ (∀ i, ports i ≠ fan j)) →
        HelperFan fan data S → HelperFan fan (Function.update data owner y) F) ∧
      (∀ H J, let caller := RecordReady (b := prime) (w := w) (d := 16) (W := suffix) parent H J (binSyms L cutoff) SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
        caller x S → caller y F) ∧
      ∀ h, y (position h) = Shared50RecursiveNodeRows.transpose (one_dvd desc.rows) (x ∘ position) h := by
  intro occurrence parent payload slots placed stage worker ports cut e headerCapacity
  let headers := fun i j => stage (borrowedHeaders T i j)
  have headerAt (i : Fin 127) (j : Fin 6) : e (borrowedHeaders 80 i j) = headers i j := by
    calc
      _ = placed (archiveSetupPlacement 80 T 0 (borrowedHeaders 80 i j)) := rfl
      _ = placed (((borrowedHeaders T i j).castAdd 0).natAdd 80) := congrArg placed (archiveSetupPlacement_header 80 T 0 i j)
      _ = _ := rfl
  have offWorker (k j) : e k ≠ ports j := by
    change placed (archiveSetupPlacement 80 T 0 k) ≠ placed ((((workerPorts j).castAdd 273).castAdd 0).natAdd 80)
    exact placed.injective.ne ((archiveSetupPlacement_frame k).1 (workerPorts j))
  have offParent (k j) : e k ≠ parent j := by
    have ne : archiveSetupPlacement 80 T 0 k ≠ slots payload := (archiveSetupPlacement_frame (T := T) (L := 0) k).1 (scheduledRecordPorts workerPorts 24)
    change host (Record.payloadBank (record 24) (slots payload) (archiveSetupPlacement 80 T 0 k)) ≠ host ((record j).castAdd _)
    apply host.injective.ne
    rw [Record.payloadBank_private _ _ _ ne]
    intro eq
    have h := congrArg Fin.val eq
    simp only [Fin.val_natAdd,Fin.val_castAdd] at h
    have := (record j).isLt
    omega
  let rank := nodeChildren5[occurrence.val]
  obtain ⟨positive,rankBound⟩ := nodeChildren5_bounds occurrence
  have bound : rank ≤ 64 := rankBound.trans (by decide)
  have shared : scheduledRecordPorts ports 24 = parent 24 := congrArg host (Record.payloadBank_shared (record 24) (slots payload))
  have apartParent (i : Fin T) (j : Fin 35) (hj : j ≠ 24) : stage (i.castAdd 273) ≠ parent j := by
    change host (Record.payloadBank (record 24) (slots payload) (slots (i.castAdd 273))) ≠ host ((record j).castAdd _)
    apply host.injective.ne
    by_cases eq : slots (i.castAdd 273) = slots payload
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
  refine ⟨fun k j => (offParent k j).symm,?_,leaf,?_⟩
  · intro k hk j
    by_cases eq : j = 24
    · subst j
      rw [← shared]
      intro same
      change ports ((Fin.castLEEmb (Nat.le_add_left 35 rowSwapBlock.tapes)) (24 : Fin 35)) = ports k at same
      exact hk (congrArg Fin.val (ports.injective same).symm)
    · exact (apartParent (workerPorts k) j eq).symm
  intro body large f installed localPort bank
  let i : Fin 127 := ⟨2*rank-2,by omega⟩
  obtain ⟨prepare,setup⟩ := prepareWorkerRecord_exec body bank headers (fun i j k => apart i j (localPort k))
  obtain ⟨dispatch,call⟩ := moveCutoffCall body large f ports cut (headers i 5) cutOff (fun k => (apart i 5 k).symm) rank
  let fields : List (Fin 35) := [2,27,28,32,33]
  let controls := fields.map bank
  obtain ⟨produce,produceRun⟩ := placedMoveHeaders e body headerCapacity
  refine ⟨produce.seq (prepare.seq (dispatch.seq (Mult.ShortConv.clearWords controls))),?_⟩
  intro node w B rows L cutoff recursiveTime W desc M suffix aligned split label positiveRole cutFits fits precision pos
  have measure := (scheduledChild_measures prime node ⟨_,aligned⟩ ⟨_,split⟩ occurrence).2
  have total : (M^16*suffix)*142080 = volume prime node := by
    unfold volume
    rw [aligned,split,Nat.mul_comm 64 (w+1),pow_mul]
    dsimp only [M,suffix,W]
    ring
  have size : volume prime desc = M^16*suffix := Nat.eq_of_mul_eq_mul_right (by decide : 0 < 142080) (measure.trans total.symm)
  let pack := CopyChildLayout.packActive desc
  have card := Fintype.card_congr pack
  simp only [Fintype.card_fin] at card
  let position := pack.trans (finCongr (card.symm.trans size))
  have coords (h) : (position h).val = (CopyChildLayout.packActive desc h).val := rfl
  obtain ⟨initial,input⟩ := parentArchiveInput_exists node w
  let blankHost : Stacks H prime := ⟨[],[],fun _ => [],fun _ => []⟩
  let seed := embOvr e initial.get blankHost
  refine ⟨position,coords,seed,?_⟩
  intro x u S stock header payload core rate room budget active price recurse
  have view := embStk_ovr e.injective initial blankHost
  have archiveStacks (k) := stock.1 k
  have l : (embStk e S).L = initial.L := funext fun k =>
    (archiveStacks k).1.trans (congrArg (fun D => Stacks.L D k) view)
  have r : (embStk e S).R = initial.R := funext fun k =>
    (archiveStacks k).2.trans (congrArg (fun D => Stacks.R D k) view)
  have ready : ParentArchiveInput node w (embStk e S) := by
    change ParentArchiveInput node w ⟨_,_,(embStk e S).L,(embStk e S).R⟩
    rw [l,r]
    exact input
  have privatePort (j : Fin (rowSwapBlock.tapes+35)) (hj : j.val ≠ 24) : S.L (ports j) = [] ∧ S.R (ports j) = [] := by
    have kept := stock.2 j hj
    have blank := embOvr_off initial.get blankHost (fun k => offWorker k j)
    exact ⟨kept.1.trans blank.1,kept.2.trans blank.2⟩
  have archive := (privatePort (localPort 34) (by change 34 ≠ 24; decide)).2
  have empty (j : Fin 35) (hj : j ≠ 24) (_ : j ≠ 34) := privatePort (localPort j) (fun eq => hj (Fin.ext eq))
  have clean (j : Fin (rowSwapBlock.tapes+35)) (hj : 35 ≤ j.val) := privatePort j (by omega)
  have width : desc.width = (w+1)*rank := by
    change rank*(node.width/64) = _
    rw [aligned,Nat.mul_div_cancel_left _ (by decide),Nat.mul_comm]
  have smaller : desc.width < node.width := by
    rw [width,aligned,Nat.mul_comm 64]
    exact Nat.mul_lt_mul_of_pos_left (rankBound.trans_lt (by decide : 42 < 64)) (Nat.succ_pos w)
  let digits := if active then L else (CopyChildLayout.spectators desc).size
  obtain ⟨v₀,S₀,m₀,run₀,user₀,cost₀,generated,frame₀⟩ := produceRun node w B rows aligned split label positiveRole u S ready
  have workerFrame j := frame₀ (ports j) (fun k => offWorker k j)
  have parentFrame j := frame₀ (parent j) (fun k => offParent k j)
  have words i j := (headerAt i j) ▸ generated i j
  have src : ∀ z, readAt blank (S₀.L (parent 24)) (S₀.R (parent 24)) z = RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ x)) z) := by
    rw [(parentFrame 24).1,(parentFrame 24).2]; exact payload
  obtain ⟨v,D,m,user,run,cost,stored,left,off⟩ := setup w W x v₀ S₀ words
    (fun j hn hm => ⟨(workerFrame (localPort j)).1.trans (empty j hn hm).1,(workerFrame (localPort j)).2.trans (empty j hn hm).2⟩)
    (by simpa only [show bank 24 = parent 24 from shared] using src)
  rw [show S₀.R (bank 34) = [] from (workerFrame (localPort 34)).2.trans archive] at stored
  have spectator := ((off (headers i 5) (fun k => (apart i 5 (localPort k)).symm)).trans (words i 5)).trans
    (moveSpectatorHeader desc w W rank positive bound width size)
  have clear (j : Fin (rowSwapBlock.tapes+35)) (hj : 35 ≤ j.val) : D.L (ports j) = [] ∧ D.R (ports j) = [] := by
    have outside (k : Fin 35) : bank k ≠ ports j := by
      intro eq
      change ports (localPort k) = ports j at eq
      have h := congrArg Fin.val (ports.injective eq)
      change k.val = j.val at h
      omega
    exact ⟨(congrFun left _).trans ((workerFrame j).1.trans (clean j hj).1),(off _ outside).trans ((workerFrame j).2.trans (clean j hj).2)⟩
  obtain ⟨z,F,n,y,exec,paid,same,out,free,frame,read⟩ := call node desc w suffix L cutoff recursiveTime budget position
    width cutFits fits recurse (fun _ => move body f installed node desc w suffix width position coords
      (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) pos) rate room)
    smaller v D x ((off cut (fun k => cutOff (localPort k))).trans ((parentFrame 34).2.trans header)) spectator stored clear
  have keep (j) (outside : ∀ i, ports i ≠ j) : F.L j = S₀.L j ∧ F.R j = S₀.R j :=
    ⟨(frame j outside).1.trans (congrFun left j),(frame j outside).2.trans (off j (fun k => outside (localPort k)))⟩
  obtain ⟨q,final,erase⟩ := retireWorkerControls body bank w suffix [] y z F out
  let G := {F with R := fun k => if k ∈ controls then [] else F.R k}
  have untouched (j) (away : ∀ k ∈ fields, bank k ≠ j) : G.R j = F.R j := by
    apply ite_eq_right
    intro mem
    obtain ⟨k,hk,eq⟩ := List.mem_map.mp mem
    exact away k hk eq
  have preserved (j) (outside : ∀ i, ports i ≠ j) : G.L j = S₀.L j ∧ G.R j = S₀.R j :=
    ⟨(keep j outside).1,(untouched j (fun k _ => outside (localPort k))).trans (keep j outside).2⟩
  have payloadAt : G.R (parent 24) = F.R (parent 24) := by
    apply untouched
    intro k hk
    rw [← shared]
    exact bank.injective.ne (fun eq => (by decide : (24 : Fin 35) ∉ [2,27,28,32,33]) (eq ▸ hk))
  have result z := out.src z
  simp only [shared,sub_zero] at result
  refine ⟨q,G,_,y,Exec.seq run₀ (Exec.seq run (Exec.seq exec erase)),?_,final.trans (same.trans (user.trans user₀)),?_,?_,?_,?_,?_,?_,?_,?_,read⟩
  · change m ≤ 14*M.size+6*suffix.size+6*(w+1)+11*(w+1).size+50 at cost
    change n ≤ price+8*digits+4*w+23*desc.width+22*L+61 at paid
    have overhead := moveOverhead_volume desc w W rank L digits pos bound width precision
      (by dsimp only [digits]; split <;> first | exact le_max_left .. | exact le_max_right ..) size
    change 18*M.size+8*suffix.size+6*(w+1)+11*(w+1).size+124+8*digits+6*w+23*desc.width+22*L ≤ _ at overhead
    change m₀+(m+(n+(2*(2*M.size+suffix.size+w)+13))) ≤ _
    change m₀ ≤ _*(M^16*suffix) at cost₀
    rw [← size] at cost₀
    rw [Nat.add_mul]
    omega
  · exact (preserved cut cutOff).2.trans ((parentFrame 34).2.trans header)
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
  · intro j away outside
    exact ⟨(preserved j outside).1.trans (frame₀ j away).1,(preserved j outside).2.trans (frame₀ j away).2⟩
  · intro K nextArchive nextPorts nextSeed untouched archiveFree portsFree stock
    apply stock.frame untouched _ archiveFree portsFree
    intro j away
    exact ⟨(preserved j away.2).1.trans (frame₀ j away.1).1,(preserved j away.2).2.trans (frame₀ j away.1).2⟩
  · intro k fan owner data atOwner apart live
    apply fanUpdate owner y live
    · intro z
      rw [atOwner,payloadAt]
      simpa only [G,List.map_ofFn,Function.comp_def,sub_zero] using result z
    · intro j ne
      obtain ⟨archiveFree,portsFree⟩ := apart j ne
      exact ⟨(preserved _ portsFree).1.trans (frame₀ _ archiveFree).1,
        (preserved _ portsFree).2.trans (frame₀ _ archiveFree).2⟩
  · intro H J caller start
    apply start.returnPayload (fun j hj => by
      have h := preserved (parent j) (fun k => apartParent (workerPorts k) j hj)
      exact ⟨h.1.trans (parentFrame j).1,h.2.trans (parentFrame j).2⟩)
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
