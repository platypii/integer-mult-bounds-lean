module

public import IntegerMultBounds.MathlibTM2.M6.BitScalarMoveSequence
public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleLeaf
public import IntegerMultBounds.MathlibTM2.DFT.Fields

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

theorem PrivateTapes.moveStock {k T K : ℕ} {owner : Fin k ↪ Fin T}
    (archive : Fin (80+273) ↪ Fin T) (ports : Fin K ↪ Fin T)
    (archiveFree : ∀ a j, owner j ≠ archive a) (portsFree : ∀ i : Fin K, i.val ≠ 24 → ∀ j, owner j ≠ ports i)
    {seed S : Stacks T prime} (ready : PrivateTapes owner seed S) : MovePrivateStock archive ports seed S :=
  ⟨fun a => ready _ (archiveFree a),fun i hi => ready _ (portsFree i hi)⟩

/-- Place the parent record beside the phase tapes, sharing its payload
with the chosen owner and its cutoff with the final phase tape. -/
def phaseWorkerRecord {k : ℕ} (owner : Fin k) : Fin 35 ↪ Fin ((k+2+1)+35) :=
  (Record.payloadBank (Fin.last (k+2)) 34).trans
    (Equiv.swap ((24 : Fin 35).natAdd (k+2+1)) (((owner.castAdd 2).castAdd 1).castAdd 35)).toEmbedding

theorem phaseWorkerRecord_shared {k : ℕ} (owner : Fin k) :
    phaseWorkerRecord owner 24 = (((owner.castAdd 2).castAdd 1).castAdd 35) ∧
    phaseWorkerRecord owner 34 = (Fin.last (k+2)).castAdd 35 := by
  have offPayload : (Fin.last (k+2)).castAdd 35 ≠ ((24 : Fin 35).natAdd (k+2+1)) := by
    intro eq
    have h := congrArg Fin.val eq
    simp only [Fin.val_castAdd,Fin.val_last,Fin.val_natAdd] at h
    omega
  have offOwner : (Fin.last (k+2)).castAdd 35 ≠ (((owner.castAdd 2).castAdd 1).castAdd 35) := by
    intro eq
    have h := congrArg Fin.val eq
    simp only [Fin.val_castAdd,Fin.val_last] at h
    omega
  constructor
  · change Equiv.swap _ _ (Record.payloadBank _ _ _) = _
    rw [Record.payloadBank_private _ _ _ (by decide : (24 : Fin 35) ≠ 34),Equiv.swap_apply_left]
  · change Equiv.swap _ _ (Record.payloadBank _ _ _) = _
    rw [Record.payloadBank_shared,Equiv.swap_apply_of_ne_of_ne offPayload offOwner]

open Certificates.PR589 in
/-- Prepare and dispatch a packed MOVE from the caller's cutoff. Only the
above-cutoff branch requires a child execution witness. -/
theorem packedMixedMoveCall [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (workerPorts : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (capacity : columnCapacity ≤ Q)
    (n : Fin 9) (p : StageRun) (moveIndex : MoveIndex)
    {k H : ℕ} (layout : Fin 661 ↪ Fin k) (host : Fin (((k+2+1)+35)+(80+((T+273)+0))) ↪ Fin H) :
    let target := layout (paidRegister moveIndex.val)
    let occurrence := phaseChildPositions.choose (n,p,moveIndex)
    let base := (Fin.castAddEmb (80+((T+273)+0))).trans host
    let record := phaseWorkerRecord target
    let phase := (Fin.castAddEmb 35 (n := k+2+1)).trans base
    let fan := (Fin.castAddEmb 1 (n := k+2)).trans phase
    let payload := ((scheduledRecordPorts workerPorts) 24).castAdd 273
    let slots := (Fin.castAddEmb 0 (n := T+273)).trans (Fin.natAddEmb 80)
    let placed := (Record.payloadBank (record 24) (slots payload)).trans host
    let stage := slots.trans placed
    let worker := (Fin.castAddEmb 273 (n := T)).trans stage
    let ports := workerPorts.trans worker
    (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q →
    ∃ leaf : Pr P H Q prime U, ∀ (body : P → Pr P H Q prime U) (large f : P), body f = leaf →
    ∃ code, ∀ (node : Descriptor) (w B rows L cutoff recursiveTime : ℕ),
    let W := node.beforeRows*rows*node.beforeH*node.between*node.afterD
    let desc := scheduledChild prime node occurrence
    let M := prime^(w+1)
    let suffix := M^112*W
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    ({node with rows := rows} : Descriptor).Positive → cutoff < 2^L → desc.width.size ≤ L → L ≤ 64*(w+1) → 0 < W → ∃ position : Fin (volume prime desc) ≃ Fin (M^16*suffix),
    (∀ h, (position h).val = (CopyChildLayout.packActive desc h).val) ∧
    ∃ seed : Stacks H prime, ∀ (data : Fin k → Fin (M^16*suffix) → ZMod 2) (u : HS H Q prime U) (S : Stacks H prime),
    PrivateTapes phase seed S → HelperFan fan data S → S.R (phase (Fin.last (k+2))) = binSyms L cutoff →
    let core : ℝ := (LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|)
    ∀ rate : ℝ, 163+core ≤ rate →
    let budget := ⌊(rate*(desc.width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime desc⌋₊
    let active := cutoff < desc.width
    let price := if active then recursiveTime else budget
    (active → ScheduledChildExec node desc w suffix ports (binSyms L cutoff) position body large recursiveTime) →
    let next := Shared50RecursiveNodeRows.transpose (one_dvd desc.rows) (data target ∘ position) ∘ position.symm
    ∃ z F t, Exec body code (mk u S) t (mk z F) ∧
      t ≤ (((RecursiveRowsQuotient.constant 142080+30)*142080*43+152402152)+5000)*volume prime desc+price ∧ z.user = u.user ∧
      F.R (phase (Fin.last (k+2))) = binSyms L cutoff ∧ HelperFan fan (Function.update data target next) F := by
  intro target occurrence base record phase fan payload slots placed stage worker ports headerCapacity
  let parent := record.trans base
  let cut := parent 34
  let e := (archiveSetupPlacement 80 T 0).trans placed
  let headers := fun i j => stage (borrowedHeaders T i j)
  have headerAt (i : Fin 127) (j : Fin 6) : e (borrowedHeaders 80 i j) = headers i j := by
    calc
      _ = placed (archiveSetupPlacement 80 T 0 (borrowedHeaders 80 i j)) := rfl
      _ = placed (((borrowedHeaders T i j).castAdd 0).natAdd 80) := congrArg placed (archiveSetupPlacement_header 80 T 0 i j)
      _ = _ := rfl
  have offWorker (k j) : e k ≠ ports j := by
    change placed (archiveSetupPlacement 80 T 0 k) ≠ placed ((((workerPorts j).castAdd 273).castAdd 0).natAdd 80)
    exact placed.injective.ne ((archiveSetupPlacement_frame k).1 (workerPorts j))
  have offBase (k j) : e k ≠ base j := by
    have ne : archiveSetupPlacement 80 T 0 k ≠ slots payload := (archiveSetupPlacement_frame (T := T) (L := 0) k).1 (scheduledRecordPorts workerPorts 24)
    change host (Record.payloadBank (record 24) (slots payload) (archiveSetupPlacement 80 T 0 k)) ≠ host (j.castAdd _)
    apply host.injective.ne
    rw [Record.payloadBank_private _ _ _ ne]
    intro eq
    have h := congrArg Fin.val eq
    simp only [Fin.val_natAdd,Fin.val_castAdd] at h
    have := j.isLt
    omega
  have offParent k j := offBase k (record j)
  let rank := nodeChildren5[occurrence.val]
  obtain ⟨positive,rankBound⟩ := nodeChildren5_bounds occurrence
  have bound : rank ≤ 64 := rankBound.trans (by decide)
  have shared : scheduledRecordPorts ports 24 = parent 24 := congrArg host (Record.payloadBank_shared (record 24) (slots payload))
  have apartParent (i : Fin T) (j : Fin ((k+2+1)+35)) (hj : j ≠ record 24) : stage (i.castAdd 273) ≠ base j := by
    change host (Record.payloadBank (record 24) (slots payload) (slots (i.castAdd 273))) ≠ host (j.castAdd _)
    apply host.injective.ne
    by_cases eq : slots (i.castAdd 273) = slots payload
    · rw [eq,Record.payloadBank_shared]
      exact (Fin.castAddEmb _).injective.ne hj.symm
    · rw [Record.payloadBank_private _ _ _ eq]
      intro same
      have h := congrArg Fin.val same
      simp only [Fin.val_natAdd,Fin.val_castAdd] at h
      have := j.isLt
      omega
  have cutOff (i) : ports i ≠ cut := apartParent (workerPorts i) (record 34) (record.injective.ne (by decide))
  have apart (i j k) : headers i j ≠ ports k := by
    intro eq
    exact borrowedHeaders_apart i j (workerPorts k) (stage.injective eq)
  obtain ⟨leaf,move⟩ := stoppedMoveProgram (P := P) (U := U) ports capacity rank positive
  have portsFree (k : Fin (rowSwapBlock.tapes+35)) (hk : k.val ≠ 24) j : base j ≠ ports k := by
    by_cases eq : j = record 24
    · subst j
      change parent 24 ≠ _
      rw [← shared]
      intro same
      change ports ((Fin.castLEEmb (Nat.le_add_left 35 rowSwapBlock.tapes)) (24 : Fin 35)) = ports k at same
      exact hk (congrArg Fin.val (ports.injective same).symm)
    · exact (apartParent (workerPorts k) j eq).symm
  refine ⟨leaf,?_⟩
  intro body large f installed
  let localPort := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
  let bank := localPort.trans ports
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
  intro data u S privateStock live cutoffWord core rate room budget active price recurse next
  let x := data target
  have atOwner : parent 24 = fan (target.castAdd 2) := congrArg base (phaseWorkerRecord_shared target).1
  have atCut : cut = phase (Fin.last (k+2)) := congrArg base (phaseWorkerRecord_shared target).2
  have header : S.R cut = binSyms L cutoff := atCut.symm ▸ cutoffWord
  have payload := fanPayload live target
  have payload (z) := payload z
  simp only [← atOwner,List.map_ofFn,Function.comp_def,sub_zero] at payload
  have stock := privateStock.moveStock e ports (fun a j => (offBase a (j.castAdd 35)).symm)
    (fun i hi j => portsFree i hi (j.castAdd 35))
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
  have value : y = next := by
    funext j
    simpa only [next,Function.comp_apply,Equiv.apply_symm_apply] using read (position.symm j)
  refine ⟨q,G,_,Exec.seq run₀ (Exec.seq run (Exec.seq exec erase)),?_,final.trans (same.trans (user.trans user₀)),?_,?_⟩
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
  · rw [← atCut]
    exact (preserved cut cutOff).2.trans ((parentFrame 34).2.trans header)
  · rw [← value]
    apply fanUpdate target y live
    · intro z
      rw [← atOwner,payloadAt]
      simpa only [G,List.map_ofFn,Function.comp_def,sub_zero] using result z
    · intro j ne
      have archiveFree a := offBase a ((j.castAdd 1).castAdd 35)
      have away (i) : ports i ≠ fan j := by
        apply apartParent (workerPorts i) ((j.castAdd 1).castAdd 35)
        intro eq
        apply ne
        exact (Fin.castAddEmb 1).injective ((Fin.castAddEmb 35).injective
          (eq.trans (phaseWorkerRecord_shared target).1))
      exact ⟨(preserved _ away).1.trans (frame₀ _ archiveFree).1,
        (preserved _ away).2.trans (frame₀ _ archiveFree).2⟩

/-- Populate an empty occurrence archive from the parent's cutoff and
the trailing header of the rank-selected adjacent exchange. -/
theorem prepareMoveArchive {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin 35 ↪ Fin T) (cut : Fin T) (headers : Fin 127 → Fin 6 → Fin T)
    (offCut : ∀ j, bank j ≠ cut) (offHeader : ∀ i j, bank j ≠ headers i 5)
    (rank : ℕ) (positive : 0 < rank) (bound : rank ≤ 64) :
    let i : Fin 127 := ⟨2*rank-2,by omega⟩
    ∃ code, ∀ (child : Descriptor) (w W L cutoff : ℕ),
    child.width = (w+1)*rank → volume prime child = (prime^(w+1))^16*((prime^(w+1))^112*W) →
    let n := CopyChildLayout.spectators child
    let archive := binSyms (A := prime) n.size n ++ separator :: binSyms L cutoff
    ∀ (u : HS T Q prime U) (S : Stacks T prime), S.R cut = binSyms L cutoff →
    S.R (headers i 5) = (Routines.hdr (helperAdjacentView (w+1) 1 W i) 5).map bitSymbol →
    S.R (bank 34) = [] → S.R (bank 0) = [] → S.R (bank 1) = [] →
    ∃ z, Exec body code (mk u S) (6*(L+n.size)+13)
      (mk z {S with R := Function.update S.R (bank 34) archive}) ∧ z.user = u.user := by
  intro i
  let copy : Fin T → Pr P T Q prime U := fun source => bcopy source (bank 34) (bank 0) (bank 1)
  refine ⟨(copy cut).seq ((Prog.act (DFT.pushSep (bank 34))).seq (copy (headers i 5))),?_⟩
  intro child w W L cutoff width size n archive u S header field empty a b
  have count := field.trans (moveSpectatorHeader child w W rank positive bound width size)
  obtain ⟨v,user,first⟩ := bcopy_exec (body := body) (a := cut) (c := bank 34) (t₁ := bank 0) (t₂ := bank 1)
    (by simp [Ne.symm (offCut _)]) u S a b
  rw [header,empty,List.append_nil,length_binSyms] at first
  let D := {S with R := Function.update S.R (bank 34) (binSyms L cutoff)}
  have mark := Exec.act (body := body) (DFT.pushSep (bank 34)) (mk v D)
  rw [DFT.pushSep_run] at mark
  let F := {D with R := Function.update D.R (bank 34) (separator :: D.R (bank 34))}
  have read : F.R (headers i 5) = binSyms n.size n := by
    simpa [F,D,Function.update_of_ne (offHeader i 34).symm] using count
  obtain ⟨z,same,last⟩ := bcopy_exec (body := body) (a := headers i 5) (c := bank 34) (t₁ := bank 0) (t₂ := bank 1)
    (by simp [Ne.symm (offHeader i _)]) v F (by simpa [F,D] using a) (by simpa [F,D] using b)
  rw [read,length_binSyms] at last
  refine ⟨z,(Exec.seq first (Exec.seq mark last)).cast (by omega) ?_,same.trans user⟩
  simp [F,D,archive,Function.update_idem]

/-- Read the spectator count from the front of a MOVE archive, leaving
the inherited cutoff in the record for the ordinary width comparison. -/
theorem unpackMoveArchive {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin 35 ↪ Fin T) (spectator : Fin T) (apart : ∀ i, bank i ≠ spectator)
    (w W L cutoff spectators : ℕ) (word : Fin ((prime^(w+1))^16*W) → ZMod 2)
    (u : HS T Q prime U) (S : Stacks T prime) :
    let count := binSyms (A := prime) spectators.size spectators
    let header := binSyms (A := prime) L cutoff
    let stored := fun archive => RecordReady (b := prime) (w := w) (d := 16) (W := W)
      bank (prime^(w+1)).size W.size archive SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 word
    let F := {S with R := Function.update (Function.update S.R (bank 34) header) spectator count}
    stored (count ++ separator :: header) S → S.R spectator = [] →
    ∃ z, Exec body (DFT.takeField (bank 34) spectator (bank 0)) (mk u S) (4*spectators.size+5) (mk z F) ∧
      z.user = u.user ∧ stored header F ∧ F.R spectator = count := by
  intro count header stored F ready empty
  obtain ⟨z,user,run⟩ := DFT.takeField_exec body (apart 34) (bank.injective.ne (by decide : (34 : Fin 35) ≠ 0))
    (apart 0).symm (DFT.separator_not_mem_binSyms spectators.size spectators) u S ready.archive (ready.scratch 0 (by decide)).2 empty
  refine ⟨z,by simpa only [count,length_binSyms] using run,user,?_,Function.update_self ..⟩
  have updated := replaceArchive bank _ header word S ready
  apply updated.returnPayload (F := F) (outBank := bank) (fun j _ => ⟨rfl,Function.update_of_ne (apart j) ..⟩)
  intro z
  simpa only [F,Function.update_of_ne (apart 24),sub_zero] using (updated.src z).symm

/-- Restore the combined archive after dispatch. Two transfers preserve the
order of the spectator digits and empty the temporary registers. -/
theorem restoreMoveArchive {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin 35 ↪ Fin T) (spectator : Fin T) (apart : ∀ i, bank i ≠ spectator)
    (w W L cutoff spectators : ℕ) (word : Fin ((prime^(w+1))^16*W) → ZMod 2)
    (u : HS T Q prime U) (S : Stacks T prime) :
    let count := binSyms (A := prime) spectators.size spectators
    let header := binSyms (A := prime) L cutoff
    let stored := fun archive => RecordReady (b := prime) (w := w) (d := 16) (W := W)
      bank (prime^(w+1)).size W.size archive SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 word
    let archive := count ++ separator :: header
    let F := {S with R := Function.update (Function.update S.R (bank 34) archive) spectator []}
    stored header S → S.R spectator = count →
    ∃ z, Exec body ((Prog.act (DFT.pushSep (bank 34))).seq
      ((moveR spectator (bank 0) id).seq (moveR (bank 0) (bank 34) id))) (mk u S) (4*spectators.size+5) (mk z F) ∧
      z.user = u.user ∧ stored archive F := by
  intro count header stored archive F ready countAt
  have sep := Exec.act (body := body) (DFT.pushSep (bank 34)) (mk u S)
  rw [DFT.pushSep_run,ready.archive] at sep
  have different := bank.injective.ne (by decide : (0 : Fin 35) ≠ 34)
  obtain ⟨v,user,reverse⟩ := moveR_exec body spectator (bank 0) (apart 0).symm id u _
  obtain ⟨z,same,restore⟩ := moveR_exec body (bank 0) (bank 34) different id v _
  have run := Exec.seq sep (Exec.seq reverse restore)
  have empty := (ready.scratch 0 (by decide)).2
  simp [movedR,Function.update_of_ne,Ne.symm (apart 34),different,Ne.symm different,apart,
    countAt,empty,count,length_binSyms,Function.update_idem] at run
  refine ⟨z,run.cast (by omega) ?_,same.trans user,?_⟩
  · congr 2
    funext j
    by_cases h : j = spectator <;> by_cases a : j = bank 34 <;> by_cases b : j = bank 0 <;>
      simp_all [archive,count,Function.update_apply]
  · have updated := replaceArchive bank _ archive word S ready
    apply updated.returnPayload (F := F) (outBank := bank) (fun j _ => ⟨rfl,Function.update_of_ne (apart j) ..⟩)
    intro j
    simpa only [F,Function.update_of_ne (apart 24),sub_zero] using (updated.src j).symm

/-- Run the stopped leaf on the extracted spectator field. Swapping its
archive port onto that field keeps the inherited cutoff in the parent record. -/
theorem stoppedMoveWithSpectator [M8.Machine.Net] {work T Q : ℕ} {P U : Type}
    (ports : Fin (work+35) ↪ Fin T) (spectator : Fin T)
    (apart : ∀ i, ports i ≠ spectator) (fitsLeaf : 44+LeafCore.small ≤ work+35) (capacity : columnCapacity ≤ Q) (rank : ℕ) (positive : 0 < rank) :
    ∃ code : Pr P T Q prime U, ∀ (body : P → Pr P T Q prime U) (f : P), body f = code →
    ∀ (node child : Descriptor) (w W : ℕ), child.width = (w+1)*rank →
    ∀ position : Fin (volume prime child) ≃ Fin ((prime^(w+1))^16*W),
    (∀ i, (position i).val = (CopyChildLayout.packActive child i).val) → 0 < W →
    let core : ℝ := (LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|)
    ∀ rate : ℝ, 163+core ≤ rate → child.width < node.width →
    let bank := scheduledRecordPorts ports
    let count := binSyms (A := prime) (CopyChildLayout.spectators child).size (CopyChildLayout.spectators child)
    ∀ archive word u S,
    let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) bank
      (prime^(w+1)).size W.size archive SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
    let clean := fun D : Stacks T prime => ∀ i : Fin (work+35), 35 ≤ i.val →
      D.L (ports i) = [] ∧ D.R (ports i) = []
    stored word S → clean S → S.R spectator = count →
    ∃ z F t y, Exec body (body f) (mk u S) t (mk z F) ∧
      t ≤ ⌊(rate*(child.width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime child⌋₊ ∧ z.user = u.user ∧
      stored y F ∧ clean F ∧ F.R spectator = count ∧ F.L spectator = S.L spectator ∧
      (∀ j, j ≠ spectator → (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
      ∀ h, y (position h) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) h := by
  let idx : Fin (work+35) := ⟨34,by omega⟩
  let placed := ports.trans (Equiv.swap (ports idx) spectator).toEmbedding
  have atField : placed idx = spectator := Equiv.swap_apply_left ..
  have same i (ne : i ≠ idx) : placed i = ports i :=
    Equiv.swap_apply_of_ne_of_ne (ports.injective.ne ne) (apart i)
  obtain ⟨code,leaf⟩ := stoppedMoveOnBank (P := P) (U := U) placed fitsLeaf capacity rank positive
  refine ⟨code,?_⟩
  intro body f installed node child w W width position packed pos core rate room smaller bank count archive word u S stored clean ready free field
  let other := scheduledRecordPorts placed
  have bankEq (j : Fin 35) (ne : j ≠ 34) : other j = bank j := same _ (fun eq => by have h := congrArg Fin.val eq; exact ne (Fin.ext h))
  have outside (i : Fin (work+35)) (hi : 35 ≤ i.val) : placed i = ports i :=
    same i (fun eq => by have h := congrArg Fin.val eq; change i.val = 34 at h; omega)
  have switchBank (b c : Fin 35 ↪ Fin T) (agree : ∀ j, j ≠ 34 → b j = c j)
      (x : Fin ((prime^(w+1))^16*W) → ZMod 2) (D : Stacks T prime) (a a' : List (Fin (prime+4)))
      (h : RecordReady (b := prime) (w := w) (d := 16) (W := W) b (prime^(w+1)).size W.size a
        SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 x D) (hdr : D.R (c 34) = a') :
      RecordReady (b := prime) (w := w) (d := 16) (W := W) c (prime^(w+1)).size W.size a'
        SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 x D := by
    refine ⟨?_,?_,?_,?_,?_,hdr,?_,?_,?_⟩
    all_goals first
      | rw [← agree _ (by decide)]; first | exact h.modulus | exact h.width | exact h.one | exact h.padded | exact h.clock | exact h.src | exact h.dst
      | intro j hj; rw [← agree j (fun eq => (by decide : (34 : Fin 35) ∉ shearWork) (eq ▸ hj))]; exact h.scratch j hj
  have start := switchBank bank other (fun j ne => (bankEq j ne).symm) word S archive count ready (atField ▸ field)
  obtain ⟨z,F,t,y,run,paid,user,out,blank,left,frame,read⟩ := leaf body f installed node child w W width position packed pos rate room smaller u S word start (fun i hi => outside i hi ▸ free i hi)
  have keep := frame (ports idx) (fun i => by
    by_cases eq : i = idx
    · simpa only [eq,atField] using (apart idx).symm
    · exact (same i eq) ▸ ports.injective.ne eq)
  refine ⟨z,F,t,y,run,paid,user,switchBank other bank bankEq y F count archive out (keep.2.trans ready.archive),?_,?_,?_,?_,read⟩
  · intro i hi
    exact outside i hi ▸ blank i hi
  · exact atField ▸ out.archive
  · exact atField ▸ left
  · intro j ne off
    apply frame
    intro i
    by_cases eq : i = idx
    · simpa only [eq,atField] using ne.symm
    · rw [same i eq]; exact off i

noncomputable def twoFieldDispatch {work T Q : ℕ} {P U : Type}
    (ports : Fin (work+35) ↪ Fin T) (spectator : Fin T) (rank : ℕ)
    (large leaf : Pr P T Q prime U) : Pr P T Q prime U :=
  let bank := scheduledRecordPorts ports
  let cmp := cutoffColumnSlots.trans bank
  let select := Prog.cond (fun z => symBit (z.scan (cmp 7))) large leaf
  let finish := (Prog.act (DFT.pushSep (bank 34))).seq
    ((moveR spectator (bank 0) id).seq (moveR (bank 0) (bank 34) id))
  (DFT.takeField (bank 34) spectator (bank 0)).seq ((ordinaryCutoffTest cmp rank).seq (select.seq finish))

/-- Dispatch a MOVE from the two-field archive. Both branches restore
the original record, and only an active child requires recursion. -/
theorem twoFieldMoveProgram [M8.Machine.Net] {work T Q : ℕ} {P U : Type}
    (ports : Fin (work+35) ↪ Fin T) (spectator : Fin T)
    (apart : ∀ i, ports i ≠ spectator) (fitsLeaf : 44+LeafCore.small ≤ work+35) (capacity : columnCapacity ≤ Q) (rank : ℕ) (positive : 0 < rank) :
    ∃ leafCode : Pr P T Q prime U, ∀ (body : P → Pr P T Q prime U) (large leaf : P), body leaf = leafCode →
    ∀ (node child : Descriptor) (w W L cutoff time : ℕ), child.width = (w+1)*rank →
    cutoff < 2^L → child.width.size ≤ L → ∀ position : Fin (volume prime child) ≃ Fin ((prime^(w+1))^16*W),
    (∀ i, (position i).val = (CopyChildLayout.packActive child i).val) → 0 < W →
    let core : ℝ := (LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|)
    ∀ rate : ℝ, 163+core ≤ rate → child.width < node.width →
    let bank := scheduledRecordPorts ports
    let n := CopyChildLayout.spectators child
    let header := binSyms (A := prime) L cutoff
    let archive := binSyms n.size n ++ separator :: header
    let active := cutoff < child.width
    let price := if active then time else ⌊(rate*(child.width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime child⌋₊
    (active → MoveOnBankExec node child w W ports header position body (body large) time) →
    let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) bank
      (prime^(w+1)).size W.size archive SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
    let clean := fun D : Stacks T prime => ∀ i : Fin (work+35), 35 ≤ i.val →
      D.L (ports i) = [] ∧ D.R (ports i) = []
    ∀ word u S, stored word S → clean S → S.R spectator = [] →
    ∃ z F t y, Exec body (twoFieldDispatch ports spectator rank (body large) (body leaf)) (mk u S) t (mk z F) ∧
      t ≤ price+4*w+23*child.width+22*L+8*n.size+61 ∧ z.user = u.user ∧
      stored y F ∧ clean F ∧ F.R spectator = [] ∧ F.L spectator = S.L spectator ∧
      (∀ j, j ≠ spectator → (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
      ∀ h, y (position h) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) h := by
  obtain ⟨leafCode,stop⟩ := stoppedMoveWithSpectator (P := P) (U := U) ports spectator apart fitsLeaf capacity rank positive
  refine ⟨leafCode,?_⟩
  intro body large leaf installed
  let bank := scheduledRecordPorts ports
  let cmp := cutoffColumnSlots.trans bank
  let select : Pr P T Q prime U := .cond (fun z => symBit (z.scan (cmp 7))) (body large) (body leaf)
  intro node child w W L cutoff time width fits digits position coords pos core rate room smaller _ n header archive active price recurse stored clean word u S ready free empty
  have away j := apart ((Fin.castLEEmb (Nat.le_add_left 35 work)) j)
  obtain ⟨v,openRun,user,opened,count⟩ := unpackMoveArchive body bank spectator away w W L cutoff n word u S ready empty
  let D := {S with R := Function.update (Function.update S.R (bank 34) header) spectator (binSyms n.size n)}
  have high (i : Fin (work+35)) (hi : 35 ≤ i.val) : ports i ≠ bank 34 := by
    intro eq
    have h := congrArg Fin.val (ports.injective eq)
    change i.val = 34 at h
    omega
  have clear : clean D := fun i hi => ⟨(free i hi).1,by simpa [D,Function.update_of_ne (apart i),Function.update_of_ne (high i hi)] using (free i hi).2⟩
  have scratch : ∀ k : Fin 10, 2 ≤ k.val → cutoffColumnSlots k ∈ shearWork := by decide
  obtain ⟨q,m,same,flag,cost,test⟩ := ordinaryCutoffTest_exec body cmp rank w L cutoff fits
    (width ▸ digits) v D opened.clock opened.archive (fun k hk => (opened.scratch _ (scratch k hk)).2)
  rw [← width] at flag cost
  have branch : ∃ z F t y, Exec body select (mk q D) (t+1) (mk z F) ∧ t ≤ price ∧ z.user = q.user ∧
      RecordReady (b := prime) (w := w) (d := 16) (W := W) bank (prime^(w+1)).size W.size header SparseRoleCircuit.encode
        (fun _ => blank) (fun _ => blank) 0 0 y F ∧ clean F ∧ F.R spectator = binSyms n.size n ∧ F.L spectator = S.L spectator ∧
      (∀ j, j ≠ spectator → (∀ i, ports i ≠ j) → F.L j = D.L j ∧ F.R j = D.R j) ∧
      ∀ h, y (position h) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) h := by
    by_cases h : active
    · obtain ⟨z,F,t,y,run,paid,ret,out,blank,_,frame,read⟩ := recurse h smaller q D word opened clear
      exact ⟨z,F,t,y,Exec.cond_true (by simp [mk_var,flag,show cutoff < child.width from h]) run,
        by simpa [price,h] using paid,ret,out,blank,(frame spectator apart).2.trans count,(frame spectator apart).1,fun j _ => frame j,read⟩
    · obtain ⟨z,F,t,y,run,paid,ret,out,blank,field,left,frame,read⟩ := stop body leaf installed node child w W width position coords pos rate room smaller header word q D opened clear count
      exact ⟨z,F,t,y,Exec.cond_false (by simp [mk_var,flag,show ¬cutoff < child.width from h]) run,
        by simpa [price,h] using paid,ret,out,blank,field,left,frame,read⟩
  obtain ⟨z,F,t,y,run,paid,ret,out,blank,field,left,frame,read⟩ := branch
  obtain ⟨v',closeRun,final,closed⟩ := restoreMoveArchive body bank spectator away w W L cutoff n y z F out field
  refine ⟨v',_,_,y,Exec.seq openRun (Exec.seq test (Exec.seq run closeRun)),by omega,
    final.trans (ret.trans (same.trans user)),closed,?_,Function.update_self ..,left,?_,read⟩
  · intro i hi
    exact ⟨(blank i hi).1,by simpa [Function.update_of_ne (apart i),Function.update_of_ne (high i hi)] using (blank i hi).2⟩
  · intro j ne off
    have diff : j ≠ bank 34 := (off _).symm
    simpa only [D,Function.update_of_ne ne,Function.update_of_ne diff] using frame j ne off

/-- Reserve the last row-swap port for the spectator field. -/
theorem movePrefixFits [M8.Machine.Net] : rowSwapBlock.tapes-1+35 < rowSwapBlock.tapes+35 := by
  have := rowSwapFits
  omega

noncomputable def movePrefix [M8.Machine.Net] : Fin (rowSwapBlock.tapes-1+35) ↪ Fin (rowSwapBlock.tapes+35) :=
  Fin.castLEEmb movePrefixFits.le

noncomputable def moveSpectatorPort [M8.Machine.Net] : Fin (rowSwapBlock.tapes+35) := ⟨_,movePrefixFits⟩

theorem scheduledTwoFieldMove [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (capacity : columnCapacity ≤ Q)
    (rank : ℕ) (positive : 0 < rank) :
    let prefixBank := movePrefix.trans ports
    let spectator := ports moveSpectatorPort
    ∃ leafCode : Pr P T Q prime U, ∀ (body : P → Pr P T Q prime U) (entry large leaf : P), body leaf = leafCode →
    body entry = twoFieldDispatch prefixBank spectator rank (body large) (body leaf) →
    ∀ (node child : Descriptor) (w W L cutoff time : ℕ), child.width = (w+1)*rank →
    cutoff < 2^L → child.width.size ≤ L → ∀ position : Fin (volume prime child) ≃ Fin ((prime^(w+1))^16*W),
    (∀ i, (position i).val = (CopyChildLayout.packActive child i).val) → 0 < W →
    let core : ℝ := (LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|)
    ∀ rate : ℝ, 163+core ≤ rate →
    let n := CopyChildLayout.spectators child
    let header := binSyms (A := prime) L cutoff
    let active := cutoff < child.width
    let price := if active then time else ⌊(rate*(child.width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime child⌋₊
    (active → MoveOnBankExec node child w W prefixBank header position body (body large) time) →
    ScheduledChildExec node child w W ports (binSyms n.size n ++ separator :: header) position body entry
      (price+4*w+23*child.width+22*L+8*n.size+61) := by
  intro prefixBank spectator
  have apart (i) : prefixBank i ≠ spectator := ports.injective.ne (fun eq => by have h := congrArg Fin.val eq; exact i.isLt.ne h)
  have fits := moveLeafFitsWithSpare
  have size := rowSwapFits
  obtain ⟨code,mixed⟩ := twoFieldMoveProgram (P := P) (U := U) prefixBank spectator apart (by omega) capacity rank positive
  refine ⟨code,?_⟩
  intro body entry large leaf installed dispatch node child w W L cutoff time width fitsCut digits position coords pos core rate room n header active price recurse smaller u S word ready free
  have high : 35 ≤ moveSpectatorPort.val := by change 35 ≤ rowSwapBlock.tapes-1+35; omega
  obtain ⟨z,F,t,y,run,paid,user,out,clean,empty,left,frame,read⟩ :=
    mixed body large leaf installed node child w W L cutoff time width fitsCut digits position coords pos rate room smaller recurse
      word u S ready (fun i hi => free (movePrefix i) hi) (free moveSpectatorPort high).2
  refine ⟨z,F,t,y,dispatch ▸ run,paid,user,out,?_,fun j off => frame j (off _).symm (fun i => off (movePrefix i)),read⟩
  intro i hi
  by_cases bound : i.val < rowSwapBlock.tapes-1+35
  · exact clean ⟨i.val,bound⟩ hi
  · have eq : i = moveSpectatorPort := Fin.ext (by have := i.isLt; change i.val = rowSwapBlock.tapes-1+35; omega)
    subst i
    exact ⟨left.trans (free moveSpectatorPort high).1,empty⟩

/-- Call a scheduled MOVE from an empty archive, produce both fields on
the machine, and release the occurrence archive after the child returns. -/
theorem callPreparedMove [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (capacity : columnCapacity ≤ Q)
    (cut : Fin T) (headers : Fin 127 → Fin 6 → Fin T)
    (offCut : ∀ j, scheduledRecordPorts ports j ≠ cut)
    (offHeader : ∀ i j, scheduledRecordPorts ports j ≠ headers i 5)
    (rank : ℕ) (positive : 0 < rank) (bound : rank ≤ 64) :
    let bank := scheduledRecordPorts ports
    let i : Fin 127 := ⟨2*rank-2,by omega⟩
    ∃ leafCode : Pr P T Q prime U, ∀ (body : P → Pr P T Q prime U) (entry large leaf : P), body leaf = leafCode →
    body entry = twoFieldDispatch (movePrefix.trans ports) (ports moveSpectatorPort) rank (body large) (body leaf) →
    ∃ code, ∀ (node child : Descriptor) (w W L cutoff time : ℕ),
    let suffix := (prime^(w+1))^112*W
    child.width = (w+1)*rank → volume prime child = (prime^(w+1))^16*suffix →
    ∀ position : Fin (volume prime child) ≃ Fin ((prime^(w+1))^16*suffix),
    (∀ h, (position h).val = (CopyChildLayout.packActive child h).val) → 0 < W → cutoff < 2^L →
    child.width.size ≤ L → L ≤ 64*(w+1) →
    let core : ℝ := (LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|)
    ∀ rate : ℝ, 163+core ≤ rate → child.width < node.width →
    let active := cutoff < child.width
    let price := if active then time else ⌊(rate*(child.width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime child⌋₊
    (active → MoveOnBankExec node child w suffix (movePrefix.trans ports) (binSyms L cutoff) position body (body large) time) →
    let stored := RecordReady (b := prime) (w := w) (d := 16) (W := suffix) bank (prime^(w+1)).size suffix.size []
      SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
    let clean := fun S : Stacks T prime => ∀ j : Fin (rowSwapBlock.tapes+35), 35 ≤ j.val →
      S.L (ports j) = [] ∧ S.R (ports j) = []
    ∀ word u S, stored word S → clean S → S.R cut = binSyms L cutoff →
    S.R (headers i 5) = (Routines.hdr (helperAdjacentView (w+1) 1 W i) 5).map bitSymbol →
    ∃ z F t y, Exec body code (mk u S) t (mk z F) ∧ t ≤ price+10000*volume prime child ∧
      z.user = u.user ∧ stored y F ∧ clean F ∧
      (∀ j, (∀ l, ports l ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
      ∀ h, y (position h) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) h := by
  intro bank i
  obtain ⟨leafCode,dispatch⟩ := scheduledTwoFieldMove (P := P) (U := U) ports capacity rank positive
  refine ⟨leafCode,?_⟩
  intro body entry large leaf installed table
  obtain ⟨prep,prepare⟩ := prepareMoveArchive body bank cut headers offCut offHeader rank positive bound
  refine ⟨prep.seq ((Prog.call entry).seq (bclear (bank 34))),?_⟩
  intro node child w W L cutoff time suffix width size position coords pos fits digits precision core rate room smaller active price recurse stored clean word u S ready free header field
  let n := CopyChildLayout.spectators child
  let archive := binSyms (A := prime) n.size n ++ separator :: binSyms L cutoff
  obtain ⟨v,start,user⟩ := prepare child w W L cutoff width size u S header field ready.archive
    (ready.scratch 0 (by decide)).2 (ready.scratch 1 (by decide)).2
  have high (j : Fin (rowSwapBlock.tapes+35)) (hj : 35 ≤ j.val) : ports j ≠ bank 34 := by
    intro eq
    have h := congrArg Fin.val (ports.injective eq)
    change j.val = 34 at h
    omega
  have worker := dispatch body entry large leaf installed table node child w suffix L cutoff time width fits digits position coords
    (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) pos) rate room recurse
  obtain ⟨q,D,t,y,run,paid,same,out,blank,frame,read⟩ := worker smaller v _ word
    (replaceArchive bank [] archive word S ready)
    (fun j hj => ⟨(free j hj).1,(Function.update_of_ne (high j hj) ..).trans (free j hj).2⟩)
  obtain ⟨z,final,_,finish⟩ := bclear_exec (body := body) (bank 34) q D
  rw [out.archive] at finish
  refine ⟨z,_,_,y,Exec.seq start (Exec.seq (Exec.call run) finish),?_,final.trans (same.trans user),
    replaceArchive bank archive [] y D out,?_,?_,read⟩
  · simp only [List.length_append,List.length_cons,length_binSyms]
    have overhead := moveOverhead_volume child w W rank L n.size pos bound width precision (le_max_right ..) size
    change t ≤ price+4*w+23*child.width+22*L+8*n.size+61 at paid
    dsimp only [n] at paid overhead
    omega
  · intro j hj
    exact ⟨(blank j hj).1,(Function.update_of_ne (high j hj) ..).trans (blank j hj).2⟩
  · intro j outside
    have ne : j ≠ bank 34 := (outside _).symm
    exact ⟨(frame j outside).1,(Function.update_of_ne ne ..).trans ((frame j outside).2.trans (Function.update_of_ne ne ..))⟩

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

-- The tagged MOVE dispatcher and generic archive wrapper are available in 21524d7e.

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

private theorem ScheduledChildExec.weaken {P U : Type} [M8.Machine.Net] {T Q w W a b : ℕ}
    {node child : Descriptor} {ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T} {record position}
    {body : P → Pr P T Q prime U} {f : P}
    (worker : ScheduledChildExec node child w W ports record position body f a) (le : a ≤ b) :
    ScheduledChildExec node child w W ports record position body f b := by
  intro smaller u S word ready free
  obtain ⟨z,F,t,y,run,paid,rest⟩ := worker smaller u S word ready free
  exact ⟨z,F,t,y,run,paid.trans le,rest⟩

private theorem sweepChildOverhead [M8.Machine.Net] {α : Type} (runs : List StageRun) (jobsPerRun : List α)
    (time : ℕ → ℕ) (coeff : StageRun → ℝ) (rate : ℝ) (offset V w : ℕ) :
    let indices := List.range' offset (runs.flatMap (fun _ => jobsPerRun)).length
    let scale := (V : ℝ)*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
    (rate+(runs.map coeff).sum)*scale + ((indices.map (fun j => time j+5000*V)).sum : ℝ) ≤
      (rate+(runs.map (fun p => coeff p+5000*(jobsPerRun.length : ℝ))).sum)*scale +
        ((indices.map time).sum : ℝ) := by
  dsimp only
  let charged := fun j => time j+5000*V
  let jobs := (runs.flatMap (fun _ => jobsPerRun)).length
  let indices := List.range' offset jobs
  have lengthJobs (ls : List StageRun) : (ls.flatMap (fun _ => jobsPerRun)).length =
      ls.length*jobsPerRun.length := by
    induction ls with
    | nil => simp
    | cons a ls ih => simp [ih,Nat.add_mul,Nat.add_comm]
  have extra : (indices.map charged).sum = (indices.map time).sum+jobs*(5000*V) := by
    simp [charged,List.sum_map_add,List.map_const',indices]
  have one : 1 ≤ ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau :=
    Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 w) M8.Machine.BudgetBound.exponent_range.1.le
  rw [extra]
  simp only [indices,jobs,lengthJobs,List.sum_map_add,List.map_const',List.sum_replicate,nsmul_eq_mul,
    Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,add_mul] at one ⊢
  nlinarith only [mul_nonneg (show 0 ≤ (runs.length : ℝ)*jobsPerRun.length*(5000*(V : ℝ)) by positivity) (sub_nonneg.mpr one)]

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
      ∀ (budget : Fin nodeChildren5.length → ℕ),
      ∀ L : ℕ, cutoff < 2^L → node.width.size ≤ L →
      let price := fun i => if cutoff < (child i).width then budget i else
        ⌊(rate*((child i).width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime (child i)⌋₊
      ∃ (mp : ∀ p i, Fin (volume prime (child (mi p i))) ≃ Fin ((prime^(w+1))^16*W))
        (cp : ∀ p j, Fin (volume prime (child (ci p j))) ≃ Fin ((prime^(w+1))^16*W)),
      (∀ p i h, (mp p i h).val = (CopyChildLayout.packActive (child (mi p i)) h).val) ∧
      (∀ p j, CopyIntervalPositions (child (ci p j)) (w+1) W (cp p j)) ∧
      ∃ (Label : Type) (tapes : StageRun → ℕ) (body : ∀ p, Label → Pr Label (tapes p) Q prime U),
        PackedStageExecution (w := w+1) (B := B) (K := K) n tapes body coeff (fun time =>
          (∀ k, price k + 22*(L-node.width) ≤ time k.val) ∧
          (∀ p i, let k := mi p i; cutoff < (child k).width → (child k).width < node.width →
            MoveOnBankExec node (child k) w W (movePrefix.trans (mr p i)) (binSyms L cutoff) (mp p i) (mb p i) (mb p i (.active (mf p i))) (budget k)) ∧
          (∀ p j, let k := ci p j; cutoff < (child k).width → (child k).width < node.width →
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
    scheduledTwoFieldMove (P := WorkerLabel P) (U := U) (mr p i) ((le_max_left _ _).trans caps)
      (nodeChildren5[(mi p i).val]) (nodeChildren5_bounds (mi p i)).1
  let mb := fun p i => workerTable (twoFieldDispatch (movePrefix.trans (mr p i)) (mr p i moveSpectatorPort) nodeChildren5[(mi p i).val]) (leaf p i) (ml p i) (mf p i)
  let cb := fun p j => let cmp := cutoffColumnSlots.trans (scheduledRecordPorts (cr p j))
                       workerTable (fun large leaf => (ordinaryCutoffTest cmp 7).seq (.cond (fun z => symBit (z.scan (cmp 7))) large leaf))
                         (stoppedCopyProgram (cr p j) ((le_max_right _ _).trans caps)) (cl p j) (cf p j)
  obtain ⟨coeff,stage⟩ := build ((le_max_left _ _).trans room) mb (fun _ _ => .entry) cb (fun _ _ => .entry)
  refine ⟨mb,cb,fun p => coeff p+5000*(Geometry.Moves.localPaid.length : ℝ),fun _ _ _ => rfl,fun _ _ _ => rfl,?_⟩
  intro node w B rows cutoff width split label K W pos rate large _ _ child budget L cutFits parentFits price
  have smaller (i : Fin nodeChildren5.length) : (child i).width < node.width := by
    change nodeChildren5[i.val]*(node.width/64) < node.width
    rw [width,Nat.mul_div_cancel_left _ (by decide)]
    exact Nat.mul_lt_mul_of_pos_right ((nodeChildren5_bounds i).2.trans_lt (by decide : 42 < 64)) (Nat.succ_pos w)
  let mrec := fun p i => let s := CopyChildLayout.spectators (child (mi p i))
                         binSyms (A := prime) s.size s ++ separator :: binSyms L cutoff
  let crec := fun (_ : StageRun) (_ : CopyIndex) => binSyms (A := prime) L cutoff
  obtain ⟨mp,cp,banks,mc,cc,T,fan,bank,run⟩ := stage node w B rows width split label pos mrec crec
  have overhead (k : Fin nodeChildren5.length) (position : Fin (volume prime (child k)) ≃ Fin ((prime^(w+1))^16*W)) :
      4*w+23*(child k).width+22*L+8*(CopyChildLayout.spectators (child k)).size+61 ≤ 5000*volume prime (child k)+22*(L-node.width) := by
    let tailWidth := B*prime^(64*((w+1)*64))*K
    have regroup : W = (prime^(w+1))^112*tailWidth := by dsimp only [W,tailWidth]; ring
    have vol := Fintype.card_congr position
    simp only [Fintype.card_fin,regroup] at vol
    have tailPos : 0 < tailWidth := by rw [regroup] at pos; exact Nat.pos_of_mul_pos_left pos
    have shape : (child k).width = (w+1)*nodeChildren5[k.val] := by
      change nodeChildren5[k.val]*(node.width/64) = _
      rw [width,Nat.mul_div_cancel_left _ (by decide),Nat.mul_comm]
    have prec : min L node.width ≤ 64*(w+1) := (min_le_right ..).trans width.le
    have bill := moveOverhead_volume (child k) w tailWidth _ (min L node.width) _ tailPos ((nodeChildren5_bounds k).2.trans (by decide : 42 ≤ 64))
      shape prec (le_max_right ..) vol
    omega
  refine ⟨mp,cp,mc,cc,_,fun p => (banks p).tapes,fun p => (banks p).body (mBank p) (cBank p) (mb p) (cb p),T,fan,bank,?_⟩
  intro scratch owner worker host blocks V time ready
  let charged := fun j => time j+5000*V
  have execute := run charged
  suffices works : _ by
    intro shared
    obtain ⟨initial,view,code,exec⟩ := execute works shared
    refine ⟨initial,view,code,?_⟩
    intro x u S live headers free fresh
    obtain ⟨z,F,t,out,step,paid,ret,done⟩ := exec x u S live headers free fresh
    refine ⟨z,F,t,out,step,paid.trans ?_,ret,done⟩
    have bill := sweepChildOverhead stageRuns Geometry.Moves.localPaid time coeff (stagePackingRate n) (stageChildStart n) V w
    dsimp only at bill
    exact bill
  constructor
  · intro p i
    have shape : (child (mi p i)).width = (w+1)*nodeChildren5[(mi p i).val] := by
      change nodeChildren5[(mi p i).val]*(node.width/64) = _
      rw [width,Nat.mul_div_cancel_left _ (by decide),Nat.mul_comm]
    apply ScheduledChildExec.weaken (move p i (mb p i) .entry (.active (mf p i)) .leaf rfl rfl node _ w W L cutoff _ shape
      cutFits ((Nat.size_le_size (smaller _).le).trans parentFits) (mp p i) (mc p i) pos rate
      ((le_max_left _ _).trans large) (fun h => ready.2.1 p i h (smaller _)))
    let k := mi p i
    change price k+4*w+23*(child k).width+22*L+8*(CopyChildLayout.spectators (child k)).size+61 ≤ time k.val+5000*V
    have room := ready.1 k
    have vol := Fintype.card_congr (mp p i)
    simp only [Fintype.card_fin] at vol
    change volume prime (child k) = V at vol
    have bill := overhead k (mp p i)
    rw [vol] at bill
    omega
  · intro p j
    apply ScheduledChildExec.weaken (copy (cr p j) _ (cb p j) .entry (.active (cf p j)) .leaf rfl rfl node n p j w W rows L cutoff
      width split cutFits ((Nat.size_le_size (smaller _).le).trans parentFits) (cp p j) (cc p j) pos rate _ ((le_max_right _ _).trans large) (fun h => ready.2.2 p j h (smaller _)))
    let k := ci p j
    change 4*w+23*(child k).width+22*L+51+price k ≤ time k.val+5000*V
    have room := ready.1 k
    have vol := Fintype.card_congr (cp p j)
    simp only [Fintype.card_fin] at vol
    change volume prime (child k) = V at vol
    have bill := overhead k (cp p j)
    rw [vol] at bill
    omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
