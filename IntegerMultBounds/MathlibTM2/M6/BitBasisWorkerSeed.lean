module

public import IntegerMultBounds.MathlibTM2.M6.BitWorkerRecordSeed
public import IntegerMultBounds.MathlibTM2.M6.BitWorkerDispatch
public import IntegerMultBounds.MathlibTM2.M6.BitPortRun
public import IntegerMultBounds.MathlibTM2.M6.BitPortSwapSetup

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)

/-- Load a swap's private stacks from four external runtime words and return
its entire 35-tape caller workspace blank. -/
theorem loadSwapPortFromWords {P U : Type} {T Q K : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin (35+(24+K)) ↪ Fin T) (source : Fin 4 → Fin T)
    (apart : ∀ i j, bank i ≠ source j) (d i j : ℕ) (degree : 2 ≤ d) :
    let suffix := (Fin.natAddEmb 35 (m := 24+K)).trans bank
    ∃ rate : ℕ, ∃ code, ∀ w W, 0 < W → ∀ u (S : Stacks T prime),
      let M := prime^(w+1)
      S.R (source 0) = binSyms M.size M → S.R (source 1) = binSyms 1 1 →
      S.R (source 2) = binSyms W.size W → (S.R (source 3)).length = w →
      (∀ k, S.L (bank k) = [] ∧ S.R (bank k) = []) →
      ∃ z F n, Exec body code (mk u S) n (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F n (rate*(M^d*W)) ∧
        (∀ k, let seed := swapPrivateStacks K (payloadView prime d (w+1) W) d i j (w+1)
          F.L (suffix k) = seed.L k ∧ F.R (suffix k) = seed.R k) ∧
        ∀ k, (∀ h, suffix h ≠ k) → F.L k = S.L k ∧ F.R k = S.R k := by
  classical
  intro suffix
  let caller := (Fin.castAddEmb (24+K) (n := 35)).trans bank
  let slots : Fin 4 ↪ Fin 35 := ⟨![2,28,27,33],by decide⟩
  have separate (a b) : caller a ≠ suffix b := bank.injective.ne (by
    intro eq
    have val := congrArg Fin.val eq
    change a.val = 35+b.val at val
    omega)
  obtain ⟨copy,read⟩ := installChildSeed body caller slots source (caller 0) (caller 1)
    (fun i j => apart _ _) (fun i => by
      have h : ∀ i : Fin 4, slots i ≠ 0 ∧ slots i ≠ 1 := by decide
      simp [List.nodup_cons,Function.Embedding.trans_apply,(apart _ _).symm,caller,
        bank.injective.eq_iff,(h i).1,(h i).2])
  obtain ⟨rate,setup,run⟩ := placedSwapPortLoader body bank d i j degree
  let targets := slots.trans caller
  let work := (List.finRange 4).map targets
  have unique := (List.nodup_finRange 4).map targets.injective
  refine ⟨rate+100,(copy.seq setup).seq (clearWorkTapes work),?_⟩
  intro w W positive u S M base unit width clock free
  let words := fun i => S.R (source i)
  let seed : Stacks 35 prime := ⟨[],[],fun _ => [],Function.extend slots words (fun _ => [])⟩
  have atSlot (a) : seed.R (slots a) = words a := slots.injective.extend_apply words (fun _ => []) a
  obtain ⟨v,R,t,exec,user,copied,set,off⟩ := read seed u S (fun a => (atSlot a).symm) (fun _ => (free _).2)
    (free _).2 (free _).2
  have stored a : R (caller (slots a)) = words a :=
    (set _ (fun h => False.elim (h a rfl))).trans (atSlot a)
  let D := {S with R := R}
  have noScratch : ∀ k : Fin 35, 3 ≤ k.val → k.val < 9 → ∀ a, slots a ≠ k := by decide
  obtain ⟨z,G,m,ready,same,bill,out,frame⟩ := run w W positive v D
    ((stored 0).trans base) ((stored 1).trans unit) ((stored 2).trans width)
    ((congrArg List.length (stored 3)).trans clock)
    (fun k lo hi => (off _ (fun a => caller.injective.ne (noScratch k lo hi a))).trans (free _).2)
    (fun k => ⟨(free _).1,(off _ (fun a => separate _ k)).trans (free _).2⟩)
  have copyBill : CleanupBound S D t (seedLoadBill words) := by
    intro js nd
    change t+tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js S+seedLoadBill words
    simpa only [D,atSlot] using copied js nd
  obtain ⟨last,lastUser,clear⟩ := clearWorkTapes_exec body work unique z G
  let F := {G with L := fun k => if k ∈ work then [] else G.L k, R := fun k => if k ∈ work then [] else G.R k}
  have paid := cleanupBound_clearBank (F := F) work unique (copyBill.seq bill)
    (Nat.le_refl (tapeCharge cleanupWeight work G+1)) (fun k hk => by simp [F,hk])
    (fun k => by by_cases hk : k ∈ work <;> simp [F,hk])
  have init : tapeCharge cleanupWeight work S = 16 := by
    change (work.map (fun k => cleanupWeight (S.L k) (S.R k))).sum = 16
    rw [List.map_congr_left (g := fun _ => 4) (fun k hk => by
      obtain ⟨a,_,rfl⟩ := List.mem_map.mp hk
      change cleanupWeight (S.L (bank _)) (S.R (bank _)) = _
      rw [(free _).1,(free _).2]
      rfl)]
    rfl
  have vol := Nat.le_mul_of_pos_right (M^d) positive
  have hm : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have rad := (Nat.le_self_pow (by omega : d ≠ 0) M).trans vol
  have wt := (Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt (n := w+1)).le
  have count := Nat.le_mul_of_pos_left W (pow_pos hm d)
  have bits (n : ℕ) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have fee : seedLoadBill words+17 ≤ 100*(M^d*W) := by
    simp [seedLoadBill,Fin.sum_univ_succ,words,base,unit,width,clock,length_binSyms]
    have := bits M
    have := bits W
    change w+1 ≤ M at wt
    omega
  refine ⟨last,F,_,(exec.seq ready).seq clear,lastUser.trans (same.trans user),?_,?_,?_⟩
  · intro js nd
    have h := paid js nd
    apply h.trans (Nat.add_le_add_left _ _)
    rw [init,Nat.add_mul]
    change seedLoadBill words+rate*(M^d*W)+16+1 ≤ rate*(M^d*W)+100*(M^d*W)
    omega
  · intro k
    have h : suffix k ∉ work := by
      intro mem
      obtain ⟨a,_,eq⟩ := List.mem_map.mp mem
      exact separate _ k eq
    simpa only [F,ite_eq_right h] using out k
  · intro k away
    by_cases h : k ∈ work
    · obtain ⟨a,_,rfl⟩ := List.mem_map.mp h
      simp only [F,ite_eq_left h]
      exact ⟨(free _).1.symm,(free _).2.symm⟩
    · have orig := off k (fun a eq => h (eq ▸ List.mem_map_of_mem (f := targets) (List.mem_finRange a)))
      simpa only [F,ite_eq_right h] using And.intro (frame k away).1 ((frame k away).2.trans orig)

noncomputable def basisSeedPorts {d : ℕ} (ops : List (FlatCoordinateSchedule.Op d)) :
    Fin 2 ↪ Fin (FlatCoordinateCleanSchedule.tapeCount ops) :=
  (Fin.natAddEmb 2 (m := 2)).trans (Fin.castLEEmb (by
    have := FlatCoordinateInitializedSchedule.skeleton_tapes_ge ops
    unfold FlatCoordinateCleanSchedule.tapeCount
    omega))

/-- Physically initialize a COPY or MOVE basis workspace from the atom width
and spectator count. Both binary headers have a left separator. -/
theorem loadBasisWorkerSeed {P U : Type} {T Q d : ℕ} (body : P → Pr P T Q prime U)
    (ops : List (FlatCoordinateSchedule.Op d)) (bank : Fin (FlatCoordinateCleanSchedule.tapeCount ops) ↪ Fin T)
    (source : Fin 2 → Fin T) (tmp saved : Fin T)
    (apart : ∀ i j, bank (basisSeedPorts ops i) ≠ source j)
    (regs : ∀ i, [source i,bank (basisSeedPorts ops i),tmp,saved].Nodup) :
    ∃ code, ∀ w W u (S : Stacks T prime), let seed := basisHeaderStacks ops w W
      ∀ privateTape : Fin (FlatCoordinateCleanSchedule.tapeCount ops) → Prop,
      (∀ i, privateTape (basisSeedPorts ops i)) →
      S.R (source 0) = binSyms w.size w → S.R (source 1) = binSyms W.size W →
      (∀ j, privateTape j → S.L (bank j) = [] ∧ S.R (bank j) = []) → S.R tmp = [] → S.R saved = [] →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (8*(w.size+W.size)+24) ∧
        (∀ j, privateTape j → F.L (bank j) = seed.L j ∧ F.R (bank j) = seed.R j) ∧
        ∀ j, (∀ i, bank (basisSeedPorts ops i) ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  let ports := basisSeedPorts ops
  obtain ⟨copy,load⟩ := installChildSeed body bank ports source tmp saved apart regs
  let order := List.finRange 2
  refine ⟨copy.seq (markArchivePorts (ports.trans bank) order),?_⟩
  intro w W u S seed privateTape headers width count free ht hs
  have x : seed.R (ports 0) = binSyms w.size w := canonicalBits_symbols _
  have y : seed.R (ports 1) = binSyms W.size W := canonicalBits_symbols _
  obtain ⟨v,R,n,start,user,price,stored,frame⟩ := load seed u S (fun i => by
    fin_cases i
    · exact width.trans x.symm
    · exact count.trans y.symm) (fun i => (free _ (headers i)).2) ht hs
  let D := {S with R := R}
  obtain ⟨L,finish,cost,marked,kept⟩ := markArchivePorts_exec body (ports.trans bank) order
    (List.nodup_finRange _) v D (fun i _ => (free _ (headers i)).1)
  refine ⟨v,_,_,start.seq finish,user,?_,?_,?_⟩
  · have total := (show CleanupBound S D n (seedLoadBill (fun i => seed.R (ports i))) from price).seq cost
    have eq : seedLoadBill (fun i => seed.R (ports i))+(5*order.length+1) = 8*(w.size+W.size)+24 := by
      simp [seedLoadBill,Fin.sum_univ_succ,order,x,y,length_binSyms]
      omega
    rwa [eq] at total
  · intro j priv
    by_cases a : j.val = 2
    · obtain rfl : j = ports 0 := Fin.ext a
      exact ⟨marked 0 (List.mem_finRange _),stored _ (fun off => False.elim (off 0 rfl))⟩
    by_cases b : j.val = 3
    · obtain rfl : j = ports 1 := Fin.ext b
      exact ⟨marked 1 (List.mem_finRange _),stored _ (fun off => False.elim (off 1 rfl))⟩
    have off (i : Fin 2) : ports i ≠ j := by fin_cases i <;> intro eq <;> first | exact a (congrArg Fin.val eq.symm) | exact b (congrArg Fin.val eq.symm)
    have left := kept (bank j) (fun i _ => bank.injective.ne (off i))
    simp only [seed,basisHeaderStacks,a,b,false_or,ite_false]
    exact ⟨left.trans (free j priv).1,(frame _ (fun i => bank.injective.ne (off i))).trans (free j priv).2⟩
  · intro j off
    exact ⟨kept _ (fun i _ => off _),frame _ (fun i => off _)⟩

/-- Prepare the private metadata of a port correction while its owner tape
already holds a live row. -/
theorem loadPortBasisMetadata {P U : Type} {T Q d : ℕ} (body : P → Pr P T Q prime U)
    (ops : List (FlatCoordinateSchedule.Op d)) (bank : Fin (FlatCoordinateCleanSchedule.tapeCount ops) ↪ Fin T)
    (source : Fin 2 → Fin T) (tmp saved : Fin T)
    (apart : ∀ i j, bank (basisSeedPorts ops i) ≠ source j)
    (regs : ∀ i, [source i,bank (basisSeedPorts ops i),tmp,saved].Nodup) :
    ∃ code, ∀ w W u (S : Stacks T prime),
      let metadata := basisWorkspace ops (0 : Fin ((prime^w)^d*W) → ZMod 2)
      S.R (source 0) = binSyms w.size w → S.R (source 1) = binSyms W.size W →
      (∀ j, j ≠ segmentSource ops → S.L (bank j) = [] ∧ S.R (bank j) = []) →
      S.R tmp = [] → S.R saved = [] →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (8*(w.size+W.size)+24) ∧
        (∀ j, j ≠ segmentSource ops → ∀ h, metadata.tape j h =
          readAt blank (F.L (bank j)) (F.R (bank j)) (h-metadata.head j)) ∧
        ∀ j, (∀ i, bank (basisSeedPorts ops i) ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨code,load⟩ := loadBasisWorkerSeed body ops bank source tmp saved apart regs
  refine ⟨code,?_⟩
  intro w W u S metadata width count free ht hs
  have priv (i : Fin 2) : basisSeedPorts ops i ≠ segmentSource ops := by
    intro eq
    have h := congrArg Fin.val eq
    change 2+i.val = 0 at h
    omega
  obtain ⟨z,F,t,run,user,bill,ready,off⟩ := load w W u S (· ≠ segmentSource ops) priv width count free ht hs
  refine ⟨z,F,t,run,user,bill,?_,off⟩
  intro j outside h
  rw [(ready j outside).1,(ready j outside).2]
  exact basisHeaderStacks_rep ops (0 : Fin ((prime^w)^d*W) → ZMod 2) j h

local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos w).ne'⟩

noncomputable def portBasisCost {d : ℕ} (ops : List (FlatCoordinateSchedule.Op d)) (w W : ℕ) :=
  let tapes := FlatCoordinateCleanSchedule.tapeCount ops
  8*(w.size+W.size)+24+13*(FlatCoordinateCleanSchedule.constant ops*((prime^w)^d*W)*(tapes+5)+6)+4*tapes+1

/-- Load the basis headers and run the scheduled coordinate operations on
the caller's live owner row. -/
theorem runPortBasis {P U : Type} {T Q d : ℕ} (ops : List (FlatCoordinateSchedule.Op d))
    (body : P → Pr P T Q prime U) (capacity : stateCount (FlatCoordinateCleanSchedule.program ops) ≤ Q)
    (bank : Fin (FlatCoordinateCleanSchedule.tapeCount ops) ↪ Fin T)
    (source : Fin 2 → Fin T) (tmp saved : Fin T)
    (apart : ∀ i j, bank (basisSeedPorts ops i) ≠ source j)
    (regs : ∀ i, [source i,bank (basisSeedPorts ops i),tmp,saved].Nodup) :
    ∃ code, ∀ w W, 0 < W → ∀ (x : Fin ((prime^w)^d*W) → ZMod 2) u (S : Stacks T prime),
      ∀ perm : (Fin d → ZMod (prime^w)) ≃ (Fin d → ZMod (prime^w)),
      (∀ a, OrderedAffine.run (ops.map (fun op => op.action w)) a = perm a) →
      let row := segmentSource ops
      S.R (source 0) = binSyms w.size w → S.R (source 1) = binSyms W.size W →
      (∀ h, readAt blank (S.L (bank row)) (S.R (bank row)) h = (portOwner x).tape 0 h) →
      (∀ j, j ≠ row → S.L (bank j) = [] ∧ S.R (bank j) = []) → S.R tmp = [] → S.R saved = [] →
      ∃ (y : Fin ((prime^w)^d*W) → ZMod 2), ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (portBasisCost ops w W) ∧
        (∀ h, readAt blank (F.L (bank row)) (F.R (bank row)) h = (portOwner y).tape 0 h) ∧
        (∀ a j, y (FlatCoordinateLayout.index (Q := prime^w) (perm a) j) = x (FlatCoordinateLayout.index (Q := prime^w) a j)) ∧
        (∀ j, j ≠ row → F.L (bank j) = [] ∧ F.R (bank j) = []) ∧
        ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨load,prepare⟩ := loadPortBasisMetadata body ops bank source tmp saved apart regs
  let slots := (List.finRange (FlatCoordinateCleanSchedule.tapeCount ops)).filter (· ≠ segmentSource ops)
  let work := slots.map bank
  have mem j : bank j ∈ work ↔ j ≠ segmentSource ops := by simp [work,slots,bank.injective.eq_iff]
  have distinct : work.Nodup := ((List.nodup_finRange _).filter _).map bank.injective
  refine ⟨(load.seq (embProg bank Empty.elim (foreign (liftQ (FlatCoordinateCleanSchedule.program ops) capacity)))).seq
    (clearWorkTapes work),?_⟩
  intro w W positive x u S perm action row width count owner free ht hs
  let bits : FlatCoordinateStages.Array d w W := fun i => SparseRoleCircuit.encode (a := 0) (x i)
  let layout := fun a : FlatCoordinateStages.Array d w W => SharedBankStageInput.raw
        (FlatCoordinateShiftSharedBank.common (d := d) (b := w) (W := W) a) (FlatCoordinateCleanSchedule.tapeCount ops)
  have tape (word : Fin ((prime^w)^d*W) → ZMod 2) :
      (layout (fun i => SparseRoleCircuit.encode (word i))).tape row = (portOwner word).tape 0 := by
    change FlatRepeatedControlNormalize.encoded (putWord (fun _ => blank) 0
      (List.ofFn fun i => SparseRoleCircuit.encode (a := 0) (word i))) = _
    rw [RecursiveRoleSerialization.encoded_word,List.map_ofFn]
    congr 2
  obtain ⟨v,D,l,start,user,charge,privateReady,frame⟩ := prepare w W u S width count free ht hs
  have ready : RepT (layout bits) (D.L ∘ bank) (D.R ∘ bank) := by
    intro j h
    by_cases eq : j = row
    · subst j
      have kept := frame (bank row) (fun i eq => by
        have h := congrArg Fin.val (bank.injective eq)
        change 2+i.val = 0 at h
        omega)
      change (layout bits).tape row h = readAt blank (D.L (bank row)) (D.R (bank row)) (h-0)
      rw [kept.1,kept.2,sub_zero,tape x]
      exact (owner h).symm
    · change j ≠ segmentSource ops at eq
      have cell := privateReady j eq h
      rw [basisWorkspace_eq ops 0 x] at cell
      simpa only [layout,bits,Function.comp_apply,basisWorkspace,SharedPlacementAlphabet.setTape,Function.update_of_ne eq] using cell
  obtain ⟨z,G,b,post,rep,same,_,_,_,n,time,run⟩ := foreign_exec (P := Empty) Empty.elim _
    (HoareTime.liftQ capacity (FlatCoordinateCleanSchedule.realizes ops w W positive bits)) (embDn bank v) (embStk bank D) _ rfl ready
  obtain ⟨z',F,placed,_,last,projection,off⟩ := exec_emb (ι := Empty.elim) (body' := body) bank.injective
    (fun f => nomatch f) run v rfl D rfl
  obtain ⟨v',zu,clear⟩ := clearWorkTapes_exec body work distinct z' F
  let B := {F with L := fun j => if j ∈ work then [] else F.L j,
                   R := fun j => if j ∈ work then [] else F.R j}
  have blankAt j (hj : j ∈ work) : B.L j = [] ∧ B.R j = [] := by simp [B,hj]
  have initial j (hj : j ∈ work) : S.L j = [] ∧ S.R j = [] := by
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hj
    exact free i ((mem i).mp (List.mem_map_of_mem hi))
  have bill : tapeCharge cleanupWeight work S = 4*work.length := by
    unfold tapeCharge
    rw [List.map_congr_left (g := fun _ => 4) (fun j hj => by simp [cleanupWeight,(initial j hj).1,(initial j hj).2])]
    simp [List.map_const',Nat.mul_comm]
  let addr := ((FlatCoordinateLayout.rankEquiv (Q := prime^w) (d := d)).prodCongr (Equiv.refl (Fin W))).trans finProdFinEquiv
  let y := fun i => x (addr (perm.symm (addr.symm i).1,(addr.symm i).2))
  have move a j : y (addr (perm a,j)) = x (addr (a,j)) := by
    simp only [y,Equiv.symm_apply_apply]
  have encoded : FlatCoordinateInitializedSchedule.array ops w W positive bits =
      fun i => SparseRoleCircuit.encode (y i) := by
    funext i
    obtain ⟨⟨a,j⟩,rfl⟩ := addr.surjective i
    obtain ⟨a,rfl⟩ := perm.surjective a
    rw [move]
    have step := FlatCoordinateInitializedSchedule.array_entry ops w W positive bits a j
    exact (congrArg (fun z : Fin d → ZMod (prime^w) =>
      FlatCoordinateInitializedSchedule.array ops w W positive bits (addr (z,j))) (action a)).symm.trans step
  refine ⟨y,v',B,_,(start.seq placed).seq clear,zu.trans (last.trans (same.trans user)),?_,?_,move,
    fun j hj => blankAt _ ((mem j).mpr hj),?_⟩
  · have paid := cleanupBound_clearBank work distinct (charge.seq (foreignCleanupBound placed))
      (le_refl (tapeCharge cleanupWeight work F+1)) blankAt
      (fun j => by by_cases h : j ∈ work <;> simp [B,h])
    rw [bill] at paid
    have length : work.length ≤ FlatCoordinateCleanSchedule.tapeCount ops := by
      simpa only [work,slots,List.length_map,List.length_finRange] using
        (List.length_filter_le (l := List.finRange (FlatCoordinateCleanSchedule.tapeCount ops)) (p := fun j => decide (j ≠ segmentSource ops)))
    intro js nd
    exact (paid js nd).trans (by unfold portBasisCost; dsimp only; gcongr; exact time)
  · intro h
    rw [post.1,encoded,← projection] at rep
    have keep : bank row ∉ work := fun hj => (mem row).mp hj rfl
    simp only [B,ite_eq_right keep]
    rw [← tape y]
    have cell := (rep row h).symm
    change readAt blank (F.L (bank row)) (F.R (bank row)) (h-0) = _ at cell
    rwa [sub_zero] at cell
  · intro j hj
    have away : j ∉ work := fun h => by obtain ⟨i,_,eq⟩ := List.mem_map.mp h; exact hj i eq
    have a := off j hj
    have b := frame j (fun i => hj _)
    simpa only [B,ite_eq_right away] using And.intro (a.1.trans b.1) (a.2.trans b.2)

private theorem portBasisCost_linear (ops : List (FlatCoordinateSchedule.Op 16)) :
    ∃ C : ℕ, ∀ w W, 0 < W → portBasisCost ops w W ≤ C*((prime^w)^16*W) := by
  let tapes := FlatCoordinateCleanSchedule.tapeCount ops
  let rate := FlatCoordinateCleanSchedule.constant ops
  refine ⟨13*rate*(tapes+5)+4*tapes+119,?_⟩
  intro w W positive
  let V := (prime^w)^16*W
  have hp := Shared50ModularControl.prime_prime
  have radix : 0 < prime^w := pow_pos hp.pos _
  have width : w ≤ prime^w := (Nat.lt_two_pow_self.le).trans (Nat.pow_le_pow_left hp.two_le _)
  have small : w ≤ V := width.trans ((Nat.le_self_pow (by decide : 16 ≠ 0) _).trans (Nat.le_mul_of_pos_right _ positive))
  have count : W ≤ V := Nat.le_mul_of_pos_left _ (pow_pos radix _)
  have sizes (k : ℕ) : k.size ≤ k := Nat.size_le.mpr Nat.lt_two_pow_self
  have fixed := Nat.le_mul_of_pos_right (4*tapes+103) (positive.trans_le count)
  change 8*(w.size+W.size)+24+13*(rate*V*(tapes+5)+6)+4*tapes+1 ≤ (13*rate*(tapes+5)+4*tapes+119)*V
  nlinarith only [fixed,(sizes w).trans small,(sizes W).trans count]

/-- A coordinate action on a live binary row with a fixed linear cost and
reusable private tapes. -/
def RunsPortAction (ops : List (FlatCoordinateSchedule.Op 16)) (C : ℕ)
    (action : ∀ w : ℕ, (Fin 16 → ZMod (prime^w)) → (Fin 16 → ZMod (prime^w))) : Prop :=
    ∀ {P U : Type} {T Q : ℕ}
      (body : P → Pr P T Q prime U), stateCount (FlatCoordinateCleanSchedule.program ops) ≤ Q →
      ∀ (bank : Fin (FlatCoordinateCleanSchedule.tapeCount ops) ↪ Fin T)
        (source : Fin 2 → Fin T) (tmp saved : Fin T),
      (∀ i j, bank (basisSeedPorts ops i) ≠ source j) →
      (∀ i, [source i,bank (basisSeedPorts ops i),tmp,saved].Nodup) →
      ∃ code, ∀ w W, 0 < W → ∀ (x : Fin ((prime^w)^16*W) → ZMod 2) u (S : Stacks T prime),
        let row := segmentSource ops
        S.R (source 0) = binSyms w.size w → S.R (source 1) = binSyms W.size W →
        (∀ h, readAt blank (S.L (bank row)) (S.R (bank row)) h = (portOwner x).tape 0 h) →
        (∀ j, j ≠ row → S.L (bank j) = [] ∧ S.R (bank j) = []) → S.R tmp = [] → S.R saved = [] →
        ∃ (y : Fin ((prime^w)^16*W) → ZMod 2), ∃ z F n, Exec body code (mk u S) n (mk z F) ∧
          z.user = u.user ∧ CleanupBound S F n (C*((prime^w)^16*W)) ∧
          (∀ h, readAt blank (F.L (bank row)) (F.R (bank row)) h = (portOwner y).tape 0 h) ∧
          (∀ a j, y (FlatCoordinateLayout.index (action w a) j) =
            x (FlatCoordinateLayout.index a j)) ∧
          ∀ j, j ≠ bank row → F.L j = S.L j ∧ F.R j = S.R j

private theorem scratch_ne_caller {T K : ℕ} (i : Fin K) (j : Fin T) : i.natAdd T ≠ j.castAdd K := by
  intro eq
  have h := congrArg Fin.val eq
  change T+i.val = j.val at h
  omega

/-- Execute a charged pass in the swap's workspace. All caller tapes
other than the payload are restored and the entire scratch suffix is reusable. -/
theorem RunsPortAction.onSwapBank {ops C action} (run : RunsPortAction ops C action)
    {P U : Type} {T K Q : ℕ} (body : P → Pr P (T+(24+K)) Q prime U)
    (capacity : stateCount (FlatCoordinateCleanSchedule.program ops) ≤ Q)
    (fits : FlatCoordinateCleanSchedule.tapeCount ops ≤ 1+(24+K))
    (io tmp saved : Fin T) (source : Fin 2 → Fin T)
    (regs : ∀ i, [source i,tmp,saved].Nodup) :
    ∃ code, ∀ w W, 0 < W → ∀ (x : Fin ((prime^w)^16*W) → ZMod 2) u (S : Stacks (T+(24+K)) prime),
      S.R ((source 0).castAdd _) = binSyms w.size w →
      S.R ((source 1).castAdd _) = binSyms W.size W →
      (∀ h, readAt blank (S.L (io.castAdd _)) (S.R (io.castAdd _)) h = (portOwner x).tape 0 h) →
      (∀ j : Fin (24+K), S.L (j.natAdd T) = [] ∧ S.R (j.natAdd T) = []) →
      S.R (tmp.castAdd _) = [] → S.R (saved.castAdd _) = [] →
      ∃ (y : Fin ((prime^w)^16*W) → ZMod 2), ∃ z F n, Exec body code (mk u S) n (mk z F) ∧
        z.user = u.user ∧ CleanupBound S F n (C*((prime^w)^16*W)) ∧
        (∀ h, readAt blank (F.L (io.castAdd _)) (F.R (io.castAdd _)) h = (portOwner y).tape 0 h) ∧
        (∀ a j, y (FlatCoordinateLayout.index (action w a) j) = x (FlatCoordinateLayout.index a j)) ∧
        (∀ j : Fin (24+K), F.L (j.natAdd T) = [] ∧ F.R (j.natAdd T) = []) ∧
        ∀ j : Fin T, j ≠ io → F.L (j.castAdd _) = S.L (j.castAdd _) ∧ F.R (j.castAdd _) = S.R (j.castAdd _) := by
  let bank := portPassPlacement io fits
  have row : bank (segmentSource ops) = io.castAdd _ := portPassPlacement_row io fits _
  have apart (i : Fin 2) (j : Fin T) : bank (basisSeedPorts ops i) ≠ j.castAdd _ := by
    have pos : 0 < (basisSeedPorts ops i).val := by change 0 < 2+i.val; omega
    rw [show bank (basisSeedPorts ops i) = _ from portPassPlacement_scratch io fits _ pos]
    exact scratch_ne_caller _ _
  obtain ⟨code,exec⟩ := run body capacity bank (fun i => (source i).castAdd _) (tmp.castAdd _) (saved.castAdd _)
    (fun i j => apart i (source j)) (fun i => by
      have h := regs i
      have ht := apart i tmp
      have hs := apart i saved
      simp_all [List.nodup_cons,Ne.symm (apart i (source i))])
  refine ⟨code,?_⟩
  intro w W pos x u S width count owner fresh ht hs
  obtain ⟨y,z,F,n,e,user,paid,out,act,frame⟩ := exec w W pos x u S width count (row ▸ owner)
    (fun j ne => by
      have nz : 0 < j.val := Nat.pos_of_ne_zero (fun zero => ne (Fin.ext zero))
      simpa only [bank,portPassPlacement_scratch io fits j nz] using fresh ⟨j.val-1,by omega⟩) ht hs
  rw [row] at out frame
  refine ⟨y,z,F,n,e,user,paid,out,act,?_,fun j ne => frame _ (fun eq => ne (Fin.castAdd_inj.mp eq))⟩
  intro j
  obtain ⟨left,right⟩ := frame _ (scratch_ne_caller j io)
  exact ⟨left.trans (fresh j).1,right.trans (fresh j).2⟩

private theorem runPortAction (ops : List (FlatCoordinateSchedule.Op 16))
    (action : ∀ w : ℕ, (Fin 16 → ZMod (prime^w)) → (Fin 16 → ZMod (prime^w)))
    (actions : ∀ w, ∃ perm : (Fin 16 → ZMod (prime^w)) ≃ (Fin 16 → ZMod (prime^w)),
      (∀ x, OrderedAffine.run (ops.map (fun op => op.action w)) x = perm x) ∧ ∀ x, perm x = action w x) :
    ∃ C, RunsPortAction ops C action := by
  obtain ⟨C,bound⟩ := portBasisCost_linear ops
  refine ⟨C,?_⟩
  intro P U T Q body capacity bank source tmp saved apart regs
  obtain ⟨code,run⟩ := runPortBasis ops body capacity bank source tmp saved apart regs
  refine ⟨code,?_⟩
  intro w W positive x u S row width count owner free ht hs
  obtain ⟨perm,action,matrix⟩ := actions w
  obtain ⟨y,z,F,n,exec,user,charge,result,move,blank,frame⟩ :=
    run w W positive x u S perm action width count owner free ht hs
  refine ⟨y,z,F,n,exec,user,(fun js nd => (charge js nd).trans
    (Nat.add_le_add_left (bound w W positive) _)),result,fun a j => matrix a ▸ move a j,?_⟩
  intro j off
  by_cases inside : ∃ i, bank i = j
  · obtain ⟨i,rfl⟩ := inside
    have ne : i ≠ row := fun eq => off (congrArg bank eq)
    exact ⟨(blank i ne).1.trans (free i ne).1.symm,(blank i ne).2.trans (free i ne).2.symm⟩
  · exact frame j (fun i eq => inside ⟨i,eq⟩)

open Matrix IntegerMultBounds.Swap.Modular in
theorem runRationalPortBasis (t : Fin 111) (atExit inverse : Bool) :
    ∃ ops C, RunsPortAction ops C (fun w a => let B := reduce (prime^w) (rationalPortBasis t atExit)
      (if inverse then B⁻¹ else B) *ᵥ a) := by
  obtain ⟨ops,actions⟩ := rationalPortBasis_schedule t atExit inverse
  exact ⟨ops,runPortAction ops _ actions⟩

open Matrix AffineFieldCoordinates IntegerMultBounds.Swap.Modular in
/-- The two entry transformations share a single header load and cleanup. -/
theorem runPortCorrectionEntry (t : Fin 111) (atExit reflect : Bool) :
    ∃ ops C, RunsPortAction ops C (fun w a =>
      let B := reduce (prime^w) (rationalPortBasis t atExit)
      let s := (Fin.appendEquiv (α := ZMod (prime^w)) 8 8).symm (B⁻¹ *ᵥ a)
      embed (AffineFieldProgram.execute (if reflect then .subFromD 0 7 else .addToD 0 7) s)) := by
  obtain ⟨ops,actions⟩ := portCorrectionEntry_schedule t atExit reflect
  refine ⟨ops,runPortAction ops _ ?_⟩
  intro w
  obtain ⟨perm,run,act⟩ := actions w
  exact ⟨perm,run,fun a => act a _ ((Fin.appendEquiv (α := ZMod (prime^w)) 8 8).apply_symm_apply _).symm⟩

open Matrix AffineFieldCoordinates IntegerMultBounds.Swap.Modular in
/-- After the swap, the inverse correction reflects the high digit, negates
the low digit and returns to the selected basis in a single charged run. -/
theorem runInversePortCorrectionExit (t : Fin 111) (atExit : Bool) :
    ∃ ops C, RunsPortAction ops C (fun w x =>
      let s := (Fin.appendEquiv (α := ZMod (prime^w)) 8 8).symm x
      let reflected := embed (AffineFieldProgram.execute (.subFromD 0 7) s)
      reduce (prime^w) (rationalPortBasis t atExit) *ᵥ
        OrderedAffine.execute (.scale (dIndex (Fin.last 7)) (-1)) reflected) := by
  obtain ⟨digit,digitAction⟩ := forwardDigit_schedule true
  obtain ⟨basis,basisAction⟩ := rationalPortBasis_schedule t atExit false
  let i := dIndex (Fin.last 7)
  have one : 1 ≤ coefficientBound := Nat.one_le_two_pow
  let neg : FlatCoordinateSchedule.Op 16 := .scale i (-1)
    (Or.inr ⟨by decide,by simpa using one,by simpa using one⟩)
  refine ⟨digit ++ neg :: basis,runPortAction _ _ ?_⟩
  intro w
  obtain ⟨p,runP,actP⟩ := digitAction w
  obtain ⟨q,runQ,actQ⟩ := basisAction w
  let f := OrderedAffine.execute (.scale i (-1 : ZMod (prime^w)))
  have invol : Function.Involutive f := by
    intro x
    funext j
    by_cases h : j = i <;> simp [f,OrderedAffine.execute,Function.update_apply,h]
  let flip : (Fin 16 → ZMod (prime^w)) ≃ _ := ⟨f,f,invol,invol⟩
  refine ⟨(p.trans flip).trans q,?_,?_⟩
  · intro x
    rw [List.map_append,M8.AtomSegment.run_append,runP]
    change OrderedAffine.run _ (OrderedAffine.execute (neg.action w) (p x)) = q (f (p x))
    have step : neg.action w = .scale i (-1) := by
      change OrderedAffine.Op.scale i (ratMod (ActualAffineScaling.modulus w) (-1)) = _
      rw [M8.AtomSegment.ratMod_neg_one]
    rw [step]
    exact runQ (f (p x))
  · intro x
    let halves := Fin.appendEquiv (α := ZMod (prime^w)) 8 8
    have reflected := actP (halves.symm x)
    change p (halves (halves.symm x)) = _ at reflected
    rw [halves.apply_symm_apply] at reflected
    change q (f (p x)) = _
    rw [actQ,reflected]
    rfl

open AffineFieldCoordinates in
/-- Swapping physical coordinates 0 and 15 between the two reflected
passes undoes the shift in chart coordinates, for every input row. -/
theorem inversePortDigits_cancel {R : Type*} [CommRing R] (x : Fin 16 → R) :
    let halves := Fin.appendEquiv (α := R) 8 8
    let shifted := OrderedAffine.execute (.shift (hIndex (0 : Fin 8)) (dIndex (Fin.last 7)) 1) x
    let reflect := fun a => embed (AffineFieldProgram.execute (.subFromD 0 7) (halves.symm a))
    OrderedAffine.execute (.scale (dIndex (Fin.last 7)) (-1))
      (reflect (reflect shifted ∘ Equiv.swap 0 15)) = x := by
  intro halves shifted reflect
  let s := halves.symm x
  have packed : embed s = x := halves.apply_symm_apply x
  let entered := AffineFieldProgram.execute (.subFromD 0 7) (halves.symm shifted)
  have swapped : embed entered ∘ Equiv.swap 0 15 =
      embed (AffineFieldProgram.execute (.interchange 0 7) entered) := by
    funext i
    fin_cases i <;> rfl
  change OrderedAffine.execute _ (embed (AffineFieldProgram.execute _
    (halves.symm (embed entered ∘ Equiv.swap 0 15)))) = x
  rw [swapped]
  change OrderedAffine.execute _ (embed (AffineFieldProgram.execute _
    (halves.symm (halves (AffineFieldProgram.execute (.interchange 0 7) entered))))) = x
  rw [halves.symm_apply_apply]
  refine Eq.trans ?_ packed
  have splitRow (a : Fin 16 → R) : halves.symm a = (a ∘ hIndex,a ∘ dIndex) := by
    apply halves.injective
    rw [halves.apply_symm_apply]
    funext i
    induction i using Fin.addCases (m := 8) (n := 8) with
    | left i => exact (embed_h (a ∘ hIndex,a ∘ dIndex) i).symm
    | right i => exact (embed_d (a ∘ hIndex,a ∘ dIndex) i).symm
  simpa only [entered,splitRow,shifted,packed] using inverseShift_reflect_swap s

open Matrix AffineFieldCoordinates IntegerMultBounds.Swap.Modular in
/-- The two charged passes surrounding the physical swap invert the selected
port exchange on every row, for both the entry and exit projectors. -/
theorem inversePortCorrection_passes (t : Fin 111) (atExit : Bool) :
    ∃ before after C D entry exit, RunsPortAction before C entry ∧ RunsPortAction after D exit ∧
      ∀ w (s : IntegerMultBounds.Swap.Shear.State (Fin 8) (ZMod (prime^w))),
        let P := translatedPortProjector (ZMod (prime^w)) (4:ZMod (prime^w))⁻¹ t
        let U := reduce (prime^w) (selectedProjector ⟨2+t.val,by omega⟩)
        let T := reduce (prime^w) (selectedProjector ⟨525+t.val,by omega⟩)
        let moved := if atExit then M8.Exchange.exchange T (M8.Exchange.exchange (1-P) s)
          else M8.Exchange.exchange P (M8.Exchange.exchange U s)
        exit w (entry w (embed moved) ∘ Equiv.swap 0 15) = embed s := by
  obtain ⟨before,C,entry⟩ := runPortCorrectionEntry t atExit true
  obtain ⟨after,D,exit⟩ := runInversePortCorrectionExit t atExit
  refine ⟨before,after,C,D,_,_,entry,exit,?_⟩
  intro w s P U T moved
  let B := reduce (prime^w) (rationalPortBasis t atExit)
  have red : B = _ := (rationalPortBasis_reduction w t atExit).2
  obtain ⟨_,unit,correct⟩ := portBasis_shift w t atExit
  rw [← red] at unit correct
  let coords := B⁻¹ *ᵥ embed s
  have enter : B *ᵥ coords = embed s := by
    rw [show B *ᵥ coords = (B*B⁻¹) *ᵥ embed s from mulVec_mulVec ..,
      mul_nonsing_inv B ((isUnit_iff_isUnit_det B).mp unit),one_mulVec]
  let step := OrderedAffine.execute (.shift (hIndex (0 : Fin 8)) (dIndex (Fin.last 7)) 1) coords
  have leave : B *ᵥ step = embed moved := correct coords s enter
  have back : B⁻¹ *ᵥ embed moved = step := by
    rw [← leave,mulVec_mulVec,nonsing_inv_mul B ((isUnit_iff_isUnit_det B).mp unit),one_mulVec]
  let reflect := fun a => embed (AffineFieldProgram.execute (.subFromD 0 7)
    ((Fin.appendEquiv (α := ZMod (prime^w)) 8 8).symm a))
  change B *ᵥ OrderedAffine.execute (.scale (dIndex (Fin.last 7)) (-1))
    (reflect (reflect (B⁻¹ *ᵥ embed moved) ∘ Equiv.swap 0 15)) = embed s
  rw [back]
  exact (congrArg (B *ᵥ ·) (inversePortDigits_cancel coords)).trans enter

/-- Total charge of the correction on a row of volume V. -/
noncomputable def portCorrectionTime [M8.Machine.Net] (C D push tapes K w H J V : ℕ) : ℕ :=
  let setup := dimensionTime H 1 16 + (4*(16*H+1)+6) + (10*J+12) + (21*(w+1)+12) + 2
  let run := (3808274*V + M8.RevMachine.LeafCore.coreCost V (w+1))*(tapes+5)+6
  C*V+((1+6*push)*setup+13*run+4*(24+K)+1)+D*V

/-- With the caller's canonical binary headers, all work outside the
interchange core has a fixed linear charge in the physical row volume. -/
theorem portCorrectionTime_bound [M8.Machine.Net] (C D push tapes K : ℕ) :
    ∃ rate : ℕ, ∀ w W, 0 < W →
      let M := prime^(w+1)
      let V := M^16*W
      portCorrectionTime C D push tapes K w M.size W.size V ≤
        rate*V + 13*(tapes+5)*M8.RevMachine.LeafCore.coreCost V (w+1) := by
  refine ⟨C+D+(1+6*push)*10000+13*3808274*(tapes+5)+78+4*(24+K)+1,?_⟩
  intro w W pos M V
  have hm : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have size (n : ℕ) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have square : M.size*M.size ≤ V := calc
    _ ≤ M*M := Nat.mul_le_mul (size M) (size M)
    _ = M^2 := (sq M).symm
    _ ≤ M^16 := Nat.pow_le_pow_right hm (by decide)
    _ ≤ V := Nat.le_mul_of_pos_right _ pos
  have radix : M ≤ V := (Nat.le_self_pow (by decide : 16 ≠ 0) _).trans (Nat.le_mul_of_pos_right _ pos)
  have clock : w+1 ≤ M := Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left Shared50ModularControl.prime_prime.two_le _)
  have count : W ≤ V := Nat.le_mul_of_pos_left _ (pow_pos hm _)
  have positive := pos.trans_le count
  have setup : dimensionTime M.size 1 16 + (4*(16*M.size+1)+6) + (10*W.size+12) + (21*(w+1)+12) + 2 ≤ 10000*V := by
    nlinarith only [dimensionTime_le M.size 1 16,square,(size M).trans radix,(size W).trans count,clock.trans radix,positive]
  have overhead := Nat.mul_le_mul_left (1+6*push) setup
  have fixed := Nat.le_mul_of_pos_right (78+4*(24+K)+1) positive
  unfold portCorrectionTime
  nlinarith only [overhead,fixed]

open M8.RevMachine in
/-- The full physical correction inherits the supplied interchange exponent. -/
theorem portCorrectionTime_width_bound [M8.Machine.Net] (C D push tapes K : ℕ) :
    ∃ rate : ℝ, ∀ w W, 0 < W →
      let M := prime^(w+1)
      let V := M^16*W
      (portCorrectionTime C D push tapes K w M.size W.size V : ℝ) ≤
        rate*(V : ℝ)*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau := by
  obtain ⟨a,linear⟩ := portCorrectionTime_bound C D push tapes K
  refine ⟨a+(13*(tapes+5) : ℕ)*|LeafCore.C|,?_⟩
  intro w W pos M V
  let width := ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
  have one : 1 ≤ width := Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 w)
    M8.Machine.BudgetBound.exponent_range.1.le
  have core := RevBudget.coreCost_le V (w+1) (L := width)
    (by rw [max_eq_right (by omega : 1 ≤ w+1)])
  have bound : (portCorrectionTime C D push tapes K w M.size W.size V : ℝ) ≤
      (a : ℝ)*V+(13*(tapes+5) : ℕ)*(LeafCore.coreCost V (w+1) : ℝ) := by
    exact_mod_cast linear w W pos
  have fixed := le_mul_of_one_le_right (by positivity : 0 ≤ (a : ℝ)*V) one
  exact bound.trans ((add_le_add fixed (mul_le_mul_of_nonneg_left core
    (by positivity : 0 ≤ ((13*(tapes+5) : ℕ) : ℝ)))).trans_eq (by dsimp only [width]; ring))

open Cover in
/-- Run both charged coordinate passes and the physical digit swap on one
caller row. The program is independent of the precision and spectator count. -/
theorem runPortPasses [M8.Machine.Net] {before after C D entry exit}
    (left : RunsPortAction before C entry) (right : RunsPortAction after D exit)
    {P U : Type} {T K Q : ℕ} (body : P → Pr P (T+(24+K)) Q prime U)
    (io tmp saved : Fin T) (source : Fin 2 → Fin T) (r : Fin 14 ↪ Fin (T+(24+K)))
    (regs : ∀ i, [source i,tmp,saved,io].Nodup)
    (apart : ∀ i, r i ≠ io.castAdd _)
    (capL : stateCount (FlatCoordinateCleanSchedule.program before) ≤ Q)
    (capR : stateCount (FlatCoordinateCleanSchedule.program after) ≤ Q)
    (fitL : FlatCoordinateCleanSchedule.tapeCount before ≤ 1+(24+K))
    (fitR : FlatCoordinateCleanSchedule.tapeCount after ≤ 1+(24+K)) :
    let block := LabelSwap.program (0 : Fin 1)
    ∀ (cap : block.states ≤ Q) (fit : block.tapes ≤ 1+(24+K)),
    let hdr := swapHeaderPort (T := T) (N := T+(24+K)) (by omega)
    let setup : Pr P (T+(24+K)) Q prime U := (swapRuntimeHeaders r 16).seq
      ((writeSwapConstants (T := T) (by omega) 16 (0 : Fin 16) 15).seq (markSwapHeaders (T := T) (by omega)))
    r 2 = hdr 5 → r 11 = hdr 14 → r 13 = hdr 8 →
    ∃ code, ∀ w W H J, 0 < W → prime^(w+1) < 2^H → W < 2^J →
      let V := (prime^(w+1))^16*W
      ∀ (x : Fin V → ZMod 2) u (S : Stacks (T+(24+K)) prime),
      S.R ((source 0).castAdd _) = binSyms (w+1).size (w+1) → S.R ((source 1).castAdd _) = binSyms W.size W →
      S.R (tmp.castAdd _) = [] → S.R (saved.castAdd _) = [] →
      S.R (r 0) = binSyms H (prime^(w+1)) → S.R (r 1) = binSyms 1 1 →
      S.R (r 10) = binSyms J W → (S.R (r 12)).length = w →
      (∀ k : Fin 14, 3 ≤ k → k < 9 → S.R (r k) = []) →
      (∀ h, readAt blank (S.L (io.castAdd _)) (S.R (io.castAdd _)) h = (portOwner x).tape 0 h) →
      (∀ k : Fin (24+K), S.L (k.natAdd T) = [] ∧ S.R (k.natAdd T) = []) →
      ∃ (y : Fin V → ZMod 2), ∃ z F n, Exec body code (mk u S) n (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F n (portCorrectionTime C D (Fast.Main.mnProgPush setup) block.tapes K w H J V) ∧
        (∀ h, readAt blank (F.L (io.castAdd _)) (F.R (io.castAdd _)) h = (portOwner y).tape 0 h) ∧
        (∀ a j, y (FlatCoordinateLayout.index (exit (w+1) (entry (w+1) a ∘ Equiv.swap 0 15)) j) =
          x (FlatCoordinateLayout.index a j)) ∧
        (∀ k : Fin (24+K), F.L (k.natAdd T) = [] ∧ F.R (k.natAdd T) = []) ∧
        ∀ k : Fin T, k ≠ io → F.L (k.castAdd _) = S.L (k.castAdd _) ∧ F.R (k.castAdd _) = S.R (k.castAdd _) := by
  intro block cap fit hdr setup power spectator exponent
  have nodup i : [source i,tmp,saved].Nodup := by have h := regs i; simp_all [List.nodup_cons]
  obtain ⟨a,start⟩ := left.onSwapBank body capL fitL io tmp saved source nodup
  obtain ⟨b,finish⟩ := right.onSwapBank body capR fitR io tmp saved source nodup
  let bank := (Fin.castLEEmb fit).trans (portSwapPlacement io K)
  let swap := (setup.seq (embProg bank Empty.elim (foreign (liftQ block.program cap)))).seq
    (clearWorkTapes ((List.finRange (24+K)).map (Fin.natAdd T)))
  refine ⟨(a.seq swap).seq b,?_⟩
  intro w W H J pos baseFits widthFits V x u S width count ht hs base unit spectators clock scratch owner fresh
  obtain ⟨y,v,A,l,ea,ua,ca,ya,actA,cleanA,frameA⟩ := start (w+1) W pos x u S width count owner fresh ht hs
  have keep (k : Fin (T+(24+K))) (ne : k ≠ io.castAdd _) : A.R k = S.R k := by
    induction k using Fin.addCases with
    | left k => exact (frameA k (fun eq => ne (congrArg (Fin.castAdd _) eq))).2
    | right k => exact (cleanA k).2.trans (fresh k).2.symm
  have cleanTail (k : Fin (T+(24+K))) (hk : T ≤ k.val) : A.L k = [] ∧ A.R k = [] := by
    let j : Fin (24+K) := ⟨k.val-T,by omega⟩
    have eq : k = j.natAdd T := Fin.ext (by change k.val = T+(k.val-T); omega)
    exact eq ▸ cleanA j
  obtain ⟨z,q,B,m,ub,eb,cb,cleanB,frameB,zb,actB⟩ :=
    runPortSwap body io r (0 : Fin 16) 15 (by decide) w W H J pos baseFits widthFits cap fit y
      power spectator exponent v A ((keep _ (apart 0)).trans base) ((keep _ (apart 1)).trans unit)
      ((keep _ (apart 10)).trans spectators) ((congrArg List.length (keep _ (apart 12))).trans clock)
      (fun k h l => (keep _ (apart k)).trans (scratch k h l)) ya
      (fun k => cleanTail _ (by change T ≤ T+k.val; omega)) (fun k h => cleanTail k (by omega))
  have old (k : Fin T) (ne : k ≠ io) := (frameB k ne).2.trans (frameA k ne).2
  have off i : source i ≠ io ∧ tmp ≠ io ∧ saved ≠ io := by have h := regs i; simp_all [List.nodup_cons]
  obtain ⟨out,f,F,n,ec,uc,cc,represented,actC,cleanC,frameC⟩ := finish (w+1) W pos z q B
    ((old _ (off 0).1).trans width) ((old _ (off 1).1).trans count) zb cleanB
    ((old _ (off 0).2.1).trans ht) ((old _ (off 0).2.2).trans hs)
  refine ⟨out,f,F,l+m+n,(ea.seq eb).seq ec,uc.trans (ub.trans ua),?_,represented,?_,cleanC,?_⟩
  · have vol : RecursiveInterchangeLayout.volume prime (payloadView prime 16 (w+1) W) = V := by
      simp [V,payloadView,RecursiveInterchangeLayout.volume,← pow_mul,Nat.mul_comm]
    rw [vol] at cb
    exact (ca.seq cb).seq cc
  · intro coords j
    exact (actC _ j).trans ((actB _ j).trans (actA coords j))
  · intro k ne
    exact ⟨(frameC k ne).1.trans ((frameB k ne).1.trans (frameA k ne).1),(frameC k ne).2.trans (old k ne)⟩

/-- Embed the canonical swap layout using the worker's existing 35 record
slots and the first 24 slots of the shared correction workspace. -/
def workerSwapLayout {T K : ℕ} (record : Fin 35 ↪ Fin T) : Fin 59 ↪ Fin (T+(24+K)) :=
  (finSumFinEquiv.symm.toEmbedding.trans (record.sumMap (Fin.castAddEmb (n := 24) K))).trans finSumFinEquiv.toEmbedding

/-- The swap reads its modulus, spectator count, unit and shortened clock
directly from the worker record. Its three outputs land in the shared headers. -/
theorem workerSwapLayout_ready [M8.Machine.Net] {T K : ℕ} (record : Fin 35 ↪ Fin T)
    (w W : ℕ) (archive destL destR : List (Fin (prime+4))) (S : Stacks (T+(24+K)) prime) :
    let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let seed := moveRecordSeed w W archive destL destR
    let r := swapSetupPorts.trans (workerSwapLayout (K := K) record)
    let hdr := swapHeaderPort (T := T) (N := T+(24+K)) (by omega)
    (∀ i : Fin 35, i ≠ 24 → S.R ((record i).castAdd _) = seed.R (small i)) →
    (∀ i, r i ≠ (record 24).castAdd _) ∧ r 2 = hdr 5 ∧ r 11 = hdr 14 ∧ r 13 = hdr 8 ∧
    S.R (r 0) = binSyms (prime^(w+1)).size (prime^(w+1)) ∧ S.R (r 1) = binSyms 1 1 ∧
    S.R (r 10) = binSyms W.size W ∧ (S.R (r 12)).length = w ∧
    ∀ k : Fin 14, 3 ≤ k → k < 9 → S.R (r k) = [] := by
  intro small seed r hdr read
  have off : ∀ i, swapSetupPorts i ≠ (24 : Fin 59) := by decide
  refine ⟨fun i => (workerSwapLayout record).injective.ne (off i),rfl,rfl,rfl,
    read 2 (by decide),read 28 (by decide),read 27 (by decide),?_,?_⟩
  · change (S.R ((record 33).castAdd _)).length = w
    rw [read 33 (by decide)]
    exact List.length_replicate ..
  · intro k lo hi
    have cases : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := (by decide : ∀ j : Fin 14, 3 ≤ j → j < 9 → j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8) k lo hi
    rcases cases with h|h|h|h|h|h <;> subst k <;> first | exact read 3 (by decide) | exact read 4 (by decide) | exact read 5 (by decide) | exact read 6 (by decide) | exact read 7 (by decide) | exact read 8 (by decide)

open Cover Matrix AffineFieldCoordinates IntegerMultBounds.Swap.Modular in
/-- Run a selected inverse port correction on the shared payload of a loaded
worker record. The archive and destination stacks may already be live. -/
theorem runWorkerPortCorrection [M8.Machine.Net] (t : Fin 111) (atExit : Bool) :
    ∃ q k : ℕ, ∀ {P U : Type} {T K Q : ℕ}, q ≤ Q → k ≤ K →
      ∀ (body : P → Pr P (T+(24+K)) Q prime U) (record : Fin 35 ↪ Fin T) (width : Fin T),
      (∀ i, width ≠ record i) →
      ∃ code rate coreRate, ∀ w W, 0 < W →
      let M := prime^(w+1)
      let V := M^16*W
      let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
      let io := (record 24).castAdd (24+K)
      ∀ archive destL destR (x : Fin V → ZMod 2) u (S : Stacks (T+(24+K)) prime),
      (∀ i : Fin 35, i ≠ 24 → S.R ((record i).castAdd _) = (moveRecordSeed w W archive destL destR).R (small i)) →
      S.R (width.castAdd _) = binSyms (w+1).size (w+1) →
      (∀ h, readAt blank (S.L io) (S.R io) h = (portOwner x).tape 0 h) →
      (∀ j : Fin (24+K), S.L (j.natAdd T) = [] ∧ S.R (j.natAdd T) = []) →
      ∃ (y : Fin V → ZMod 2), ∃ z F n, Exec body code (mk u S) n (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F n (rate*V+coreRate*M8.RevMachine.LeafCore.coreCost V (w+1)) ∧
        (∀ h, readAt blank (F.L io) (F.R io) h = (portOwner y).tape 0 h) ∧
        (∀ s j, let A := translatedPortProjector (ZMod M) (4:ZMod M)⁻¹ t
                let B := reduce M (selectedProjector ⟨2+t.val,by omega⟩)
                let E := reduce M (selectedProjector ⟨525+t.val,by omega⟩)
                let moved := if atExit then M8.Exchange.exchange E (M8.Exchange.exchange (1-A) s)
                  else M8.Exchange.exchange A (M8.Exchange.exchange B s)
                y (FlatCoordinateLayout.index (embed s) j) = x (FlatCoordinateLayout.index (embed moved) j)) ∧
        (∀ j : Fin (24+K), F.L (j.natAdd T) = [] ∧ F.R (j.natAdd T) = []) ∧
        ∀ j : Fin T, j ≠ record 24 → F.L (j.castAdd _) = S.L (j.castAdd _) ∧ F.R (j.castAdd _) = S.R (j.castAdd _) := by
  obtain ⟨a,b,C,D,entry,exit,left,right,correct⟩ := inversePortCorrection_passes t atExit
  let block := LabelSwap.program (0 : Fin 1)
  refine ⟨stateCount (FlatCoordinateCleanSchedule.program a)+stateCount (FlatCoordinateCleanSchedule.program b)+block.states,
    FlatCoordinateCleanSchedule.tapeCount a+FlatCoordinateCleanSchedule.tapeCount b+block.tapes,?_⟩
  intro P U T K Q states tapes body record width outside
  let r := swapSetupPorts.trans (workerSwapLayout (K := K) record)
  let source : Fin 2 → Fin T := ![width,record 27]
  have regs (i : Fin 2) : [source i,record 0,record 1,record 24].Nodup := by
    fin_cases i <;> simp [source,List.nodup_cons,outside,record.injective.eq_iff]
  have away (i) : r i ≠ (record 24).castAdd _ :=
    (workerSwapLayout record).injective.ne ((by decide : ∀ i, swapSetupPorts i ≠ (24 : Fin 59)) i)
  obtain ⟨code,run⟩ := runPortPasses left right body (record 24) (record 0) (record 1) source r regs away
    (by omega) (by omega) (by omega) (by omega) (by change block.states ≤ Q; omega)
    (by change block.tapes ≤ _; omega) rfl rfl rfl
  let setup : Pr P (T+(24+K)) Q prime U := (swapRuntimeHeaders r 16).seq
    ((writeSwapConstants (T := T) (by omega) 16 (0 : Fin 16) 15).seq (markSwapHeaders (T := T) (by omega)))
  obtain ⟨rate,bound⟩ := portCorrectionTime_bound C D (Fast.Main.mnProgPush setup) block.tapes K
  refine ⟨code,rate,13*(block.tapes+5),?_⟩
  intro w W pos M V small io archive destL destR x u S read atom owner fresh
  obtain ⟨_,_,_,_,base,unit,count,clock,scratch⟩ := workerSwapLayout_ready record w W archive destL destR S read
  obtain ⟨y,z,F,n,e,user,paid,out,act,clean,frame⟩ := run w W M.size W.size pos (Nat.lt_size_self M)
    (Nat.lt_size_self W) x u S atom count (read 0 (by decide)) (read 1 (by decide))
    base unit count clock scratch owner fresh
  refine ⟨y,z,F,n,e,user,(fun js nd => (paid js nd).trans (Nat.add_le_add_left (bound w W pos) _)),
    out,?_,clean,frame⟩
  intro s j A B E moved
  have h := act (embed moved) j
  rwa [correct (w+1) s] at h

private theorem correctedRecordReady [M8.Machine.Net] {T w W : ℕ}
    (bank : Fin 35 ↪ Fin T) (S : Stacks T prime) (x : Fin ((prime^(w+1))^16*W) → ZMod 2) :
    let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let seed := moveRecordSeed w W [] [] []
    (∀ i : Fin 35, i ≠ 24 → S.L (bank i) = seed.L (small i) ∧ S.R (bank i) = seed.R (small i)) →
    (∀ h, readAt blank (S.L (bank 24)) (S.R (bank 24)) h = (portOwner x).tape 0 h) →
    RecordReady (b := prime) (w := w) (d := 16) (W := W) bank (prime^(w+1)).size W.size []
      SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 x S := by
  intro small seed stored owner
  refine ⟨(stored 2 (by decide)).2,(stored 27 (by decide)).2,(stored 28 (by decide)).2,
    (stored 32 (by decide)).2,?_,(stored 34 (by decide)).2,?_,?_,?_⟩
  · rw [(stored 33 (by decide)).2]
    exact List.length_replicate ..
  · intro i hi
    have free := (by decide : ∀ j ∈ shearWork, j.val ≠ 2 ∧ j.val ≠ 24 ∧ j.val ≠ 25 ∧ j.val ≠ 27 ∧
      j.val ≠ 28 ∧ j.val ≠ 32 ∧ j.val ≠ 33 ∧ j.val ≠ 34) i hi
    obtain ⟨a,b,c,d,e,f,g,h⟩ := free
    simpa [seed,moveRecordSeed,small,a,b,c,d,e,f,g,h] using stored i (fun eq => b (congrArg Fin.val eq))
  · intro z
    rw [sub_zero,owner]
    let view := phaseIntervalChild 0 7 (w+1) W
    have size := phaseIntervalChild_volume (by decide : 0 ≤ 7) (by decide : 7 ≤ 8) (w+1) W
    change putWord _ 0 _ z = _
    rw [← sourceWord_cast (v := view) size x,swap_source_word]
    congr 2
    exact List.ofFn_congr size _
  · intro z
    rw [(stored 25 (by decide)).1,(stored 25 (by decide)).2]
    change readAt blank [] [] _ = _
    simp [readAt]
    rfl

open Matrix AffineFieldCoordinates IntegerMultBounds.Swap.Modular in
/-- Initialize an empty worker record around a live payload and apply the
selected correction. The loaded record remains available to the child. -/
theorem loadAndRunWorkerPort [M8.Machine.Net] (t : Fin 111) (atExit : Bool) :
    ∃ q k : ℕ, ∀ {P U : Type} {T K Q : ℕ}, q ≤ Q → k ≤ K →
      ∀ (body : P → Pr P (T+(24+K)) Q prime U)
        (place : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (src : Fin 3 → Fin T) (width tmp saved : Fin T),
      let record := scheduledRecordPorts place
      (∀ i, width ≠ place i) → (∀ i j, record (copyRecordTargets i) ≠ src j) →
      (∀ i, [src i,record (copyRecordTargets i),tmp,saved].Nodup) →
      ∃ code rate coreRate, ∀ w W, 0 < W →
      let M := prime^(w+1)
      let V := M^16*W
      let io := (record 24).castAdd (24+K)
      let seed := moveRecordSeed w W [] [] []
      ∀ (x : Fin V → ZMod 2) u (S : Stacks (T+(24+K)) prime),
      S.R ((src 0).castAdd _) = binSyms M.size M → S.R ((src 1).castAdd _) = binSyms W.size W →
      S.R ((src 2).castAdd _) = binSyms 1 1 → S.R (width.castAdd _) = binSyms (w+1).size (w+1) →
      (∀ i, i.val ≠ 24 → S.L ((place i).castAdd _) = [] ∧ S.R ((place i).castAdd _) = []) →
      S.R (tmp.castAdd _) = [] → S.R (saved.castAdd _) = [] →
      (∀ h, readAt blank (S.L io) (S.R io) h = (portOwner x).tape 0 h) →
      (∀ j : Fin (24+K), S.L (j.natAdd T) = [] ∧ S.R (j.natAdd T) = []) →
      ∃ (y : Fin V → ZMod 2), ∃ z F n, Exec body code (mk u S) n (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F n (rate*V+coreRate*M8.RevMachine.LeafCore.coreCost V (w+1)) ∧
        (∀ h, readAt blank (F.L io) (F.R io) h = (portOwner y).tape 0 h) ∧
        (∀ s j, let A := translatedPortProjector (ZMod M) (4:ZMod M)⁻¹ t
                let B := reduce M (selectedProjector ⟨2+t.val,by omega⟩)
                let E := reduce M (selectedProjector ⟨525+t.val,by omega⟩)
                let moved := if atExit then M8.Exchange.exchange E (M8.Exchange.exchange (1-A) s)
                  else M8.Exchange.exchange A (M8.Exchange.exchange B s)
                y (FlatCoordinateLayout.index (embed s) j) = x (FlatCoordinateLayout.index (embed moved) j)) ∧
        RecordReady (b := prime) (w := w) (d := 16) (W := W) (record.trans (Fin.castAddEmb (24+K)))
          M.size W.size [] SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 y F ∧
        (∀ i, i.val ≠ 24 → F.L ((place i).castAdd _) = seed.L i ∧ F.R ((place i).castAdd _) = seed.R i) ∧
        (∀ j : Fin (24+K), F.L (j.natAdd T) = [] ∧ F.R (j.natAdd T) = []) ∧
        ∀ j : Fin T, (∀ i, place i ≠ j) → F.L (j.castAdd _) = S.L (j.castAdd _) ∧ F.R (j.castAdd _) = S.R (j.castAdd _) := by
  obtain ⟨q,k,worker⟩ := runWorkerPortCorrection t atExit
  refine ⟨q,k,?_⟩
  intro P U T K Q states space body place src width tmp saved record outside apart regs
  let ext := Fin.castAddEmb (n := T) (24+K)
  obtain ⟨a,load⟩ := loadWorkerRecordSeed body (place.trans ext) (ext ∘ src) (ext width) (ext tmp) (ext saved)
    (fun i => ext.injective.ne (outside _)) (fun i j => ext.injective.ne (apart i j))
    (fun i => (regs i).map ext.injective)
  obtain ⟨b,rate,coreRate,run⟩ := worker states space body record width (fun i => outside _)
  refine ⟨a.seq b,rate+98,coreRate,?_⟩
  intro w W pos M V io seed x u S base count unit atom blank ht hs owner fresh
  obtain ⟨v,A,l,start,user,paid,stored,frame⟩ := load w W u S base count unit atom blank ht hs
  have ioFree := frame io (fun i ne => ext.injective.ne (place.injective.ne (fun eq => ne (congrArg Fin.val eq))))
  have clean (j : Fin (24+K)) := frame (j.natAdd T) (fun i _ => (scratch_ne_caller j (place i)).symm)
  obtain ⟨y,z,F,n,done,same,charge,out,act,reuse,keep⟩ := run w W pos [] [] [] x v A
    (fun i ne => (stored _ (fun eq => ne (Fin.ext eq))).2)
    ((frame _ (fun i _ => ext.injective.ne (outside i).symm)).2.trans atom)
    (fun h => by rw [ioFree.1,ioFree.2]; exact owner h)
    (fun j => ⟨(clean j).1.trans (fresh j).1,(clean j).2.trans (fresh j).2⟩)
  have prepared (i) (ne : i.val ≠ 24) := And.intro
    ((keep (place i) (place.injective.ne (fun eq => ne (congrArg Fin.val eq)))).1.trans (stored i ne).1)
    ((keep (place i) (place.injective.ne (fun eq => ne (congrArg Fin.val eq)))).2.trans (stored i ne).2)
  have ready := correctedRecordReady (record.trans ext) F y (fun i ne => prepared _ (fun eq => ne (Fin.ext eq))) out
  refine ⟨y,z,F,l+n,start.seq done,same.trans user,?_,out,act,ready,prepared,reuse,?_⟩
  · have hm : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
    have radix : M ≤ V := (Nat.le_self_pow (by decide : 16 ≠ 0) _).trans (Nat.le_mul_of_pos_right _ pos)
    have clock : w+1 ≤ M := Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left Shared50ModularControl.prime_prime.two_le _)
    have size (n : ℕ) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
    have spectators : W ≤ V := Nat.le_mul_of_pos_left _ (pow_pos hm _)
    intro js nd
    apply ((paid.seq charge) js nd).trans
    apply Nat.add_le_add_left
    change 18*M.size+8*W.size+8*(w+1)+11*(w+1).size+53+(rate*V+_) ≤ (rate+98)*V+_
    nlinarith only [(size M).trans radix,(size W).trans spectators,clock.trans radix,(size _).trans (clock.trans radix),pos.trans_le spectators]
  · intro j off
    have first := frame (ext j) (fun i _ => ext.injective.ne (off i))
    have last := keep j (off _).symm
    exact ⟨last.1.trans first.1,last.2.trans first.2⟩

open Matrix AffineFieldCoordinates IntegerMultBounds.Swap.Modular in
/-- Correct the live row and call the smaller scheduled child with its inherited cutoff. -/
theorem correctedInheritedWorkerCall [M8.Machine.Net] (t : Fin 111) (atExit : Bool) :
    ∃ q k : ℕ, ∀ {P U : Type} {T K Q : ℕ}, q ≤ Q → k ≤ K →
      ∀ (body : P → Pr P (T+(24+K)) Q prime U)
        (place : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (src : Fin 3 → Fin T) (width tmp saved cut : Fin T) (f : P),
      let record := scheduledRecordPorts place
      (∀ i, width ≠ place i) → (∀ i j, record (copyRecordTargets i) ≠ src j) →
      (∀ i, [src i,record (copyRecordTargets i),tmp,saved].Nodup) →
      (∀ i, place i ≠ cut) →
      ∃ code rate coreRate, ∀ w W, 0 < W →
      let M := prime^(w+1)
      let V := M^16*W
      let io := (record 24).castAdd (24+K)
      let ports := place.trans (Fin.castAddEmb (24+K))
      ∀ (node child : RecursiveInterchangeLayout.Descriptor) (L cutoff budget : ℕ)
        (position : Fin (RecursiveInterchangeLayout.volume prime child) ≃ Fin V),
      ScheduledChildExec node child w W ports (binSyms L cutoff) position body f budget true →
      child.width < node.width →
      ∀ (x : Fin V → ZMod 2) u (S : Stacks (T+(24+K)) prime),
      S.R (cut.castAdd _) = binSyms L cutoff → S.R ((src 0).castAdd _) = binSyms M.size M → S.R ((src 1).castAdd _) = binSyms W.size W →
      S.R ((src 2).castAdd _) = binSyms 1 1 → S.R (width.castAdd _) = binSyms (w+1).size (w+1) →
      (∀ i, i.val ≠ 24 → S.L ((place i).castAdd _) = [] ∧ S.R ((place i).castAdd _) = []) →
      S.R (tmp.castAdd _) = [] → S.R (saved.castAdd _) = [] →
      (∀ h, readAt blank (S.L io) (S.R io) h = (portOwner x).tape 0 h) →
      (∀ j : Fin (24+K), S.L (j.natAdd T) = [] ∧ S.R (j.natAdd T) = []) →
      ∃ (y output : Fin V → ZMod 2), ∃ z F n, Exec body code (mk u S) n (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F n (rate*V+coreRate*M8.RevMachine.LeafCore.coreCost V (w+1)+(budget+8*L+10)) ∧
        (∀ h, output (position h) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (y ∘ position) h) ∧
        (∀ s j, let A := translatedPortProjector (ZMod M) (4:ZMod M)⁻¹ t
                let B := reduce M (selectedProjector ⟨2+t.val,by omega⟩)
                let E := reduce M (selectedProjector ⟨525+t.val,by omega⟩)
                let moved := if atExit then M8.Exchange.exchange E (M8.Exchange.exchange (1-A) s)
                  else M8.Exchange.exchange A (M8.Exchange.exchange B s)
                y (FlatCoordinateLayout.index (embed s) j) = x (FlatCoordinateLayout.index (embed moved) j)) ∧
        RecordReady (b := prime) (w := w) (d := 16) (W := W) (record.trans (Fin.castAddEmb (24+K)))
          M.size W.size [] SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 output F ∧
        (∀ i, 35 ≤ i.val → F.L (ports i) = [] ∧ F.R (ports i) = []) ∧
        (∀ j : Fin (24+K), F.L (j.natAdd T) = [] ∧ F.R (j.natAdd T) = []) ∧
        ∀ j : Fin T, (∀ i, place i ≠ j) → F.L (j.castAdd _) = S.L (j.castAdd _) ∧ F.R (j.castAdd _) = S.R (j.castAdd _) := by
  obtain ⟨q,k,prepare⟩ := loadAndRunWorkerPort t atExit
  refine ⟨q,k,?_⟩
  intro P U T K Q states space body place src width tmp saved cut f record outside apart regs cutOff
  obtain ⟨a,rate,coreRate,run⟩ := prepare states space body place src width tmp saved outside apart regs
  let ext := Fin.castAddEmb (n := T) (24+K)
  let bank := record.trans ext
  let call : Pr P (T+(24+K)) Q prime U := (bcopy (ext cut) (bank 34) (bank 0) (bank 1)).seq
    ((Prog.call f).seq (bclear (bank 34)))
  refine ⟨a.seq call,rate,coreRate,?_⟩
  intro w W pos M V io ports node child L cutoff budget position worker smaller x u S header base count unit atom blank ht hs owner fresh
  obtain ⟨y,v,A,l,start,user,paid,_,act,ready,stored,clean,frame⟩ := run w W pos x u S base count unit atom blank ht hs owner fresh
  have free (i : Fin (rowSwapBlock.tapes+35)) (hi : 35 ≤ i.val) : A.L (ports i) = [] ∧ A.R (ports i) = [] := by
    have h := stored i (by omega)
    simpa [ports,moveRecordSeed,show ∀ n < 35, i.val ≠ n by omega] using h
  obtain ⟨z,F,n,out,exec,time,same,result,cleared,keep,effect⟩ :=
    inheritedWorkerCall body f ports (ext cut) (fun i => ext.injective.ne (cutOff i)) node child w W L cutoff budget
      position worker smaller v A y ((frame cut cutOff).2.trans header) ready free
  refine ⟨y,out,z,F,l+n,start.seq exec,same.trans user,paid.seq time,effect,act,result,cleared,?_,?_⟩
  · intro j
    have h := keep (j.natAdd T) (fun i => (scratch_ne_caller j (place i)).symm)
    exact ⟨h.1.trans (clean j).1,h.2.trans (clean j).2⟩
  · intro j off
    have h := keep (ext j) (fun i => ext.injective.ne (off i))
    exact ⟨h.1.trans (frame j off).1,h.2.trans (frame j off).2⟩

/-- Initialize both directions of a worker's basis change using the same
two source words and the same copy scratch. -/
theorem loadWorkerBases {P U : Type} {T Q d : ℕ} (body : P → Pr P T Q prime U)
    (ops : Bool → List (FlatCoordinateSchedule.Op d))
    (bank : ∀ side, Fin (FlatCoordinateCleanSchedule.tapeCount (ops side)) ↪ Fin T)
    (source : Fin 2 → Fin T) (tmp saved : Fin T)
    (separate : ∀ i j, bank false i ≠ bank true j)
    (outside : ∀ i, (∀ j, bank false i ≠ source j) ∧ bank false i ≠ tmp ∧ bank false i ≠ saved)
    (apart : ∀ side i j, bank side (basisSeedPorts (ops side) i) ≠ source j)
    (regs : ∀ side i, [source i,bank side (basisSeedPorts (ops side) i),tmp,saved].Nodup) :
    ∃ code, ∀ w W u (S : Stacks T prime),
      S.R (source 0) = binSyms w.size w → S.R (source 1) = binSyms W.size W →
      (∀ side j, S.L (bank side j) = [] ∧ S.R (bank side j) = []) → S.R tmp = [] → S.R saved = [] →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (16*(w.size+W.size)+48) ∧
        (∀ side j, let seed := basisHeaderStacks (ops side) w W
          F.L (bank side j) = seed.L j ∧ F.R (bank side j) = seed.R j) ∧
        ∀ j, (∀ side i, bank side i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨a,first⟩ := loadBasisWorkerSeed body (ops false) (bank false) source tmp saved (apart false) (regs false)
  obtain ⟨b,last⟩ := loadBasisWorkerSeed body (ops true) (bank true) source tmp saved (apart true) (regs true)
  refine ⟨a.seq b,?_⟩
  intro w W u S width count free ht hs
  obtain ⟨v,D,n,start,user,paid,left,frame⟩ := first w W u S (fun _ => True) (fun _ => trivial) width count (fun j _ => free false j) ht hs
  obtain ⟨z,F,t,finish,same,charge,right,keep⟩ := last w W v D (fun _ => True) (fun _ => trivial)
    ((frame _ (fun i => (outside _).1 0)).2.trans width) ((frame _ (fun i => (outside _).1 1)).2.trans count)
    (fun j _ => ⟨(frame _ (fun i => separate _ j)).1.trans (free true j).1,
      (frame _ (fun i => separate _ j)).2.trans (free true j).2⟩)
    ((frame _ (fun i => (outside _).2.1)).2.trans ht) ((frame _ (fun i => (outside _).2.2)).2.trans hs)
  refine ⟨z,F,n+t,start.seq finish,same.trans user,?_,?_,?_⟩
  · convert paid.seq charge using 1
    omega
  · intro side j
    cases side with
    | false =>
      have h := keep _ (fun i => (separate j _).symm)
      exact ⟨h.1.trans (left j trivial).1,h.2.trans (left j trivial).2⟩
    | true => exact right j trivial
  · intro j off
    exact ⟨(keep j (fun i => off true _)).1.trans (frame j (fun i => off false _)).1,
      (keep j (fun i => off true _)).2.trans (frame j (fun i => off false _)).2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
