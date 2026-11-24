module

public import IntegerMultBounds.MathlibTM2.M6.BitParentArchiveSeed
public import IntegerMultBounds.MathlibTM2.M6.BitPortRun

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)

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
          (∀ j, j ≠ row → F.L (bank j) = [] ∧ F.R (bank j) = []) ∧
          ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j

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
  exact ⟨y,z,F,n,exec,user,(fun js nd => (charge js nd).trans (Nat.add_le_add_left (bound w W positive) _)),result,fun a j => matrix a ▸ move a j,blank,frame⟩

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
