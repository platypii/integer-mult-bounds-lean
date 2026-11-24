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
