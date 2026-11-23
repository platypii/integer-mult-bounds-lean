module

public import IntegerMultBounds.MathlibTM2.M6.BitBasisWorkerSeed
public import IntegerMultBounds.MathlibTM2.M6.BitWorkerRecordSeed

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)

private theorem workerSeed_agrees {T : ℕ} {N : ℕ} (ports : Fin N ↪ Fin T)
    {ops : Bool → List (FlatCoordinateSchedule.Op 16)}
    (basis : ∀ side, Fin (FlatCoordinateCleanSchedule.tapeCount (ops side)) ↪ Fin T)
    (disjoint : ∀ side i j, ports i ≠ basis side j) (separate : ∀ i j, basis false i ≠ basis true j)
    (X : Stacks N prime) (Y : ∀ side, Stacks (FlatCoordinateCleanSchedule.tapeCount (ops side)) prime)
    (D : Stacks T prime) (j : Fin T)
    (record : ∀ i, ports i = j → D.L j = X.L i ∧ D.R j = X.R i)
    (charts : ∀ side i, basis side i = j → D.L j = (Y side).L i ∧ D.R j = (Y side).R i)
    (unused : (∀ i, ports i ≠ j) → (∀ side i, basis side i ≠ j) → D.L j = [] ∧ D.R j = []) :
    let seed := recordBasisStacks ports (basis false) (basis true) X (Y false) (Y true)
    D.L j = seed.L j ∧ D.R j = seed.R j := by
  intro seed
  obtain ⟨p,q,r⟩ := recordBasisStacks_banks ports (basis false) (basis true) (disjoint false)
    (disjoint true) separate X (Y false) (Y true)
  by_cases hit : ∃ i, ports i = j
  · obtain ⟨i,rfl⟩ := hit
    exact ⟨(record i rfl).1.trans (p i).1.symm,(record i rfl).2.trans (p i).2.symm⟩
  by_cases chart : ∃ side i, basis side i = j
  · obtain ⟨side,i,rfl⟩ := chart
    have h := charts side i rfl
    cases side with
    | false => exact ⟨h.1.trans (q i).1.symm,h.2.trans (q i).2.symm⟩
    | true => exact ⟨h.1.trans (r i).1.symm,h.2.trans (r i).2.symm⟩
  have off i eq := hit ⟨i,eq⟩
  have away side i eq := chart ⟨side,i,eq⟩
  simpa [seed,recordBasisStacks,embExt_off _ _ off,embExt_off _ _ (away false),embExt_off _ _ (away true)] using unused off away

/-- Stage setup writes slot 34 after the private loader returns. Clearing that
slot in any requested record gives exactly the loader's empty-record seed. -/
theorem WorkerBasisLayout.beforeArchive [M8.Machine.Net] {T : ℕ}
    {ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T} (layout : WorkerBasisLayout ports)
    (w W : ℕ) (record : List (Fin (prime+4))) (j : Fin T) :
    (layout.seed w W []).L j = (layout.seed w W record).L j ∧
    (layout.seed w W []).R j = Function.update (layout.seed w W record).R (scheduledRecordPorts ports 34) [] j := by
  constructor
  · rfl
  by_cases hit : ∃ i, ports i = j
  · obtain ⟨i,rfl⟩ := hit
    by_cases eq : i.val = 34
    · have e : ports i = scheduledRecordPorts ports 34 := congrArg ports (Fin.ext eq)
      rw [show Function.update (layout.seed w W record).R (scheduledRecordPorts ports 34) [] (ports i) = [] by rw [e,Function.update_self]]
      simp [WorkerBasisLayout.seed,recordBasisStacks,embExt_apply ports.injective,moveRecordSeed,eq]
    · have ne : ports i ≠ scheduledRecordPorts ports 34 := ports.injective.ne (fun e => eq (congrArg Fin.val e))
      simp [Function.update_of_ne ne,WorkerBasisLayout.seed,recordBasisStacks,embExt_apply ports.injective,moveRecordSeed,eq]
  · have off i eq := hit ⟨i,eq⟩
    have ne : j ≠ scheduledRecordPorts ports 34 := fun eq => off _ eq.symm
    simp [Function.update_of_ne ne,WorkerBasisLayout.seed,recordBasisStacks,embExt_off _ _ off]

private theorem workerSeedCost (w W : ℕ) (pos : 0 < W) :
    let M := prime^(w+1)
    18*M.size+24*W.size+8*(w+1)+27*(w+1).size+101 ≤ 178*(M^16*W) := by
  intro M
  have primePos := Shared50ModularControl.prime_prime.pos
  have live := pow_pos (pow_pos primePos (w+1)) 16
  have mass : M ≤ M^16*W := (Nat.le_self_pow (by decide : 16 ≠ 0) M).trans (Nat.le_mul_of_pos_right _ pos)
  have width : w+1 ≤ M^16*W := (Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt).le.trans mass
  have spectators : W ≤ M^16*W := Nat.le_mul_of_pos_left W live
  have size (k : ℕ) : k.size ≤ k := Nat.size_le.mpr Nat.lt_two_pow_self
  have := size M
  have := size W
  have := size (w+1)
  omega

/-- Initialize the three private banks of a basis worker. The six caller tapes
hold the modulus, spectator count, unit, atom width and two empty copy buffers. -/
theorem loadWorkerPrivateSeed [M8.Machine.Net] {P U : Type} {T Q : ℕ}
    (body : P → Pr P (T+6) Q prime U)
    (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (layout : WorkerBasisLayout ports) :
    let ops := fun side => Bool.rec layout.reverseOps layout.forwardOps side
    let basis : ∀ side, Fin (FlatCoordinateCleanSchedule.tapeCount (ops side)) ↪ Fin T :=
      fun side => Bool.rec (motive := fun b => Fin (FlatCoordinateCleanSchedule.tapeCount (ops b)) ↪ Fin T)
        layout.reverseBank layout.forwardBank side
    let localBank := Fin.castAddEmb (n := T) 6
    let caller := Fin.natAddEmb T (m := 6)
    let recBank := ports.trans localBank
    let chart := fun side => (basis side).trans localBank
    ∃ code, ∀ w W u (S : Stacks (T+6) prime),
      let M := prime^(w+1)
      0 < W → S.R (caller 0) = binSyms M.size M → S.R (caller 1) = binSyms W.size W →
      S.R (caller 2) = binSyms 1 1 → S.R (caller 3) = binSyms (w+1).size (w+1) →
      S.R (caller 4) = [] → S.R (caller 5) = [] →
      (∀ i, i.val ≠ 24 → S.L (recBank i) = [] ∧ S.R (recBank i) = []) →
      (∀ side i, S.L (chart side i) = [] ∧ S.R (chart side i) = []) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (178*(M^16*W)) ∧
        (∀ i, i.val ≠ 24 → let seed := moveRecordSeed w W [] [] []
          F.L (recBank i) = seed.L i ∧ F.R (recBank i) = seed.R i) ∧
        (∀ side i, let seed := basisHeaderStacks (ops side) (w+1) W
          F.L (chart side i) = seed.L i ∧ F.R (chart side i) = seed.R i) ∧
        (∀ j : Fin T, (∀ i, i.val = 24 → ports i ≠ j) →
          ((∀ i, ports i ≠ j) → (∀ side i, basis side i ≠ j) → S.L (localBank j) = [] ∧ S.R (localBank j) = []) →
          ∀ record, let seed := layout.seed w W record
          F.L (localBank j) = seed.L j ∧
          F.R (localBank j) = Function.update seed.R (scheduledRecordPorts ports 34) [] j) ∧
        ∀ j, (∀ i, i.val ≠ 24 → recBank i ≠ j) → (∀ side i, chart side i ≠ j) →
          F.L j = S.L j ∧ F.R j = S.R j := by
  intro ops basis localBank caller recBank chart
  have disjoint side i j : ports i ≠ basis side j := by
    cases side with
    | false => exact layout.reverseOff i j
    | true => exact layout.forwardOff i j
  have separate := layout.separate
  have apart (i : Fin T) (j : Fin 6) : localBank i ≠ caller j := by
    intro eq
    have h := congrArg Fin.val eq
    change i.val = T+j.val at h
    omega
  let recSrc := fun i : Fin 3 => caller (i.castAdd 3)
  let chartSrc := fun i : Fin 2 => caller ((![3,1] : Fin 2 → Fin 6) i)
  have distinct (s : Fin 6) (a : s ≠ 4) (b : s ≠ 5) (i : Fin T) :
      [caller s,localBank i,caller 4,caller 5].Nodup := by
    simp [List.nodup_cons,caller.injective.eq_iff,(apart i s).symm,apart i,a,b]
  obtain ⟨record,init⟩ := loadWorkerRecordSeed body recBank recSrc (caller 3) (caller 4) (caller 5)
    (fun _ => (apart _ _).symm) (fun _ _ => apart _ _) (fun j => distinct _ (by fin_cases j <;> decide)
      (by fin_cases j <;> decide) _)
  obtain ⟨bases,setup⟩ := loadWorkerBases body ops chart chartSrc (caller 4) (caller 5)
    (fun i j => localBank.injective.ne (separate i j))
    (fun _ => ⟨fun _ => apart _ _,apart _ _,apart _ _⟩) (fun _ _ _ => apart _ _)
    (fun _ j => distinct _ (by fin_cases j <;> decide) (by fin_cases j <;> decide) _)
  refine ⟨record.seq bases,?_⟩
  intro w W u S M positive modulus spectator unit atom ht hs blank empty
  obtain ⟨v,D,n,start,user,paid,stock,frame⟩ := init w W u S modulus spectator unit atom blank ht hs
  have keep j := frame (caller j) (fun _ _ => apart _ _)
  have split side i j : recBank i ≠ chart side j := localBank.injective.ne (disjoint side i j)
  obtain ⟨z,F,t,finish,same,charge,both,last⟩ := setup (w+1) W v D ((keep 3).2.trans atom)
    ((keep 1).2.trans spectator) (fun side j => by
      have kept := frame _ (fun i _ => split side i j)
      exact ⟨kept.1.trans (empty side j).1,kept.2.trans (empty side j).2⟩)
    ((keep 4).2.trans ht) ((keep 5).2.trans hs)
  have record (i : Fin (rowSwapBlock.tapes+35)) (ne : i.val ≠ 24) := And.intro
    ((last _ (fun side j => (split side i j).symm)).1.trans (stock i ne).1)
    ((last _ (fun side j => (split side i j).symm)).2.trans (stock i ne).2)
  have kept j outside off := And.intro ((last j off).1.trans (frame j outside).1)
    ((last j off).2.trans (frame j outside).2)
  refine ⟨z,F,n+t,start.seq finish,same.trans user,?_,record,both,?_,kept⟩
  · intro js nd
    apply ((paid.seq charge) js nd).trans
    apply Nat.add_le_add_left
    apply le_trans _ (workerSeedCost w W positive)
    omega
  · intro j privateSlot unused archive
    have expected := layout.beforeArchive w W archive j
    apply And.imp (fun eq => Eq.trans eq expected.1) (fun eq => Eq.trans eq expected.2)
    apply workerSeed_agrees ports basis disjoint separate _ (fun side => basisHeaderStacks (ops side) (w+1) W)
      (embStk localBank F) j
    · intro i eq
      subst j
      exact record i (fun atPayload => privateSlot i atPayload rfl)
    · intro side i eq
      subst j
      exact both side i
    · intro outside off
      have h := kept (localBank j) (fun i _ => localBank.injective.ne (outside i))
        (fun side i => localBank.injective.ne (off side i))
      exact ⟨h.1.trans (unused outside off).1,h.2.trans (unused outside off).2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
