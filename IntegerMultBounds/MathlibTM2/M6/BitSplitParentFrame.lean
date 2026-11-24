module

public import IntegerMultBounds.MathlibTM2.M6.BitMoveParentDirectory

/-! Bound the whole saved parent bank at the physical packed split entry. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open M8.RevMachine RecursiveInterchangeLayout
open Shared50ModularControl (prime)

/-- The split produces exact data words and bounded physical control stacks.
The private initial seed bounds the rest of the same physical bank. -/
theorem splitParentFrame {P U Config : Type} {T Q h : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin (intervalSplitTapes+1) ↪ Fin T) (tmp buf : Fin T)
    (tmpOff : ∀ i, bank i ≠ tmp) (bufOff : ∀ i, bank i ≠ buf) (distinct : tmp ≠ buf)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    {headers : Config → Fin h → List (Fin (prime+4))} {cells : Config → ℕ} {seed : Config → Stacks T prime}
    (load : LoadsPackedSeed headers cells seed) :
    let fan := (withHelperPort (intervalOwners 142080)).trans bank
    ∃ code, ∃ rate : ℕ, ∀ c, 0 < cells c → ∀ (x : Fin (cells c*142080) → ZMod 2) u (S : Stacks T prime),
      S.R (bank (Fin.succ 0)) = List.ofFn (fun i => SparseRoleCircuit.encode (x i)) →
      (∀ i, S.L (bank i) = []) → (∀ i, i ≠ Fin.succ 0 → S.R (bank i) = []) →
      S.L tmp = [] → S.R tmp = [] → S.R buf = [] →
      (∀ j, (∀ i, fan i ≠ bank j) → (seed c).L (bank j) = [] ∧ (seed c).R (bank j) = []) →
      (∀ j, (∀ i, bank i ≠ j) → S.L j = (seed c).L j ∧ S.R j = (seed c).R j) →
      ∃ z F n, Exec body code (mk u S) n (mk z F) ∧ z.user = u.user ∧
        n ≤ (149*(intervalSplitTapes+5)+5)*(cells c*142080)+25+
          142081*(12*cells c+19+4*(301*(cells c*142080)+2))+3*(4*(301*(cells c*142080)+2)+4)+1 ∧
        ParentStageWords (fun i => fan (i.castAdd 2)) fan (cells c)
          (Fin.lastCases (fun _ => 0) (fun row i => x (finProdFinEquiv (i,row)))) F ∧
        (∀ j, (∀ i, fan i ≠ j) → F.L j = (seed c).L j ∧ F.R j = (seed c).R j) ∧
        ((List.finRange T).map (fun j => (F.L j).length+(F.R j).length+2)).sum ≤ rate*cells c := by
  intro fan
  let own := Function.Embedding.refl (Fin T)
  obtain ⟨C,stock⟩ := load.parentFrameCost own fan
  obtain ⟨code,run⟩ := exactSplitEntry body bank tmp buf tmpOff bufOff distinct capacity
  refine ⟨code,C+2*T+142081*3+2*(301*142080+4),?_⟩
  intro c pos x u S source left empty tl tr br localSeed outerSeed
  obtain ⟨z,F,n,exec,user,paid,words,free,space,frame⟩ := run pos x u S source left empty tl tr br
  have privateAt j (away : ∀ i, fan i ≠ j) : F.L j = (seed c).L j ∧ F.R j = (seed c).R j := by
    by_cases hit : ∃ k, bank k = j
    · obtain ⟨k,rfl⟩ := hit
      exact ⟨(free k away).1.trans (localSeed k away).1.symm,(free k away).2.trans (localSeed k away).2.symm⟩
    · have off i (e : bank i = j) := hit ⟨i,e⟩
      exact ⟨(frame j off).1.trans (outerSeed j off).1,(frame j off).2.trans (outerSeed j off).2⟩
  refine ⟨z,F,n,exec,user,paid,words,privateAt,?_⟩
  let size := fun j => (F.L j).length+(F.R j).length+2
  have bounds (i : Fin 2) : size (fan (i.natAdd 142081)) ≤ 301*(cells c*142080)+4 := by
    have h := space ((withHelperPort (intervalOwners 142080)) (i.natAdd 142081))
    change (F.L (fan (i.natAdd 142081))).length+(F.R (fan (i.natAdd 142081))).length ≤ _ at h
    dsimp only [size]
    omega
  have total := stock c (cells c) _ F words privateAt
  change ((frameSlots own).map size).sum ≤ C*cells c+2*T+142081*(cells c+2)+
    ∑ i : Fin 2, size (fan (i.natAdd 142081)) at total
  have same : ((frameSlots own).map size).sum = ((List.finRange T).map size).sum := by
    simp [frameSlots,own,List.map_reverse]
    rfl
  rw [same,Fin.sum_univ_two] at total
  have fixed : T ≤ T*cells c := Nat.le_mul_of_pos_right T pos
  have a := bounds 0
  have b := bounds 1
  change ((List.finRange T).map size).sum ≤ _
  simp only [Nat.add_mul,Nat.mul_assoc] at *
  omega

/-- A scheduled MOVE pays linear overhead and preserves its saved-bank allowance. -/
theorem linearParentDirectoryMove {P R U : Type} {T H Q scratchCount : ℕ}
    {reserve : (Fin 2 → List (Fin (prime+4))) → (Fin 2 → List (Fin (prime+4))) → ℕ}
    (body : P → Pr P T Q prime U) (entry : P) (src dst : Fin (142081+2) ↪ Fin T)
    (ret : Fin 3 ↪ Fin T) (tmp buf : Fin T) (place : Fin T ↪ Fin H) (host : R → Pr R H Q prime U)
    (payload count saved aux : Fin H) (seed : CutoffNodeInput → Stacks T prime)
    (master : Fin 12 ↪ Fin H) (scratch : Fin 35 ↪ Fin H) (distinct : ∀ i j, master i ≠ scratch j)
    (fields : Fin 6 ↪ Fin H) (temp : Fin H) (counter : Fin 9 ↪ Fin H)
    (apart : [payload,temp,counter 0].Nodup)
    (payloadMaster : ∀ j, master j ≠ payload) (payloadFields : ∀ j, fields j ≠ payload)
    (i : Fin nodeChildren5.length) (frameRate : ℕ) (outside : ∀ j, place j ≠ payload) :
    let r := moveHeaderBank master scratch distinct
    let cut := master 0
    (∀ i j, fields i ≠ r j) → (∀ j, counter 2 ≠ r j) →
    (∀ i, fields i ≠ counter 2) → cut ≠ counter 2 →
    ( SeededSuspendedRowsWithReserve body entry src dst ret tmp buf place host payload count saved aux
      nodeSeedWords CutoffNodeInput.cells seed (moveSeedHeaders r fields cut) scratchCount reserve) →
    let slots := frameSlots place
    let cleanup := counter 2 :: moveSeedOutputs r
    let Label := (Fin T × Bool) ⊕ R
    payload ∉ cleanup → count ∉ cleanup → saved ∉ cleanup → aux ∉ cleanup →
    (∀ j, place j ∉ cleanup) →
    ∃ (table : Label → Pr Label H Q prime U) (code : Pr Label H Q prime U) (rate : ℕ),
      (∀ f, table (.inr f) = stateMapProg id id Sum.inr (host f)) ∧
      ∀ (p c : CutoffNodeInput) price, c.node = scheduledChild prime p.node i →
      PackedPieceHandoffWithReserve cleanupWeight reserve c.cells (packedChildOutput (c.w+1) c.cells)
        body (body entry) src dst (seed c) price →
      (seed c).L tmp = [] → (seed c).R tmp = [] → (seed c).R buf = [] →
      (∀ j, (seed c).L (ret j) = [] ∧ (seed c).R (ret j) = []) →
      let wide := packedDescriptor c.node.width (CopyChildLayout.spectators c.node)
      ∀ u (S : Stacks H prime) (x : Fin (volume prime wide) → ZMod 2),
      RecordPayload payload (fun _ => blank) 0 x S → S.L temp = [] → S.R temp = [] →
      (∀ j, S.R (counter j) = []) →
      ParentMoveDirectory p master fields S →
      (∀ j, S.R (scratch j) = []) →
      p.root.width.size = c.root.width.size → p.cutoff = c.cutoff →
      (∀ j ∈ cleanup, S.L j = [] ∧ S.R j = []) →
      S.R count = [] → S.R saved = [] → S.L aux = [] → S.R aux = [] →
      (slots.map (fun j => (S.L j).length+(S.R j).length+2)).sum ≤ frameRate*p.cells →
      ∃ z F t, Exec table code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (price+rate*p.cells) ∧
        (slots.map (fun j => (F.L j).length+(F.R j).length+2)).sum ≤ frameRate*p.cells ∧
        RecordPayload payload (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (v := wide) (one_dvd wide.rows) x) F ∧
        ParentMoveDirectory p master fields F ∧
        ∀ j, j ≠ payload → F.L j = S.L j ∧ F.R j = S.R j := by
  intro r cut fieldOff rowOff inheritedOff cutRow rows slots cleanup Label payloadOff countOff savedOff auxOff bankOff
  obtain ⟨table,code,rate,labels,run⟩ := parentDirectoryMove body entry src dst ret tmp buf place host
    payload count saved aux seed master scratch distinct fields temp counter apart payloadMaster payloadFields i
    fieldOff rowOff inheritedOff cutRow rows payloadOff countOff savedOff auxOff bankOff
  let setup := nodeHeaderSetupRate+25+rate
  let fixed := 4*(scratchCount+T)+112
  refine ⟨table,code,1000512056+setup+fixed+(prime+8)*frameRate,labels,?_⟩
  intro p c price child handoff tl tr br returns wide u S x record tempL tempR counters dir scratchR
    width cutoff clean countR savedR auxL auxR stock
  obtain ⟨z,F,t,exec,user,paid,result,dirF,restored⟩ := run p c price child handoff tl tr br returns
    u S x record tempL tempR counters dir scratchR width cutoff clean countR savedR auxL auxR
  have share := c.cells_share
  rw [child,scheduledChildVolume] at share
  have childCost := Nat.mul_le_mul_left setup (show c.cells ≤ p.cells by omega)
  have pos : 0 < p.cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
    (Nat.mul_pos p.idlePositive (by decide))
  have base := Nat.le_mul_of_pos_right fixed pos
  have save := Nat.mul_le_mul_left (prime+8) stock
  have len : slots.length = T := by simp [slots,frameSlots]
  refine ⟨z,F,t,exec,user,workerCost.weaken (charged := true) paid ?_,?_,result,dirF,restored⟩
  · change price+1000512056*p.cells+setup*c.cells+4*(scratchCount+slots.length)+112+
        (prime+8)*_ ≤ _
    rw [len]
    simp only [Nat.add_mul,Nat.mul_assoc]
    dsimp only [fixed] at base ⊢
    dsimp only [slots] at save
    simp only [Nat.add_mul] at save
    omega
  · apply le_trans _ stock
    apply le_of_eq
    congr 1
    apply List.map_congr_left
    intro j hj
    obtain ⟨k,rfl⟩ := (mem_frameSlots place j).mp hj
    simp only [(restored _ (outside k)).1,(restored _ (outside k)).2]

end IntegerMultBounds.MathlibTM2.M6.BitNode
