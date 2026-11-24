module

public import IntegerMultBounds.MathlibTM2.M6.BitScheduledMoveSeedHeaders
public import IntegerMultBounds.MathlibTM2.M6.BitSeededSuspendedMove

/-! Run the packed MOVE from the parent role fields, restoring its header scratch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open RecursiveInterchangeLayout
open Shared50ModularControl (prime)

private theorem packedVolume (v : Descriptor) :
    volume prime (packedDescriptor v.width (CopyChildLayout.spectators v)) = volume prime v := by
  simp only [volume,packedDescriptor,CopyChildLayout.spectators]
  ring

theorem CutoffNodeInput.packedCells (c : CutoffNodeInput) : volume prime (packedDescriptor (64*(c.w+1)) (CopyChildLayout.spectators c.node/142080)) = c.cells := by
  have alignment := scheduledPackedDescriptor c.node (c.w+1) c.width (c.rows ▸ dvd_mul_right ..)
  have mass := c.cells_share
  rw [← packedVolume c.node,alignment] at mass
  simp only [volume,packedDescriptor,one_mul,mul_one] at mass ⊢
  nlinarith only [mass]

/-- Erase the temporary header words after MOVE and restore the caller on every
tape except the payload. The initial cleanup charge pays for the erasure. -/
theorem restoreMoveHeaders {P U : Type} {T Q N : ℕ} (table : P → Pr P T Q prime U)
    {headers move : Pr P T Q prime U} {u a b : HS T Q prime U} {S D G : Stacks T prime}
    {n m setup price : ℕ} {payload : Fin T} {y : Fin N → ZMod 2} (cleanup : List (Fin T))
    (nd : cleanup.Nodup) (payloadOff : payload ∉ cleanup)
    (fresh : ∀ j ∈ cleanup, S.L j = [] ∧ S.R j = [])
    (prepare : Exec table headers (mk u S) n (mk a D)) (user : a.user = u.user)
    (paid : CleanupBound S D n setup)
    (frame : ∀ j, j ∉ cleanup → D.L j = S.L j ∧ D.R j = S.R j)
    (run : Exec table move (mk a D) m (mk b G)) (same : b.user = a.user)
    (bill : CleanupBound D G m price) (out : RecordPayload payload (fun _ => blank) 0 y G)
    (kept : ∀ j, j ≠ payload → G.L j = D.L j ∧ G.R j = D.R j) :
    ∃ z F t, Exec table ((headers.seq move).seq (clearWorkTapes cleanup)) (mk u S) t (mk z F) ∧
      z.user = u.user ∧ CleanupBound S F t (setup+price+4*cleanup.length+1) ∧
      RecordPayload payload (fun _ => blank) 0 y F ∧
      ∀ j, j ≠ payload → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨z,zu,erase⟩ := clearWorkTapes_exec table cleanup nd b G
  let F := clearSlots cleanup G
  have clean j (mem : j ∈ cleanup) : F.L j = [] ∧ F.R j = [] := by simp [F,clearSlots,replaceBank,mem]
  have cost := cleanupBound_clearBank cleanup nd (paid.seq bill) (Nat.le_refl (tapeCharge cleanupWeight cleanup G+1))
    (F := F) clean (fun j => by by_cases h : j ∈ cleanup <;> simp [F,clearSlots,replaceBank,h])
  have charge : tapeCharge cleanupWeight cleanup S = 4*cleanup.length := by
    unfold tapeCharge
    rw [List.map_congr_left (g := fun _ => 4) (fun j h => congrArg₂ cleanupWeight (fresh j h).1 (fresh j h).2)]
    simp [List.map_const',Nat.mul_comm]
  rw [charge] at cost
  refine ⟨z,F,_,(prepare.seq run).seq erase,zu.trans (same.trans user),cost,?_,?_⟩
  · intro j
    simpa only [F,clearSlots,replaceBank,ite_eq_right payloadOff] using out j
  · intro j ne
    by_cases mem : j ∈ cleanup
    · simp [F,clearSlots,replaceBank,mem,(fresh j mem).1,(fresh j mem).2]
    · have g := kept j ne
      have d := frame j mem
      simpa [F,clearSlots,replaceBank,mem] using And.intro (g.1.trans d.1) (g.2.trans d.2)

theorem scheduledSeededRows {P R U : Type} {T H Q scratchCount : ℕ}
    {reserve : (Fin 2 → List (Fin (prime+4))) → (Fin 2 → List (Fin (prime+4))) → ℕ}
    (body : P → Pr P T Q prime U) (entry : P) (src dst : Fin (142081+2) ↪ Fin T)
    (ret : Fin 3 ↪ Fin T) (tmp buf : Fin T) (place : Fin T ↪ Fin H) (host : R → Pr R H Q prime U)
    (payload count saved aux : Fin H) (seed : CutoffNodeInput → Stacks T prime)
    (r : Fin 38 ↪ Fin H) (fields : Fin 6 → Fin H) (cut temp : Fin H) (counter : Fin 9 ↪ Fin H)
    (apart : [payload,temp,counter 0].Nodup)
    (fieldOff : ∀ i j, fields i ≠ r j) (cutOff : ∀ j, cut ≠ r j) (rowOff : ∀ j, counter 2 ≠ r j)
    (inheritedOff : ∀ i, fields i ≠ counter 2) (cutRow : cut ≠ counter 2)
    (i : Fin nodeChildren5.length)
    (rows : SeededSuspendedRowsWithReserve body entry src dst ret tmp buf place host payload count saved aux
      nodeSeedWords CutoffNodeInput.cells seed (moveSeedHeaders r fields cut) scratchCount reserve) :
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
      (∀ j, S.R (counter j) = []) → (S.R (r 0)).length = p.w →
      S.R (r 1) = binSyms (prime^(p.w+1)).size (prime^(p.w+1)) →
      S.R (r 2) = (Routines.hdr p.node 4).map bitSymbol →
      (∀ j : Fin 38, 3 ≤ j.val → S.R (r j) = []) →
      (∀ j, j ≠ 3 → j ≠ 4 → S.R (fields j) = (Routines.hdr (role p.node 142080) j).map bitSymbol) →
      S.R cut = binSyms c.root.width.size c.cutoff →
      (∀ j ∈ cleanup, S.L j = [] ∧ S.R j = []) →
      S.R count = [] → S.R saved = [] → S.L aux = [] → S.R aux = [] →
      ∃ z F t, Exec table code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (price+(1000512056*p.cells)+(nodeHeaderSetupRate+25+rate)*c.cells+
          4*(scratchCount+slots.length)+112+(prime+8)*(slots.map (fun j => (S.L j).length+(S.R j).length+2)).sum) ∧
        RecordPayload payload (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (v := wide) (one_dvd wide.rows) x) F ∧
        ∀ j, j ≠ payload → F.L j = S.L j ∧ F.R j = S.R j := by
  intro slots cleanup Label payloadOff countOff savedOff auxOff bankOff
  obtain ⟨table,move,rate,labels,call⟩ := rows
  obtain ⟨headers,generate⟩ := scheduledMovePayloadHeaders table r fields cut payload temp counter apart
    fieldOff cutOff rowOff inheritedOff cutRow i
  have nd : cleanup.Nodup := List.nodup_cons.mpr ⟨by
    intro h
    obtain ⟨j,_,eq⟩ := List.mem_map.mp h
    exact rowOff j eq.symm, (by decide : ([3,4,12,13,18,20,29] : List (Fin 38)).Nodup).map r.injective⟩
  refine ⟨table,(headers.seq move).seq (clearWorkTapes cleanup),rate,labels,?_⟩
  intro p c price child handoff tl tr br vacant wide u S x input left right empty clock radix middle free inherited cutoff fresh hc hs al ar
  have size : volume prime wide = p.cells := (packedVolume c.node).trans (child ▸ scheduledChildVolume p i)
  let data := fun j : Fin p.cells => x (j.cast size.symm)
  have word : RecordPayload payload (fun _ => blank) 0 data S := by
    have castList {a b : ℕ} (h : a = b) (f : Fin b → ZMod 2) :
        List.ofFn (fun j : Fin a => f (j.cast h)) = List.ofFn f := by subst b; rfl
    intro j
    simpa only [data,castList] using input j
  obtain ⟨a,D,n,prepare,user,paid,ready,frame⟩ := generate p c child u S data word left right empty clock radix middle free inherited cutoff
  have payloadAt := frame payload payloadOff
  obtain ⟨b,G,m,run,same,bill,out,kept⟩ := call c c.node (c.w+1) price c.width (c.rows ▸ dvd_mul_right ..)
    (c.packedCells ▸ handoff) (by rw [c.packedCells]; exact Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) (Nat.mul_pos c.idlePositive (by decide)))
    tl tr br vacant x a D (fun j => by simpa only [payloadAt.1,payloadAt.2] using input j) ready
    ((frame _ countOff).2.trans hc) ((frame _ savedOff).2.trans hs) ((frame _ auxOff).1.trans al) ((frame _ auxOff).2.trans ar)
  have sameMass : (slots.map (fun j => (D.L j).length+(D.R j).length+2)) =
      slots.map (fun j => (S.L j).length+(S.R j).length+2) := by
    apply List.map_congr_left
    intro j mem
    obtain ⟨k,rfl⟩ := (mem_frameSlots _ _).1 mem
    have eq := frame _ (bankOff k)
    rw [eq.1,eq.2]
  obtain ⟨z,F,t,exec,user,cost,result,restored⟩ := restoreMoveHeaders table cleanup nd payloadOff
    fresh prepare user paid frame run same bill out kept
  refine ⟨z,F,t,exec,user,workerCost.weaken (charged := true) cost ?_,result,restored⟩
  change 512022*p.cells+(nodeHeaderSetupRate+25)*c.cells+28+
    (rate*c.cells+4*scratchCount+1+(price+1000000034*volume prime wide+49)+4*slots.length+1+
    (prime+8)*(slots.map (fun j => (D.L j).length+(D.R j).length+2)).sum)+32+1 ≤ _
  rw [sameMass,size]
  simp only [Nat.add_mul,Nat.mul_add]
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
