module

public import IntegerMultBounds.MathlibTM2.M6.BitCompactMoveEntry

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout
open Shared50ModularControl (prime)

/-- In the next range above the stopping band, every active sweep child
satisfies the width test for the compact child machine. -/
theorem sweepChild_compactBand (p : CutoffNodeInput) (bound : 49*(p.w+1) ≤ 64*p.cutoff)
    (n : Fin 9) (run : StageRun) {l r : ℕ} (pre : Fin l → MoveIndex) (post : Fin r → MoveIndex)
    (j : Fin 3) (k : Fin (invocationCounts l r j)) :
    7*(scheduledChild prime p.node (invocationChildren n run pre post j k)).width ≤ 64*p.cutoff := by
  have width := sweepChildWidth_le p n run pre post j k
  omega

/-- Generate a stopping-band child's headers from the scheduled parent, execute
its MOVE and restore the borrowed bank within a linear parent allowance. -/
theorem scheduledCompactBandMove {U : Type} :
    let _ := BinaryRadixEqualShared.supplierNet
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q → ∃ minimum leafRate : ℝ, ∀ D, minimum ≤ D →
      ∃ B : ℕ, ∀ {H : ℕ} (place : Fin B ↪ Fin H) (ports : Fin 4 ↪ Fin H)
        (r : Fin 38 ↪ Fin H) (fields : Fin 6 → Fin H) (cut temp : Fin H) (counter : Fin 9 ↪ Fin H)
        (i : Fin nodeChildren5.length) (frameRate : ℕ),
        (∀ i j, place i ≠ ports j) → [ports 0,temp,counter 0].Nodup →
        (∀ i j, fields i ≠ r j) → (∀ j, cut ≠ r j) → (∀ j, counter 2 ≠ r j) →
        (∀ i, fields i ≠ counter 2) → cut ≠ counter 2 →
        (∀ i j, place i ≠ moveSeedHeaders r fields cut j) →
        let cleanup := counter 2 :: moveSeedOutputs r
        let slots := frameSlots place
        (∀ i, ports i ∉ cleanup) → (∀ j, place j ∉ cleanup) →
        ∃ (P : Type) (table : P → Pr P H Q prime U) (code : Pr P H Q prime U) (rate : ℕ),
        ∀ (p : CutoffNodeInput) (blocks : ℕ), p.root.Positive →
        142080^(p.depth+1) ∣ p.root.rows → p.root.beforeH = blocks*prime^(64*p.root.width) →
        let desc := scheduledChild prime p.node i
        p.cutoff < desc.width → 7*desc.width ≤ 64*p.cutoff →
      let wide := packedDescriptor desc.width (CopyChildLayout.spectators desc)
      ∀ u (S : Stacks H prime) (x : Fin (volume prime wide) → ZMod 2),
      RecordPayload (ports 0) (fun _ => blank) 0 x S → S.L temp = [] → S.R temp = [] →
      (∀ j, S.R (counter j) = []) → (S.R (r 0)).length = p.w →
      S.R (r 1) = binSyms (prime^(p.w+1)).size (prime^(p.w+1)) →
      S.R (r 2) = (Routines.hdr p.node 4).map bitSymbol →
      (∀ j : Fin 38, 3 ≤ j.val → S.R (r j) = []) →
      (∀ j, j ≠ 3 → j ≠ 4 → S.R (fields j) = (Routines.hdr (role p.node 142080) j).map bitSymbol) →
      S.R cut = binSyms p.root.width.size p.cutoff →
      (∀ j ∈ cleanup, S.L j = [] ∧ S.R j = []) →
      S.R (ports 1) = [] → S.R (ports 2) = [] → S.L (ports 3) = [] → S.R (ports 3) = [] →
      (slots.map (fun j => (S.L j).length+(S.R j).length+2)).sum ≤ frameRate*p.cells →
      ∃ z F t, Exec table code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (cutoffTreeBudget D leafRate p.cutoff (p.depth-(p.path.length+1)) desc+rate*p.cells) ∧
        RecordPayload (ports 0) (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (v := wide) (one_dvd wide.rows) x) F ∧
        ∀ j, j ≠ ports 0 → F.L j = S.L j ∧ F.R j = S.R j := by
  intro inst
  obtain ⟨q,build⟩ := compactBandMove (U := U) (Config := ActiveBandRecord)
  refine ⟨q,?_⟩
  intro Q capacity
  obtain ⟨minimum,R,parent⟩ := build capacity
  refine ⟨minimum,R,?_⟩
  intro D enough
  obtain ⟨B,install⟩ := parent D enough ActiveBandRecord.input ActiveBandRecord.blocks
    ActiveBandRecord.band ActiveBandRecord.positive ActiveBandRecord.rows ActiveBandRecord.label ActiveBandRecord.active
  refine ⟨B,?_⟩
  intro H place ports r fields cut temp counter i frameRate external apart fieldOff cutOff rowOff inheritedOff cutRow away
  intro cleanup slots portsOff bankOff
  obtain ⟨P,table,move,rate,call⟩ := install place ports (moveSeedHeaders r fields cut) external away
  obtain ⟨headers,generate⟩ := scheduledMovePayloadHeaders table r fields cut (ports 0) temp counter apart
    fieldOff cutOff rowOff inheritedOff cutRow i
  have nd : cleanup.Nodup := List.nodup_cons.mpr ⟨by
    intro h
    obtain ⟨j,_,eq⟩ := List.mem_map.mp h
    exact rowOff j eq.symm, (by decide : ([3,4,12,13,18,20,29] : List (Fin 38)).Nodup).map r.injective⟩
  let setup := nodeHeaderSetupRate+25+rate
  refine ⟨P,table,(headers.seq move).seq (clearWorkTapes cleanup),1000512056+setup+61+(prime+8)*frameRate,?_⟩
  intro p blocks positive rows label desc active band wide u S x record left right empty clock radix middle free inherited cutoff fresh hc hs al ar stock
  have next : (p.path++[i]).foldl (scheduledChild prime) p.root = desc := by
    simp [desc,CutoffNodeInput.node,List.foldl_append]
  obtain ⟨c,root,path,depth,_,cut⟩ := activeCutoffNodeInput p.root p.depth p.b p.cutoff blocks
    positive p.levels p.base p.rootWidth rows label p.stop _ (next ▸ active)
  have child : c.node = desc := by simpa only [CutoffNodeInput.node,root,path] using next
  have small : 7*(c.w+1) ≤ c.cutoff := by rw [← child,c.width] at band; omega
  let k : ActiveBandRecord := ⟨c,blocks,root ▸ positive,by simpa only [root,depth] using rows,
    root ▸ label,by simpa only [cut,child] using active,small⟩
  have mass : volume prime wide = volume prime c.node := by simp only [wide,child,volume,packedDescriptor,CopyChildLayout.spectators]; ring
  have size := mass.trans ((congrArg (volume prime) child).trans (scheduledChildVolume p i))
  let data := fun j : Fin p.cells => x (j.cast size.symm)
  have word : RecordPayload (ports 0) (fun _ => blank) 0 data S := by
    have castList {a b : ℕ} (h : a = b) (f : Fin b → ZMod 2) :
        List.ofFn (fun j : Fin a => f (j.cast h)) = List.ofFn f := by subst b; rfl
    intro j
    simpa only [data,castList] using record j
  obtain ⟨a,D,n,prepare,user,paid,ready,frame⟩ := generate p c child u S data word left right empty clock radix middle free inherited (by simpa only [root,cut] using cutoff)
  have payloadAt := frame _ (portsOff 0)
  have invoke := call k
  dsimp only [k] at invoke
  rw [child] at invoke
  obtain ⟨b,G,m,run,same,bill,out,kept⟩ := invoke x a D
    (fun j => by simpa only [payloadAt.1,payloadAt.2] using record j) ready
    ((frame _ (portsOff 1)).2.trans hc) ((frame _ (portsOff 2)).2.trans hs)
    ((frame _ (portsOff 3)).1.trans al) ((frame _ (portsOff 3)).2.trans ar)
  have sameMass : (slots.map (fun j => (D.L j).length+(D.R j).length+2)) =
      slots.map (fun j => (S.L j).length+(S.R j).length+2) := by
    apply List.map_congr_left
    intro j mem
    obtain ⟨k,rfl⟩ := (mem_frameSlots _ _).1 mem
    have eq := frame _ (bankOff k)
    rw [eq.1,eq.2]
  obtain ⟨z,F,t,exec,user,cost,result,restored⟩ := restoreMoveHeaders table cleanup nd (portsOff 0)
    fresh prepare user paid frame run same bill out kept
  have share := c.cells_share
  rw [child] at share
  change c.cells*142080 = volume prime (scheduledChild prime p.node i) at share
  rw [scheduledChildVolume] at share
  have childCost := Nat.mul_le_mul_left setup (show c.cells ≤ p.cells by omega)
  have pos : 0 < p.cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
    (Nat.mul_pos p.idlePositive (by decide))
  have save := Nat.mul_le_mul_left (prime+8) stock
  refine ⟨z,F,t,exec,user,workerCost.weaken (charged := true) cost ?_,result,restored⟩
  change 512022*p.cells+(nodeHeaderSetupRate+25)*c.cells+28+
    (cutoffTreeBudget _ _ _ _ _+rate*c.cells+1000000034*volume prime wide+
    (prime+8)*(slots.map (fun j => (D.L j).length+(D.R j).length+2)).sum)+32+1 ≤ _
  rw [sameMass,size]
  simp only [setup,Nat.add_mul,Nat.mul_assoc] at childCost save ⊢
  simp only [cut,depth,path,List.length_append,List.length_cons,List.length_nil,Nat.zero_add] at ⊢
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
