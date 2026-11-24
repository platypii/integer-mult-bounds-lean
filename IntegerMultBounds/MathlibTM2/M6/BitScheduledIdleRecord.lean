module

public import IntegerMultBounds.MathlibTM2.M6.BitCompiledIdleRecord
public import IntegerMultBounds.MathlibTM2.M6.BitCutoffIdleChild

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout IntervalDescriptor

/-- An active occurrence consumes the parent's dispatch seed and returns its
word in parent order. Charge its recursive call at the next path depth. -/
theorem scheduledIdleRecord [M8.Machine.Net] {P U : Type} {N T Q : ℕ}
    {body : P → Pr P N Q prime U} {dst : Fin (142081+2) ↪ Fin N} {leafRate : ℝ}
    {childBudget : {c : CutoffNodeInput // c.cutoff < c.node.width} → ℕ → ℕ}
    (family : SplitRecordTreeFamily Subtype.val body dst leafRate childBudget)
    (swapCap : (@rowSwapBlock BinaryRadixEqualShared.supplierNet).states ≤ Q)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (i : Fin 9) (j : Fin idleCopies.length) (board : Fin 113 ↪ Fin T)
    (splitter : Fin intervalSplitTapes ↪ Fin T) (apart : ∀ r k, splitter r ≠ board k) :
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)
    let embed := caller.trans (intervalExtend T N)
    let raw := ((Fin.castLEEmb (by decide : 72 ≤ 113)).trans board).trans embed
    let fields := (idleRolePorts.trans board).trans embed
    let work := idleCallerWork (((Fin.castAddEmb 35 (n := 78)).trans board).trans embed)
    ∃ minimum : ℝ, 0 ≤ minimum ∧ ∀ D : ℝ, minimum ≤ D →
      ∃ (table : Option (Empty ⊕ P) → Pr (Option (Empty ⊕ P)) (intervalHostSize T N) Q prime U)
        (code : Pr (Option (Empty ⊕ P)) (intervalHostSize T N) Q prime U) (fixed base swaps : ℕ),
      ∀ (p : CutoffNodeInput) blocks, p.root.Positive → 142080^(p.depth+1) ∣ p.root.rows →
      p.root.beforeH = blocks*prime^(64*p.root.width) →
      let index := idleDirectoryIndex (i,j)
      let child := scheduledChild prime p.node index
      let fuel := p.depth-(p.path.length+1)
      p.cutoff < child.width →
      (∀ (x : {c : CutoffNodeInput // c.cutoff < c.node.width}), x.val.root = p.root → x.val.path = p.path++[index] → x.val.cutoff = p.cutoff →
        ∀ k : Fin nodeChildren5.length, let d := scheduledChild prime child k
        p.cutoff < d.width → childBudget x k.val ≤ cutoffTreeBudget D leafRate p.cutoff (fuel-1) d) →
      ∀ (word : Fin p.cells → ZMod 2) u S,
        RecordPayload (raw 24) (fun _ => blank) 0 word S →
        IdleDispatchReady raw p.w p.idleWidth p.root.width.size p.cutoff S →
        (∀ t ∈ work, S.L t = [] ∧ S.R t = []) →
        (∀ k, S.R (fields k) = (Routines.hdr (role p.node 142080) k).map bitSymbol) →
        ∃ z F n changed, Exec table code (mk u S) n (mk z F) ∧ z.user = u.user ∧
          CleanupBound S F n (fixed*p.cells+
            (base+swaps*(@swapVolumeRate BinaryRadixEqualShared.supplierNet p.w))*
              ((prime^(p.w+1))^128*p.idleWidth)+cutoffTreeBudget D leafRate p.cutoff fuel child) ∧
          RecordPayload (raw 24) (fun _ => blank) 0 changed F ∧
          parentIntervalRead i idleCopies[j.val].2 (p.w+1) (p.idleWidth*142080) word changed ∧
          ∀ t, t ≠ raw 24 → F.L t = S.L t ∧ F.R t = S.R t := by
  intro caller embed raw fields work
  obtain ⟨minimum,positive,build⟩ := compiledIdleRecord family swapCap capacity i j board splitter apart
  refine ⟨minimum,positive,?_⟩
  intro D enough
  obtain ⟨table,code,fixed,base,swaps,run⟩ := build D enough
  refine ⟨table,code,fixed,base,swaps,?_⟩
  intro p blocks rootPos rows label index child fuel active children word u S payload ready fresh roles
  obtain ⟨c,node,root,path,cut,remaining,_,_,_,_,cells⟩ := activeIdleCutoffInput p blocks rootPos rows label i j active
  have live : c.cutoff < c.node.width := by simpa only [cut,node] using active
  let x : {c : CutoffNodeInput // c.cutoff < c.node.width} := ⟨c,live⟩
  let e := idleInterval i idleCopies[j.val].2
  let lane := phaseIntervalChild (e.1+1) (e.2+1) (p.w+1) p.idleWidth 64
  let wide := {lane with afterD := lane.afterD*142080}
  have bounds := idleBounds i idleCopies[j.val].2
  have shape : wide = phaseIntervalChild (e.1+1) (e.2+1) (p.w+1) (p.idleWidth*142080) 64 := by
    simp only [wide,lane,phaseIntervalChild,Nat.mul_assoc]
  have size : volume prime wide = p.cells := (congrArg (volume prime) shape).trans
    (intervalChild_volume (Nat.succ_le_succ bounds.1) (Nat.succ_le_succ bounds.2) _ _)
  have grandchildren (k : Fin nodeChildren5.length) := children x root path cut k
  have depth : c.depth-(c.path.length+1) = fuel-1 := by
    rw [← Nat.sub_sub,remaining]
  obtain ⟨z,F,n,exec,user,paid,record,off⟩ := run p x node live (fun k => by
    simpa only [x,cut,node,depth,child,index] using grandchildren k)
    (fun k => word (k.cast size)) u S (recordPayload_castInput size _ _ _ payload)
    (by simpa only [x,root,cut] using ready) fresh roles
  let y := Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) (fun k => word (k.cast size))
  refine ⟨z,F,n,fun k => y (k.cast size.symm),exec,user,?_,recordPayload_castInput size.symm _ _ y record,?_,off⟩
  · have mass : volume prime lane = (prime^(p.w+1))^128*p.idleWidth :=
      intervalChild_volume (Nat.succ_le_succ bounds.1) (Nat.succ_le_succ bounds.2) _ _
    change volume prime lane = c.cells at cells
    simpa only [x,← cells,mass,cut,remaining,node,child,index,fuel] using paid
  · exact parentReadOfPhysicalTranspose i idleCopies[j.val].2 _ _ wide shape size word y rfl

end IntegerMultBounds.MathlibTM2.M6.BitNode
