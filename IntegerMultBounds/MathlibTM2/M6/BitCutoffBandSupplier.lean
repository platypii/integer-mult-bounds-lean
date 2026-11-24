module

public import IntegerMultBounds.MathlibTM2.M6.BitTerminalParent

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout

private structure BandNode (height : ℕ) where
  input : CutoffNodeInput
  blocks : ℕ
  positive : input.root.Positive
  rows : 142080^(input.depth+1) ∣ input.root.rows
  label : input.root.beforeH = blocks*prime^(64*input.root.width)
  active : input.cutoff < input.node.width
  band : 7*(input.w+1) ≤ input.cutoff
  stop : ∀ path : List (Fin nodeChildren5.length), path.length = height →
    (path.foldl (scheduledChild prime) input.node).width ≤ input.cutoff

private theorem bandRecords (U : Type) (height : ℕ) :
    let _ := BinaryRadixEqualShared.supplierNet
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q → ∃ (T : ℕ) (P : Type) (body : P → Pr P T Q prime U)
      (dst : Fin (142081+2) ↪ Fin T) (rate : ℝ),
      RecordTreeFamily (@BandNode.input height) body dst rate (fun _ _ _ => True) := by
  intro inst
  induction height with
  | zero =>
    obtain ⟨q,build⟩ := terminalPackedTree U
    refine ⟨q,?_⟩
    intro Q fits
    obtain ⟨T,P,body,dst,rate,D,pos,install⟩ := build fits
    refine ⟨T,P,body,dst,rate,D,pos,?_⟩
    intro K live record apart H
    obtain ⟨bank,host,code,placed,frame,_⟩ := install live record apart
    exact ⟨bank,host,code,placed,frame,fun _ _ x => False.elim ((x.stop [] rfl).not_gt x.active)⟩
  | succ h ih =>
    obtain ⟨q,child⟩ := ih
    obtain ⟨pre,post,ts,s,ports,parent⟩ := compiledPackedParent Unit U (BandNode (h+1))
    refine ⟨max q s,?_⟩
    intro Q room
    obtain ⟨N,R,tree,out,childRate,family⟩ := child ((Nat.le_max_left ..).trans room)
    obtain ⟨leafRate,build⟩ := parent ((Nat.le_max_right ..).trans room) family
    obtain ⟨body,active,work,stage,init,fixed,base,swaps,minimum,leaf,assemble,nonneg,pos,run⟩ :=
      build (fun _ _ _ => .act .done) (fun _ _ => ())
    obtain ⟨C,bound⟩ := compiledParentLocal_bound work init fixed base swaps assemble stage
    let D := max minimum C
    obtain ⟨position,coords,execute⟩ := run D (le_max_left ..) BandNode.input BandNode.blocks
      BandNode.positive BandNode.rows BandNode.label (by
        intro x i j p active c node root path cut depth live
        let k := idleDirectoryIndex (i,j)
        have smaller : (scheduledChild prime p.node k).width ≤ p.node.width := by
          change nodeChildren5[k.val]*(p.node.width/64) ≤ _
          rw [p.width,Nat.mul_div_cancel_left _ (by decide : 0 < 64)]
          exact Nat.mul_le_mul_right _ ((nodeChildren5_bounds k).2.trans (by decide : 42 ≤ 64))
        have atoms : c.w+1 ≤ p.w+1 := by
          rw [← node,c.width,p.width] at smaller
          omega
        let y : BandNode h := ⟨c,x.blocks,root ▸ x.positive,by simpa only [root,depth] using x.rows,
          root ▸ x.label,live,by rw [cut]; exact (Nat.mul_le_mul_left 7 atoms).trans x.band,by
            intro tail length
            rw [node,cut]
            exact x.stop (k :: tail) (by simp [length])⟩
        exact ⟨y,rfl,fun _ _ => trivial⟩)
    obtain ⟨physical,charged⟩ := execute leafRate le_rfl (fun x _ _ large => False.elim (x.band.not_gt large))
    obtain ⟨P,T,table,code,src,dst,seed,load,exec⟩ := physical
    have record := splitRecordChildFamily (LoadsPackedSeed.fromNodeRecord load) exec
    refine ⟨T,P,table,dst,max childRate leafRate,recordFamilyOfTreeBound record D _ ?_⟩
    intro x p active
    have bill := charged x active ((bound p).trans
      (mul_le_mul_of_nonneg_right (le_max_right minimum C) (by positivity)))
    simpa only [p.remainingDepth_eq active] using bill.1

/-- The same table can be installed over any family of aligned inputs in the
cutoff band. Both the split and installed record entry use the tree budget. -/
theorem cutoffBandTree (U : Type) :
    let _ := BinaryRadixEqualShared.supplierNet
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q →
    ∃ (N : ℕ) (P : Type) (body : P → Pr P N Q prime U) (dst : Fin (142081+2) ↪ Fin N) (rate : ℝ),
    ∀ {Config : Type} (input : Config → CutoffNodeInput) (blocks : Config → ℕ),
      (∀ x, (input x).root.Positive) → (∀ x, 142080^((input x).depth+1) ∣ (input x).root.rows) →
      (∀ x, (input x).root.beforeH = blocks x*prime^(64*(input x).root.width)) →
      (∀ x, (input x).cutoff < (input x).node.width) → (∀ x, 7*((input x).w+1) ≤ (input x).cutoff) →
      RecordTreeFamily input body dst rate (fun _ _ _ => True) := by
  intro inst
  obtain ⟨q,build⟩ := bandRecords U 6
  refine ⟨q,?_⟩
  intro Q room
  obtain ⟨N,P,body,dst,rate,minimum,nonneg,install⟩ := build room
  refine ⟨N,P,body,dst,rate,?_⟩
  intro Config input blocks positive rows label active band
  refine ⟨minimum,nonneg,?_⟩
  intro T live record apart H
  obtain ⟨bank,host,code,placed,frame,exec⟩ := install live record apart
  refine ⟨bank,host,code,placed,frame,?_⟩
  intro D enough x p running fuel _
  let y : BandNode 6 := ⟨p,blocks x,positive x,rows x,label x,active x,band x,fun path len =>
    Nat.le_of_not_gt (fun live => (len ▸ cutoffBandActiveDepth p (band x) path live).false)⟩
  exact exec D enough y running (fun _ _ => trivial)

/-- One fixed machine serves the entire seven-atom cutoff band. Its installed
record entry executes all reachable active levels, up to a uniform depth of six. -/
theorem cutoffBandSupplier (U : Type) :
    let _ := BinaryRadixEqualShared.supplierNet
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q →
    ∃ (N : ℕ) (P : Type) (body : P → Pr P N Q prime U) (dst : Fin (142081+2) ↪ Fin N)
      (rate minimum : ℝ), 0 ≤ minimum ∧
    ∀ {T : ℕ} (live : Fin (142080+2) ↪ Fin T) (record : Fin 34 ↪ Fin T),
      (∀ i j, 8 ≤ j.val → record j ≠ live i) →
      let H := 142082+T+N
      ∃ (bank : Fin N ↪ Fin H) (host : Empty ⊕ P → Pr (Empty ⊕ P) H Q prime U)
        (code : Pr (Empty ⊕ P) H Q prime U), (∀ f, host (.inr f) = embProg bank Sum.inr (body f)) ∧
        ChildBankFrame live bank ∧ ∀ D, minimum ≤ D → ∀ (p : CutoffNodeInput) blocks,
        p.root.Positive → 142080^(p.depth+1) ∣ p.root.rows →
        p.root.beforeH = blocks*prime^(64*p.root.width) → p.cutoff < p.node.width →
        7*(p.w+1) ≤ p.cutoff →
        InstalledRecordChildExec p live record dst bank host code
          (cutoffBandBudget D rate p.cutoff (min (p.depth-p.path.length) 6) p.node) := by
  intro inst
  obtain ⟨states,family⟩ := bandRecords U 6
  refine ⟨states,?_⟩
  intro Q room
  obtain ⟨N,P,body,dst,rate,minimum,nonneg,install⟩ := family room
  refine ⟨N,P,body,dst,rate,minimum,nonneg,?_⟩
  intro T live record apart H
  obtain ⟨bank,host,code,placed,frame,exec⟩ := install live record apart
  refine ⟨bank,host,code,placed,frame,?_⟩
  intro D enough p blocks positive rows label active band
  let x : BandNode 6 := ⟨p,blocks,positive,rows,label,active,band,fun path len =>
    Nat.le_of_not_gt (fun live => (len ▸ cutoffBandActiveDepth p band path live).false)⟩
  rw [← cutoffTreeBudget_band D rate _ p band]
  intro A K place link outer entry
  exact (exec D enough x active (fun _ _ => trivial)).2 place link outer entry

end IntegerMultBounds.MathlibTM2.M6.BitNode
