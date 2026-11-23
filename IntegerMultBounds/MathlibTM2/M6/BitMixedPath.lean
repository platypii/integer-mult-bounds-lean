module

public import IntegerMultBounds.MathlibTM2.M6.BitMixedIdleCost

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks RecursiveInterchangeLayout
open Shared50ModularControl (prime)
open Certificates.PR589 Stack Host M8.RevMachine

/-- On a stocked root, packed stage suppliers and a one-node time inequality
suffice for all recursive idle handoffs along the scheduled paths. -/
theorem mixedPathHandoff {U : Type} (minimum : ℝ) :
    ∃ (states : ℕ) (rate C : ℝ) (base nt : ℕ), 0 ≤ rate ∧ minimum ≤ rate ∧
    ∀ {Q : ℕ}, states ≤ Q → ∀ (root : Descriptor) (depth cutoff blocks : ℕ),
    root.Positive → 0 < root.width → 64^depth ∣ root.width → 142080^(depth+1) ∣ root.rows →
    root.beforeH = blocks*prime^(64*root.width) → root.width*42^depth ≤ cutoff*64^depth →
    ∀ time : Descriptor → ℕ,
    let visit := fun path => List.foldl (scheduledChild prime) root path
    (∀ path, let node := visit path
      cutoff < node.width → ∀ w groups B, node.width = 64*(w+1) →
      node.rows = 142080*(142080*groups) → node.beforeH = B*prime^(64*((w+1)*64)) →
      let K := node.beforeRows*(142080*groups)*node.between*node.afterD
      let W := node.beforeRows*groups*node.beforeH*node.between*node.afterD
      let m := (prime^(w+1))^128*(W*142080)
      let child := scheduledChild prime node
      let budget := fun j => if cutoff < (child j).width then time (child j) else
        ⌊(rate*((child j).width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime (child j)⌋₊
      let atPos := fun n => if h : n < nodeChildren5.length then budget ⟨n,h⟩ else 0
      (∀ j, cutoff < (child j).width → (child j).width < node.width →
        PackedDescriptorHandoff U Q (child j) (time (child j))) →
      ∃ (P : Fin 9 → Type) (t : Fin 9 → StageRun → ℕ) (body : ∀ i j, P i → Pr (P i) (t i j) Q prime U)
        (coeff : Fin 9 → StageRun → ℝ) (required : Fin 9 → (ℕ → ℕ) → Prop),
      (∀ i, PackedStageExecution (w := w+1) (B := B) (K := K) i (t i) (body i) (coeff i) (required i)) ∧
      (∀ i, required i atPos) ∧
      let overhead := fun i => ⌊(stageSetupCost base nt m (w+1) : ℝ)+
        (C+|stagePackingRate i+(stageRuns.map (coeff i)).sum|)*m*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau⌋₊+
        142081*(8*m+10)+1
      let idle := ∑ i, (idleCopies.map (fun k => idleCutoffCharge U i w W cutoff 0 k 0)).sum
      (∑ i, overhead i)+idle+9*(1+142081*(8*m+10)+1)+
        9*(2*(76*17760*m*(142081+7)+6)+1+(142081*(8*m+10)+1))+2+(∑ j, budget j) ≤ time node) →
    ∀ path, cutoff < (visit path).width → PackedDescriptorHandoff U Q (visit path) (time (visit path)) := by
  obtain ⟨states,rate,C,base,nt,pos,enough,step⟩ := mixedPackedNode (U := U) minimum
  refine ⟨states,rate,C,base,nt,pos,enough,?_⟩
  intro Q room root depth cutoff blocks positive width widths rows labels stop time visit stages path active
  generalize eq : (visit path).width = n
  induction n using Nat.strong_induction_on generalizing path with
  | h n ih =>
    obtain ⟨w,groups,B,shape,split,label,hB,hK,live⟩ :=
      activeFlatDimensions root depth cutoff blocks positive width widths rows labels stop path active
    let node := visit path
    let child := scheduledChild prime node
    have children (j) (above : cutoff < (child j).width) (smaller : (child j).width < node.width) :
        PackedDescriptorHandoff U Q (child j) (time (child j)) := by
      have next : visit (path++[j]) = child j := by simp [visit,node,child,List.foldl_append]
      exact next ▸ ih _ (smaller.trans_le eq.le) (path++[j]) (next.symm ▸ above) (congrArg Descriptor.width next)
    obtain ⟨P,t,body,coeff,required,runs,ready,paid⟩ := stages path active w groups B shape split label children
    let W := node.beforeRows*groups*node.beforeH*node.between*node.afterD
    have hW : 0 < W := by
      obtain ⟨a,g,b,c,d⟩ := live
      change 0 < 142080*groups at g
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos a (Nat.pos_of_mul_pos_left g)) b) c) d
    have run := step room node w groups W B cutoff shape split rfl hW label hB hK live
      (fun j => time (scheduledChild prime node j)) P t body coeff required children runs ready
    exact ⟨run.1,handoff_le run.2 paid⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
