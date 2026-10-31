module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.ChildFrameCallStackBounds

/-! Root-relative bounds for all four retained allocation heads along any live
recursive call path. Sibling calls and elapsed runtime do not enter the bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
open IntegerMultBounds IntegerMultBounds.Machine Networks
  Networks.Shared50ModularControl Routines NodeSplit Family NodeBank RecursiveInterchangeLayout
noncomputable section
variable (N : RevNetwork) {k : ℕ}
  {capacity : Fintype.card (Graph.PC (pcs N).length) ≤ 2^k}

/-- One actual child-frame construction at a call site of the network. -/
def ChildCall (b₀ : ℕ) (σ τ : Frame (pcs N) capacity) : Prop :=
  ∃ (hok : Ok N b₀ σ) (hm : N.width ≤ σ.n) (i : Graph.Site (pcs N))
    (w : N.World ⊕ N.Temp) (r : ℕ), r ≤ N.width ∧ (pcs N)[i] = .call (w,r) ∧
      ∃ data : RecursiveMixedSchedule.Data (tapes N) (roleView N σ.b σ.n σ.v),
        τ = childFrame (N := N) σ hok hm i w r data

def retainedHead (σ : Frame (pcs N) capacity) : Fin 4 → ℤ :=
  ![σ.p,σ.node.head 0,σ.st.head 0,σ.st.head 1]

def retainedPotential (σ : Frame (pcs N) capacity) : ℤ :=
  σ.p+σ.node.head 0+σ.st.head 0+σ.st.head 1+((tapes N+90+k)*volume prime σ.v : ℕ)

theorem ChildCall.potential {b₀ : ℕ} (hroles : 2 ≤ N.roleCount)
    {σ τ : Frame (pcs N) capacity} (h : ChildCall N b₀ σ τ) :
    retainedPotential N τ ≤ retainedPotential N σ := by
  obtain ⟨hok,hm,i,w,r,hr,_,data,rfl⟩ := h
  exact childFrame_retained_potential_le N hroles σ hok hm i w r hr data

theorem ChildCall.head_mono {b₀ : ℕ} {σ τ : Frame (pcs N) capacity}
    (h : ChildCall N b₀ σ τ) : ∀ j, retainedHead N σ j ≤ retainedHead N τ j := by
  obtain ⟨hok,hm,i,w,r,hr,_,data,rfl⟩ := h
  have hp := childFrame_payload_head N σ hok hm i w r data
  have hn : (childFrame (N := N) σ hok hm i w r data).node.head 0 =
      σ.node.head 0+BinaryDescriptorFrames.span RecursiveViewFrame.fields (RecursiveViewFrame.words (hdr σ.v))+
        BinaryDescriptorFrames.span RecursiveViewFrame.fields (RecursiveViewFrame.words (hdr (midView N σ.b σ.n σ.v))) := by
    change (RecursiveViewFrame.savedStack _ (RecursiveViewFrame.savedStack _ σ.node)).head 0 = _
    rw [RecursiveViewFrame.savedStack_head,RecursiveViewFrame.savedStack_head]
  have hd : (childFrame (N := N) σ hok hm i w r data).st.head 0 = σ.st.head 0+
      BinaryDescriptorFrames.span RecursiveChildCallSetup.fields (RecursiveChildCallSetup.words (hdr (roleView N σ.b σ.n σ.v))) :=
    RecursiveChildCallSetup.savedStacks_descriptor_head _ _ _
  have hc : (childFrame (N := N) σ hok hm i w r data).st.head 1 = σ.st.head 1+k :=
    RecursiveChildCallSetup.savedStacks_pc_head _ _ _
  intro j
  fin_cases j <;> simp [retainedHead,hp,hn,hd,hc] <;> omega

theorem liveCall_potential {b₀ : ℕ} (hroles : 2 ≤ N.roleCount)
    {root σ : Frame (pcs N) capacity} (hpath : Relation.ReflTransGen (ChildCall N b₀) root σ) :
    retainedPotential N σ ≤ retainedPotential N root := by
  induction hpath with
  | refl => exact le_rfl
  | tail hpath hcall ih => exact (hcall.potential N hroles).trans ih

theorem liveCall_head_mono {b₀ : ℕ} {root σ : Frame (pcs N) capacity}
    (hpath : Relation.ReflTransGen (ChildCall N b₀) root σ) :
    ∀ j, retainedHead N root j ≤ retainedHead N σ j := by
  induction hpath with
  | refl => exact fun _ => le_rfl
  | tail hpath hcall ih => exact fun j => (ih j).trans (hcall.head_mono N j)

/-- Fixed intervals for all retained allocation heads, ready for the machine
controller's head invariant and the host's stack-span interpretation. -/
theorem liveCall_head_bounds {b₀ : ℕ} (hroles : 2 ≤ N.roleCount)
    {root σ : Frame (pcs N) capacity} (hpath : Relation.ReflTransGen (ChildCall N b₀) root σ) :
    ∀ j, retainedHead N root j ≤ retainedHead N σ j ∧
      retainedHead N σ j ≤ retainedHead N root j+((tapes N+90+k)*volume prime root.v : ℕ) := by
  have h := liveCall_potential N hroles hpath
  have hm := liveCall_head_mono N hpath
  have h0 := hm 0
  have h1 := hm 1
  have h2 := hm 2
  have h3 := hm 3
  have hnonneg : (0 : ℤ) ≤ ((tapes N+90+k)*volume prime σ.v : ℕ) := Int.natCast_nonneg _
  unfold retainedPotential at h
  simp only [retainedHead,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h0 h1 h2 h3
  intro j
  constructor
  · exact hm j
  · fin_cases j <;> simp only [retainedHead,Matrix.cons_val_zero',Matrix.cons_val_succ'] <;> omega

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
