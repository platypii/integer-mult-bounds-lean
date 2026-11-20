module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackLeafPairSwap
public import IntegerMultBounds.MathlibTM2.Cover.FallbackWeightedLeafRun

/-! Execute a coordinate leaf between the descriptor change and its return. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open M8.RevMachine RecursiveInterchangeLayout

/-- A leaf may change its role tapes subject to its payload specification.
Returning restores the parent descriptor and decrements the coordinate counter. -/
theorem coordinateCall_exec {T n work Q cost : ℕ} {F U : Type} (roles : Tapes T prime)
    (v : Descriptor) (positive : v.Positive) (b m : ℕ) (hb : 0 < b) (width : v.width = n*b)
    (i : Fin n) (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (st : Tapes 2 prime) (free : Family.NodeFree node) (effect : Tapes T prime → Prop) :
    let common := CommonBank.count T
    let entry : Graph.Block common prime := Blocks.seqB LeafRoutines.offsets (Blocks.seqB Blocks.push LeafRoutines.view)
    let leave : Graph.Block common prime := Blocks.seqB Blocks.restore LeafRoutines.advance
    let parent := fun roles' count => CommonBank.bank roles' (Routines.hdr v) f p node scalar (Family.leafC b m n count) st
    let c := Family.leafC b m n (i.val+1)
    let live := Function.update (Function.update (Function.update c 12 (some i.val)) 13 (some 1)) 14 (some (n-i.val-1))
    let view := {(RecursiveInterchangeLayout.child (prime^b) 1 1 v i i.rev) with width := b}
    let inside := fun roles' => CommonBank.bank roles' (Routines.hdr view) f p
      (RecursiveViewFrame.savedStack (Routines.hdr v) node) scalar live st
    ∀ (ef : entry.tapes ≤ common+work) (xf : leave.tapes ≤ common+work)
      (eqs : entry.states ≤ Q) (xqs : leave.states ≤ Q)
      (body : F → Pr F ((common+55)+work) Q prime U) (leaf : Pr F _ Q prime U)
      (u : HS _ Q prime U) (S : Stacks _ prime),
    let rep := fun bank (D : Stacks ((common+55)+work) prime) => RepT bank
      (fun i : Fin common => D.L ((i.castAdd 55).castAdd work))
      (fun i => D.R ((i.castAdd 55).castAdd work))
    let clean := fun (D : Stacks ((common+55)+work) prime) => ∀ (j : Fin work) x,
      readAt blank (D.L (j.natAdd (common+55))) (D.R (j.natAdd (common+55))) x = blank
    let keep := fun (D E : Stacks ((common+55)+work) prime) => ∀ j : Fin 55,
      D.L ((j.natAdd common).castAdd work) = E.L ((j.natAdd common).castAdd work) ∧
      D.R ((j.natAdd common).castAdd work) = E.R ((j.natAdd common).castAdd work)
    let place := fun (g : Graph.Block common prime) (fits : g.tapes ≤ common+work) (cap : g.states ≤ Q) =>
      statePlacedNormalized (framePorts 55 fits) cap (Nat.zero_lt_of_lt g.program.start.isLt)
        Empty.elim (foreign g.program)
    rep (parent roles (i.val+1)) S → clean S →
    (∀ z D, rep (inside roles) D → clean D → keep D S →
      ∃ roles' y E t, effect roles' ∧ y.user = z.user ∧ t ≤ cost ∧
        Exec body leaf (mk z D) t (mk y E) ∧ rep (inside roles') E ∧ clean E ∧ keep E D) →
    ∃ roles' z D t, effect roles' ∧ z.user = u.user ∧
      t ≤ (1+(1800*volume prime v*(entry.tapes+5)+6))+cost+(1+(200*volume prime v*(leave.tapes+5)+6)) ∧
      Exec body (((place entry ef eqs).seq leaf).seq (place leave xf xqs)) (mk u S) t (mk z D) ∧
      rep (parent roles' i.val) D ∧ clean D ∧ keep D S := by
  intro common entry leave parent c live view inside ef xf eqs xqs body leaf u S rep clean keep place ready blank middle
  have frame := coordinateFrame_runs roles v positive b m hb width i f p node scalar st free
  have en : common ≤ entry.tapes := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have ex : common ≤ leave.tapes := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  obtain ⟨roles',z,D,t,user,bound,run,out,cleanD,keepD⟩ := framedLeaf_exec
    (record := 55) entry leave _ _ (fun r : Subtype effect => inside r.val)
    (fun r => parent r.val i.val) frame.1 (fun r => frame.2 r.val)
    en ex ef xf eqs xqs body leaf u S ready blank (by
      intro z D child freeD keepD
      obtain ⟨r,y,E,t,hr,h⟩ := middle z D child freeD keepD
      exact ⟨⟨r,hr⟩,y,E,t,h⟩)
  exact ⟨roles'.val,z,D,t,roles'.property,user,bound,run,out,cleanD,keepD⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
