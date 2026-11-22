module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleWindow
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryIdleRead

/-! A scheduled recursive call on one flat remainder port. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover
open RecursiveInterchangeLayout
open Shared50ModularControl (prime)

/-- The physical port keeps the active pair and spectator index of the scheduled child. -/
def IdleChildPositions (i : Fin 9) (j : Fin 222) (w W : ℕ) (child : Descriptor)
    (position : Fin (volume prime child) ≃ Fin ((prime^w)^128*W)) : Prop :=
  let e := idleInterval i j
  let size := intervalChild_volume (idleBounds i j).1 ((idleBounds i j).2.trans (by decide : 63 ≤ 64)) w W
  (phaseIntervalChild e.1 e.2 w W 64).width = child.width ∧
    InheritedIntervalPositions child (phaseIntervalChild e.1 e.2 w W 64) size position

/-- Moving both endpoints together preserves the charged rank and gives
the scheduled child its physical active coordinates. -/
theorem idleChildPositions_offset (node : Descriptor) (i : Fin 9) (j : Fin idleCopies.length)
    (w rows offset : ℕ) (fits : (idleInterval i idleCopies[j.val].2).2+offset ≤ 64)
    (hw : 0 < w) (width : node.width = 64*w) (split : node.rows = 142080*rows) :
    let W := node.beforeRows*rows*node.beforeH*node.between*node.afterD
    let V := (prime^w)^128*W
    let child := scheduledChild prime node (idleDirectoryIndex (i,j))
    let e := idleInterval i idleCopies[j.val].2
    let interval := phaseIntervalChild (e.1+offset) (e.2+offset) w W 64
    let size : volume prime interval = V :=
      intervalChild_volume (Nat.add_le_add_right (idleBounds i idleCopies[j.val].2).1 offset) fits w W
    ∃ position : Fin (volume prime child) ≃ Fin V, interval.width = child.width ∧
      child.width < node.width ∧ InheritedIntervalPositions child interval size position := by
  intro W V child e interval size
  have bounds := idleBounds i idleCopies[j.val].2
  have rank := idleDirectoryIndex_rank i j
  have sameWidth : interval.width = child.width := by
    change ((e.2+offset)-(e.1+offset))*w = nodeChildren5.get (idleDirectoryIndex (i,j))*(node.width/64)
    rw [Nat.add_sub_add_right,width,Nat.mul_div_cancel_left _ (by decide : 0 < 64),rank]
  have smaller : child.width < node.width := by
    rw [← sameWidth,width]
    exact Nat.mul_lt_mul_of_pos_right (by dsimp only [interval,phaseIntervalChild,e]; omega) hw
  have measure := (scheduledChild_measures prime node ⟨w,width⟩ ⟨rows,split⟩ (idleDirectoryIndex (i,j))).2
  have parent : V*142080 = volume prime node := by
    dsimp only [V,W,volume]
    rw [width,split,Nat.mul_comm 64 w,pow_mul,show 128 = 64+64 by decide,pow_add]
    ring
  have equal : volume prime child = volume prime interval :=
    (Nat.eq_of_mul_eq_mul_right (by decide : 0 < 142080) (measure.trans parent.symm)).trans size.symm
  let packed := (CopyChildLayout.packActive child).symm.trans ((finCongr equal).trans (CopyChildLayout.packActive interval))
  have card := Fintype.card_congr packed
  simp only [Fintype.card_fin] at card
  let position := (CopyChildLayout.packActive child).trans ((finCongr card).trans
    ((CopyChildLayout.packActive interval).symm.trans (finCongr size)))
  have coords : InheritedIntervalPositions child interval size position := by
    intro k
    simp [position]
  exact ⟨position,sameWidth,smaller,coords⟩

theorem flatIdleCall_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U) (f : P)
    (node : Descriptor) (i : Fin 9) (j : Fin idleCopies.length) (w rows : ℕ)
    (hw : 0 < w) (width : node.width = 64*w) (split : node.rows = 142080*rows) :
    let W := node.beforeRows*rows*node.beforeH*node.between*node.afterD
    let V := (prime^w)^128*W
    let child := scheduledChild prime node (idleDirectoryIndex (i,j))
    ∃ position : Fin (volume prime child) ≃ Fin V, IdleChildPositions i idleCopies[j.val].2 w W child position ∧
      ∀ (stored : (Fin V → ZMod 2) → Stacks T prime → Prop)
        (u : HS T Q prime U) S (word : Fin V → ZMod 2) budget,
      (child.width < node.width → ∃ z F n changed, Exec body (body f) (mk u S) n (mk z F) ∧
        n ≤ budget ∧ z.user = u.user ∧ stored changed F ∧ ∀ k, changed (position k) =
          Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) k) →
      ∃ z F n changed, Exec body (.call f) (mk u S) n (mk z F) ∧ n ≤ budget+2 ∧
        z.user = u.user ∧ stored changed F ∧ intervalChildRead i idleCopies[j.val].2 w W word changed := by
  intro W V child
  have bounds := idleBounds i idleCopies[j.val].2
  let size := intervalChild_volume bounds.1 (bounds.2.trans (by decide : 63 ≤ 64)) w W
  obtain ⟨position,sameWidth,smaller,coords⟩ := idleChildPositions_offset node i j w rows 0
    (bounds.2.trans (by decide)) hw width split
  simp only [Nat.add_zero] at sameWidth coords
  refine ⟨position,⟨sameWidth,coords⟩,?_⟩
  intro stored u S word budget run
  obtain ⟨z,F,n,changed,exec,paid,user,out,read⟩ := run smaller
  refine ⟨z,F,_,changed,Exec.call exec,by omega,user,out,?_⟩
  have result := (coords.transpose_iff sameWidth word changed).1 read
  intro a
  simpa only [Fin.cast_cast,Fin.cast_eq_self] using congrFun result (a.cast size)

end IntegerMultBounds.MathlibTM2.M6.BitNode
