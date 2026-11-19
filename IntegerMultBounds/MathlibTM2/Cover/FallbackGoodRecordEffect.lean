module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodChildLayout
public import IntegerMultBounds.MathlibTM2.Cover.GoodForm

/-! Identify the combined payload action using only the recursive child's
rank-field behavior and the two surrounding adapter effects. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine FlatCoordinateLayout GoodForm Matrix
open M8.Exchange M8.ReversedExchange IntegerMultBounds.Swap.Shear
variable {M r g W : ℕ} [NeZero M] {α : Type*}
local notation "d" => r+g

theorem goodRecord_effect {G : Matrix (Fin d) (Fin d) (ZMod M)} (stage : Stage G r)
    (A : Matrix (Fin d) (Fin r) (ZMod M)) (B : Matrix (Fin r) (Fin d) (ZMod M))
    (factor : G = A*B) (idem : G*G = G) (w inv : Fin d → ZMod M) (inverse : ∀ i, w i * inv i = 1)
    (input before after output : Fin (M^(d+d)*W) → α) :
    let δ := fun i : Fin d => if i.val < r then stage.M i i else 1
    let δ' := fun i : Fin d => if i.val < r then Ring.inverse (stage.M i i) else 1
    let right := rev d * stage.U * rev d
    let undo := rev d * stage.U' * rev d
    let K := kMat (pivotMatrix (revPivots d r)) (right * rev d * (stage.L * diagonal δ)) *
      diagonal (fun i => inv i * δ' i)
    let address := fun (s : State (Fin d) (ZMod M)) (j : Fin W) => index (Fin.append s.1 s.2) j
    (∀ x y j, let h := (diagonal w * stage.L' * diagonal inv).mulVec x
              before (address (h,right.mulVec y + K.mulVec h) j) = input (address (x,y) j)) →
    (∀ (hg tg : Fin g → ZMod M) (s : State (Fin r) (ZMod M)) j,
      let h := fun i : Fin r => w (i.castAdd g) * stage.M (i.castAdd g) (i.castAdd g)
      let h' := fun i : Fin r => inv (i.castAdd g) * Ring.inverse (stage.M (i.castAdd g) (i.castAdd g))
      after (address (childFields hg tg (Weighted.child r h h' s)) j) = before (address (childFields hg tg s) j)) →
    (∀ x y j, output (address ((diagonal w * stage.L * diagonal inv).mulVec x,
        undo.mulVec (y + (-K).mulVec x)) j) = after (address (x,y) j)) →
    ∀ s j, output (address (transform (diagonal w) 1 (revExchangeOf (rev d) G
      (transform (diagonal inv) 1 s))) j) = input (address s j) := by
  intro δ δ' right undo K address incoming childRun outgoing s j
  let u := cross K (transform (diagonal w * stage.L' * diagonal inv) right s)
  let v := Weighted.child r (fun i => w i * δ i) (fun i => inv i * δ' i) u
  have middle : after (address v j) = before (address u j) :=
    goodChild_effect (fun i => w i * δ i) (fun i => inv i * δ' i) before after
      (fun hg tg x k => by simpa only [δ,δ',Fin.val_castAdd,Fin.isLt,ite_true] using childRun hg tg x k)
      u.1 u.2 j
  rw [← stage.goodMove (Nat.le_add_right r g) A B factor idem w inv inverse s]
  exact (outgoing v.1 v.2 j).trans (middle.trans (incoming s.1 s.2 j))

end IntegerMultBounds.MathlibTM2.Cover.Fallback
