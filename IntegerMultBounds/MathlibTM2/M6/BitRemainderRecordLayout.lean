module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodChildLayout
public import IntegerMultBounds.Machine.Shared50RecursiveNodeRows

/-! Physical descriptor for the weighted child inside a classified PR589 record. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open IntegerMultBounds.MathlibTM2.Cover.Fallback

/-- The ordinary adapters leave a rank prefix on the head and a rank suffix
on the tail. Both inactive parts sit between these active fields. -/
noncomputable def remainderRecordChild (lo hi a W : ℕ) : Descriptor :=
  ⟨1,1,1,(hi-lo)*a,(prime^a)^(2*(64-(hi-lo))),W⟩

theorem remainderRecordChild_volume (lo hi a W : ℕ) (fits : hi ≤ 64) :
    volume prime (remainderRecordChild lo hi a W) = (prime^a)^64*((prime^a)^64*W) := by
  have fields : hi-lo+(2*(64-(hi-lo))+(hi-lo)) = 64+64 := by omega
  simp only [volume,remainderRecordChild,one_mul]
  rw [show prime^((hi-lo)*a) = (prime^a)^(hi-lo) by rw [← pow_mul,Nat.mul_comm]]
  simp only [← Nat.mul_assoc,← pow_add]
  congr 2; omega

/-- The scanner's rank-field postcondition is precisely the child read needed
between the two ordinary-record adapters. -/
theorem remainderRecordChild_read {lo hi a W : ℕ} [NeZero (prime^a)] :
    let M := prime^a
    let r := hi-lo
    let g := 64-r
    let v := remainderRecordChild lo hi a W
    let logical := {v with width := r}
    ∀ (before after : ℕ → ZMod 2) (move : IntegerMultBounds.Swap.Shear.State (Fin r) (ZMod M) →
        IntegerMultBounds.Swap.Shear.State (Fin r) (ZMod M)),
      (∀ mid < v.between, ∀ j < W, ∀ s,
        let addr := fun (u : IntegerMultBounds.Swap.Shear.State (Fin r) (ZMod M)) =>
          RecursiveInterchangeLayout.index M logical 0 0 0 (FlatCoordinateLayout.rank u.1).val
            mid (FlatCoordinateLayout.rank u.2).val j
        after (addr (move s)) = before (addr s)) →
      ∀ (hg tg : Fin g → ZMod M) s (j : Fin W),
        let addr := fun u => let t := childFields hg tg u
                             (FlatCoordinateLayout.index (Fin.append t.1 t.2) j).val
        after (addr (move s)) = before (addr s) := by
  intro M r g v logical before after move reads hg tg s j addr
  have shape : logical = goodChildDescriptor M r g W := by
    simp only [logical,v,remainderRecordChild,goodChildDescriptor,g,r,M,two_mul]
  have fits : (FlatCoordinateLayout.rank (Fin.append hg tg)).val < v.between := by
    simpa only [v,remainderRecordChild,two_mul,g,r,M] using (FlatCoordinateLayout.rank (Fin.append hg tg)).isLt
  have action := reads _ fits _ j.isLt s
  rw [shape] at action
  simpa only [addr,goodChildIndex] using action

end IntegerMultBounds.MathlibTM2.M6.BitNode
