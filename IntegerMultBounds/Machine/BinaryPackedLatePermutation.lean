import IntegerMultBounds.Machine.BinaryPackedLateData
import IntegerMultBounds.Machine.ActiveRepairLayoutPermutationFields

/-! The actual fixed-width late word arithmetic realizes the exact permutation
used by the global repair theorem, including exceptional packed addresses. -/
namespace IntegerMultBounds.Machine.BinaryPackedLatePermutation
noncomputable section
open Compact Compact.PowerTwo
open ActiveRepairLayoutPermutationFields

 theorem run_fields {S : Type*} (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (X : List Bool) (hX : X.length=n) (x : BinaryPackedLateData.State q b n S) :
    let hq : 1≤q := by omega
    let e := lateEquiv q b n X hq hX
    let y := BinaryPackedLateData.run q b n hb hbq X hX x
    e (y.2.2.1,(y.1,y.2.1))=lateSperm q b X (e (x.2.2.1,(x.1,x.2.1))) := by
  dsimp only
  have hq : 1≤q := by omega
  let e := lateEquiv q b n X hq hX
  have hp := packedLatePerm_agrees (2*Li q) (Bi b) (by have := Li_pos q; omega)
    (by have := Bi_one b; omega) (controls X) (e (x.2.2.1,(x.1,x.2.1)))
  change ((lateSperm q b X (e (x.2.2.1,(x.1,x.2.1)))).2.1.val,
      (lateSperm q b X (e (x.2.2.1,(x.1,x.2.1)))).2.2.val,
      (lateSperm q b X (e (x.2.2.1,(x.1,x.2.1)))).1.val)=
    packedLate (2*Li q) (Bi b) (controls X) x.1.val x.2.1.val x.2.2.1.val at hp
  have hr : packedLate (2*Li q) (Bi b) (controls X) x.1.val x.2.1.val x.2.2.1.val=
      packedLate ((2 : ℤ)^q) ((2 : ℤ)^b) (controls X) x.1.val x.2.1.val x.2.2.1.val := by
    rw [two_Li q hq]
  have hh := (BinaryPackedLateData.agrees q b n hb hbq X hX x).trans (hp.trans hr).symm
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun z : ℤ × ℤ × ℤ => z.2.2) hh
  · apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hh
    · apply Subtype.ext
      exact congrArg (fun z : ℤ × ℤ × ℤ => z.2.1) hh

end
end IntegerMultBounds.Machine.BinaryPackedLatePermutation
