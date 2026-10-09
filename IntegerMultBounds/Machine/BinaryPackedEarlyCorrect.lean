import IntegerMultBounds.Machine.BinaryPackedEarlyArray
import IntegerMultBounds.Machine.BinaryPackedEarlyAddress

/-! Full serialized-array correctness of the four real offset actions. The
common address equivalence covers every dirty back/unused/active/payload cell;
guarded inputs have exactly the ideal selected toggle and restored temporary. -/
namespace IntegerMultBounds.Machine.BinaryPackedEarlyCorrect
open CompactGadgetReservationShape
open BinaryPackedEarlyLayout
open Compact.Radix (pack)

 theorem packed_entry (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hw : n*b≤s.H)
    (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n)
    (x : Fin (rows*s.recordWidth) → Bool) (a : Address s q b n rows) :
    ∃ (v : BinaryPackedEarlyData.Target q n) (w : BinaryPackedEarlyData.Temp b n),
      ((v.val : ℤ),(w.val : ℤ))=
        Compact.packedEarly ((2 : ℤ)^q) ((2 : ℤ)^b) (Z.map Compact.PowerTwo.ctrl) a.1.val a.2.1.val ∧
      BinaryPackedEarlyArray.run s q b n rows hq hw Z hb hbq x
        (index s q b n rows hq hw (v,w,a.2.2))=x (index s q b n rows hq hw a) := by
  let out := BinaryPackedEarlyData.run q b n Z hb hbq a
  refine ⟨out.1,out.2.1,BinaryPackedEarlyData.agrees q b n Z hb hbq hZ a,?_⟩
  have he : out=(out.1,out.2.1,a.2.2) := by
    apply Prod.ext
    · rfl
    · exact Prod.ext rfl (BinaryPackedEarlyData.spectator q b n Z hb hbq a)
  have h := BinaryPackedEarlyArray.run_entry s q b n rows hq hw Z hb hbq hZ x a
  change BinaryPackedEarlyArray.run s q b n rows hq hw Z hb hbq x (index s q b n rows hq hw out)=_ at h
  rw [he] at h
  exact h

 theorem good_entry (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hw : n*b≤s.H)
    (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n)
    (x : Fin (rows*s.recordWidth) → Bool) (a : Address s q b n rows) (ds : List Compact.DigitState)
    (hcontrols : ds.map Compact.DigitState.z=Z.map Compact.PowerTwo.ctrl)
    (hv : (a.1.val : ℤ)=pack ((2 : ℤ)^q) (ds.map Compact.DigitState.v))
    (ht : (a.2.1.val : ℤ)=pack ((2 : ℤ)^b) (ds.map Compact.DigitState.w))
    (hgood : ∀ d∈ds, d.Good ((2 : ℤ)^b) ((2 : ℤ)^(q-1))) :
    ∃ v : BinaryPackedEarlyData.Target q n,
      (v.val : ℤ)=pack ((2 : ℤ)^q) (ds.map (fun d => Compact.toggle d.v d.z)) ∧
      BinaryPackedEarlyArray.run s q b n rows hq hw Z hb hbq x
        (index s q b n rows hq hw (v,a.2.1,a.2.2))=x (index s q b n rows hq hw a) := by
  let out := BinaryPackedEarlyData.run q b n Z hb hbq a
  have hvalue := congrArg Prod.fst (BinaryPackedEarlyData.good_value q b n Z hb hbq hZ a ds hcontrols hv ht hgood)
  refine ⟨out.1,hvalue,?_⟩
  have he : out=(out.1,a.2.1,a.2.2) := by
    apply Prod.ext
    · rfl
    · exact Prod.ext (BinaryPackedEarlyData.good_temp q b n Z hb hbq hZ a ds hcontrols hv ht hgood)
        (BinaryPackedEarlyData.spectator q b n Z hb hbq a)
  have h := BinaryPackedEarlyArray.run_entry s q b n rows hq hw Z hb hbq hZ x a
  change BinaryPackedEarlyArray.run s q b n rows hq hw Z hb hbq x (index s q b n rows hq hw out)=_ at h
  rw [he] at h
  exact h

/-- The exact packed action assertion ranges over every cell of the common
role word, rather than only a selected clean slice of its reservations. -/
 theorem all_cells (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hw : n*b≤s.H)
    (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n)
    (x : Fin (rows*s.recordWidth) → Bool) (i : Fin (rows*s.recordWidth)) :
    ∃ a : Address s q b n rows, index s q b n rows hq hw a=i ∧
      BinaryPackedEarlyArray.run s q b n rows hq hw Z hb hbq x
        (index s q b n rows hq hw (BinaryPackedEarlyData.run q b n Z hb hbq a))=x i := by
  obtain ⟨a,ha⟩ := (BinaryPackedEarlyAddress.index_bijective s q b n rows hq hw).2 i
  refine ⟨a,ha,?_⟩
  rw [←ha]
  exact BinaryPackedEarlyArray.run_entry s q b n rows hq hw Z hb hbq hZ x a

end IntegerMultBounds.Machine.BinaryPackedEarlyCorrect
