import IntegerMultBounds.Machine.CountedPackedRuntimeLine
import IntegerMultBounds.Compact.ToggleValue

/-! The repair-key ideal toggle uses a fixed controls-at gather and XOR rule.
All widths/counts come from original q/b/n descriptors; private shape and
count metadata and mask scratch are physically erased. -/
namespace IntegerMultBounds.Machine.CountedIdealToggle
noncomputable section
variable {a : ℕ}
open Compact.PowerTwo (toggleMask)
open ColumnTransducer

private theorem map_zip (V M : List Bool) :
    (V.zip M).map (fun c => xor c.1 c.2)=List.zipWith xor V M := by
  induction V generalizing M with
  | nil => simp
  | cons v V ih => cases M <;> simp [ih]

def program (a : ℕ) := CountedPackedRuntimeLine.program 2 (fun _ z => z) xorRule a
abbrev bank := @CountedPackedRuntimeLine.input
def word (q : ℕ) (V Z : List Bool) := List.zipWith xor V (toggleMask q Z)

theorem word_length (q : ℕ) (V Z : List Bool) (hq : 1≤q) (hV : V.length=Z.length*q) :
    (word q V Z).length=V.length := by
  simp only [word,List.length_zipWith,Compact.PowerTwo.toggleMask_length q hq,hV,min_self]

theorem runs (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (W Z V : List Bool)
    (f g h : ℤ → Fin (a+4)) (pW pZ pO pV pT : ℤ) (hs : Fin 3 → List Bool)
    (hW : W.length=Z.length*b) (hV : V.length=Z.length*q)
    (hv : ∀ i, Counter.value (hs i)=CountedPackedShapeHeaders.originalValues q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hf : f (pW-1)=blank) (hg : g (pZ-1)=blank)
    (hh : h (pV-1)=blank) (hh' : h (pV+V.length)=blank) :
    HoareTime (program a)
      (fun z => z=bank (PackedLine.bank (putWord f pW (W.map bitSymbol))
        (putWord g pZ (Z.map bitSymbol)) (fun _ => blank)
        (putWord h pV (V.map bitSymbol)) (fun _ => blank) pW pZ pO pV pT) hs)
      (fun z => z=bank (PackedLine.bank (putWord f pW (W.map bitSymbol))
        (putWord g pZ (Z.map bitSymbol)) (fun _ => blank)
        (putWord h pV (V.map bitSymbol)) (putWord (fun _ => blank) pT ((word q V Z).map bitSymbol))
        pW pZ pO pV pT) hs)
      (533*((Z.length+1)*(q+b+1))) := by
  have hx : Z.length*(CountedPackedShapeHeaders.shape 2 q b hb hbq).sx≤W.length := by
    change Z.length*1≤W.length
    rw [hW]
    nlinarith
  have hm : V.length=Z.length*(CountedPackedShapeHeaders.shape 2 q b hb hbq).st := hV
  have hr := CountedPackedRuntimeLine.runs 2 (fun _ z => z) xorRule q b hb hbq W Z V
    f g h pW pZ pO pV pT hs hv hc hx hm hf hg hh hh'
  have he : ColumnTransducer.digits xorRule 0
      (V.zip (Gather.gather (fun _ z => z) (CountedPackedShapeHeaders.shape 2 q b hb hbq) W Z Z.length)) =
      word q V Z := by
    change ColumnTransducer.digits xorRule 0 (V.zip (Gather.gather (fun _ z => z)
      (PackedArith.controlsAt q b hb hbq) W Z Z.length))=_
    rw [Compact.PowerTwo.gather_controls,xorRule_digits]
    exact map_zip V (toggleMask q Z)
  rw [he] at hr
  refine hr.consequence (fun _ h => h) (fun _ h => h) ?_
  rw [hV]
  nlinarith

theorem value (q : ℕ) (hq : 1≤q) (V Z : List Bool) (hV : V.length=Z.length*q) :
    (Counter.value (word q V Z) : ℤ)=Compact.Radix.pack ((2 : ℤ)^q)
      (Compact.toggleList (Compact.Radix.digits ((2 : ℤ)^q) Z.length (Counter.value V))
        (Z.map Compact.PowerTwo.ctrl)) :=
  Compact.PowerTwo.toggle_word_value q hq V Z hV
end
end IntegerMultBounds.Machine.CountedIdealToggle
