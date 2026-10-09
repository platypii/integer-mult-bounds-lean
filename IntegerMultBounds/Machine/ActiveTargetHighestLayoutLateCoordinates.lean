import IntegerMultBounds.Machine.ActiveTargetHighestBits
import IntegerMultBounds.Machine.ActivePrefixDirtyControlGlobalSwap

/-! On every original address, the highest later-source action changes just
the lowest activeBefore bit, controlled by the highest selected activeAfter
bit. All low target bits, source bits, and spectators are literal frames. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestLayoutLateCoordinates
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes (Parameters Address)
open ActiveTargetHighestPairData hiding Array
open ActiveTargetHighestPairLayoutGeometry (sourceHigh late)
open ActiveTargetHighestBits
open RecursiveInterchangeRows (pack pack_val)

variable (s : Shape) (p : Parameters s) (offset rows : ℕ)
variable (hfit : offset+p.f*p.q≤p.after) (hbefore : 1≤p.before)
variable (hH : 1≤s.H) (hr : 0<rows) (hp : 0<s.payload)
local notation "g" => late s p offset rows hfit hbefore hH hr hp
local notation "hs" => ActiveTargetHighestPairLayoutGeometry.source_high_lt s p offset p.after hfit
local notation "ht" => Nat.lt_of_lt_of_le Nat.zero_lt_one hbefore

def targetParts (x : Address s p rows) := split p.before 0 ht x.activeBefore
def sourceParts (x : Address s p rows) := split p.after (sourceHigh s p offset) hs x.activeAfter

def frontSize := ((((rows*2^(p.n*p.b))*2^(s.H-p.n*p.b))*2^(p.n*p.b))*2^(s.H-p.n*p.b))*2^s.F
def front (x : Address s p rows) : Fin (frontSize s p rows) :=
  pack (pack (pack (pack (pack x.row x.u) x.uTail) x.t) x.tTail) x.frontSlack

theorem prefix_size : frontSize s p rows*2^(p.before-1)=P g := by
  have hw := p.compactFits
  have he : p.n*p.b+(s.H-p.n*p.b)+p.n*p.b+(s.H-p.n*p.b)+s.F+(p.before-1)=
      2*s.H+s.F+p.before-1 := by omega
  simp only [frontSize,P,late]
  calc
    _ = rows*2^(p.n*p.b+(s.H-p.n*p.b)+p.n*p.b+(s.H-p.n*p.b)+s.F+(p.before-1)) := by
      simp only [pow_add]; ring
    _ = _ := by rw [he]

theorem gap_size : 2^(p.n*p.q)*2^(p.after-sourceHigh s p offset-1)=gap g := by
  have hh := hs
  have he : p.n*p.q+(p.after-sourceHigh s p offset-1)=p.after-offset-p.rho-1 := by
    unfold sourceHigh at *; omega
  simp only [gap,late,←pow_add,he]

theorem suffix_size : (2^(sourceHigh s p offset)*2^(s.H+s.B))*s.payload=suffix g := by
  simp only [suffix,late,pow_add]
  ring

def prefixIndex (x : Address s p rows) : Fin (P g) :=
  Fin.cast (prefix_size s p offset rows hfit hbefore hH hr hp) (pack (front s p rows x) (targetParts s p rows hbefore x).1.1)
theorem prefix_val (x : Address s p rows) :
    (prefixIndex s p offset rows hfit hbefore hH hr hp x).val=
      (front s p rows x).val*2^(p.before-1)+(targetParts s p rows hbefore x).1.1.val := by
  change (pack (front s p rows x) (targetParts s p rows hbefore x).1.1).val=_
  rw [pack_val (front s p rows x) (targetParts s p rows hbefore x).1.1]
  rfl
def middle (x : Address s p rows) : Fin (gap g) :=
  Fin.cast (gap_size s p offset rows hfit hbefore hH hr hp) (pack x.target (sourceParts s p offset rows hfit x).1.1)
def tail (x : Address s p rows) : Fin (suffix g) :=
  Fin.cast (suffix_size s p offset rows hfit hbefore hH hr hp)
    (pack (pack (sourceParts s p offset rows hfit x).2 x.back) x.payload)
def index (x : Address s p rows) : Fin (volume g) :=
  RadixRangePadding.index (prefixIndex s p offset rows hfit hbefore hH hr hp x)
    (targetParts s p rows hbefore x).1.2 (middle s p offset rows hfit hbefore hH hr hp x)
    (sourceParts s p offset rows hfit x).1.2 (tail s p offset rows hfit hbefore hH hr hp x)

theorem original_index (x : Address s p rows) :
    Fin.cast (ActiveTargetHighestPairLayoutGeometry.late_volume s p offset rows hfit hbefore hH hr hp)
      (index s p offset rows hfit hbefore hH hr hp x)=ActivePrefixDirtyControlGlobalSwap.index s p x := by
  apply Fin.ext
  change (index s p offset rows hfit hbefore hH hr hp x).val=
    (CompactActiveTargetLayout.index s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits p.activeSize x).val
  rw [CompactActiveTargetLayout.index_val]
  have hb := split_val p.before 0 ht x.activeBefore
  have ha := split_val p.after (sourceHigh s p offset) hs x.activeAfter
  have hz : (split p.before 0 ht x.activeBefore).2.val=0 := by
    have := (split p.before 0 ht x.activeBefore).2.isLt
    simp only [pow_zero] at this
    omega
  simp only [pow_zero,hz,Nat.mul_one,Nat.add_zero] at hb
  have hpow := size p.after (sourceHigh s p offset) hs
  have hbeforepow := size p.before 0 ht
  simp only [pow_zero,Nat.mul_one,Nat.sub_zero] at hbeforepow
  simp only [index,RadixRangePadding.index,pack_val,prefix_val,middle,tail,Fin.val_cast,front,
    targetParts,sourceParts]
  rw [←gap_size s p offset rows hfit hbefore hH hr hp,←suffix_size s p offset rows hfit hbefore hH hr hp]
  rw [←hb,←ha,←hpow,←hbeforepow]
  simp only [Nat.sub_zero]
  ring

def destination (x : Address s p rows) : Address s p rows :=
  { x with activeBefore := toggle p.before 0 ht (sourceParts s p offset rows hfit x).1.2 x.activeBefore }

theorem index_destination (x : Address s p rows) :
    index s p offset rows hfit hbefore hH hr hp (destination s p offset rows hfit hbefore x)=
      RadixRangePadding.index (prefixIndex s p offset rows hfit hbefore hH hr hp x)
        (ActiveTargetHighestLaterValue.xorBit (targetParts s p rows hbefore x).1.2
          (sourceParts s p offset rows hfit x).1.2)
        (middle s p offset rows hfit hbefore hH hr hp x)
        (sourceParts s p offset rows hfit x).1.2 (tail s p offset rows hfit hbefore hH hr hp x) := by
  simp only [index,prefixIndex,middle,tail,front,targetParts,sourceParts,destination,split_toggle]
  rfl

end
end IntegerMultBounds.Machine.ActiveTargetHighestLayoutLateCoordinates
