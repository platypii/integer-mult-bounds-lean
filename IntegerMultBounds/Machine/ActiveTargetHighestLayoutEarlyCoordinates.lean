import IntegerMultBounds.Machine.ActiveTargetHighestLayoutLateCoordinates

/-! Earlier-source highest action in the unchanged activeBefore field.
Only its lowest bit changes; the source and all bits between them remain
literal spectators, as do both dirty reservations and all target low bits. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestLayoutEarlyCoordinates
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes (Parameters Address)
open ActiveTargetHighestPairData hiding Array
open ActiveTargetHighestPairLayoutGeometry (sourceHigh early)
open ActiveTargetHighestBits
open ActiveTargetHighestLayoutLateCoordinates (front frontSize)
open RecursiveInterchangeRows (pack pack_val)

variable (s : Shape) (p : Parameters s) (offset rows : ℕ)
variable (hfit : offset+p.f*p.q≤p.before) (hsource : 0<sourceHigh s p offset)
variable (hH : 1≤s.H) (hr : 0<rows) (hp : 0<s.payload)
local notation "g" => early s p offset rows hfit hsource hH hr hp
local notation "hs" => ActiveTargetHighestPairLayoutGeometry.source_high_lt s p offset p.before hfit

def sourceParts (x : Address s p rows) := split p.before (sourceHigh s p offset) hs x.activeBefore
def targetParts (x : Address s p rows) := split (sourceHigh s p offset) 0 hsource
  (sourceParts s p offset rows hfit x).2

theorem prefix_size : frontSize s p rows*2^(p.before-sourceHigh s p offset-1)=P g := by
  have hw := p.compactFits
  have hh := hs
  have he : p.n*p.b+(s.H-p.n*p.b)+p.n*p.b+(s.H-p.n*p.b)+s.F+(p.before-sourceHigh s p offset-1)=
      2*s.H+s.F+p.before-(sourceHigh s p offset+1) := by omega
  simp only [frontSize,P,early]
  calc
    _ = rows*2^(p.n*p.b+(s.H-p.n*p.b)+p.n*p.b+(s.H-p.n*p.b)+s.F+(p.before-sourceHigh s p offset-1)) := by
      simp only [pow_add]; ring
    _ = _ := by rw [he]

theorem suffix_size : ((2^(p.n*p.q)*2^p.after)*2^(s.H+s.B))*s.payload=suffix g := by
  simp only [suffix,early,pow_add]
  ring

def prefixIndex (x : Address s p rows) : Fin (P g) :=
  Fin.cast (prefix_size s p offset rows hfit hsource hH hr hp) (pack (front s p rows x) (sourceParts s p offset rows hfit x).1.1)
theorem prefix_val (x : Address s p rows) :
    (prefixIndex s p offset rows hfit hsource hH hr hp x).val=
      (front s p rows x).val*2^(p.before-sourceHigh s p offset-1)+(sourceParts s p offset rows hfit x).1.1.val := by
  change (pack (front s p rows x) (sourceParts s p offset rows hfit x).1.1).val=_
  rw [pack_val (front s p rows x) (sourceParts s p offset rows hfit x).1.1]
def middle (x : Address s p rows) : Fin (gap g) := (targetParts s p offset rows hfit hsource x).1.1
def tail (x : Address s p rows) : Fin (suffix g) :=
  Fin.cast (suffix_size s p offset rows hfit hsource hH hr hp) (pack (pack (pack x.target x.activeAfter) x.back) x.payload)
def index (x : Address s p rows) : Fin (volume g) :=
  RadixRangePadding.index (prefixIndex s p offset rows hfit hsource hH hr hp x)
    (sourceParts s p offset rows hfit x).1.2 (middle s p offset rows hfit hsource hH hr hp x)
    (targetParts s p offset rows hfit hsource x).1.2 (tail s p offset rows hfit hsource hH hr hp x)

theorem original_index (x : Address s p rows) :
    Fin.cast (ActiveTargetHighestPairLayoutGeometry.early_volume s p offset rows hfit hsource hH hr hp)
      (index s p offset rows hfit hsource hH hr hp x)=ActivePrefixDirtyControlGlobalSwap.index s p x := by
  apply Fin.ext
  change (index s p offset rows hfit hsource hH hr hp x).val=
    (CompactActiveTargetLayout.index s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits p.activeSize x).val
  rw [CompactActiveTargetLayout.index_val]
  have ht := split_val (sourceHigh s p offset) 0 hsource (sourceParts s p offset rows hfit x).2
  have hz : (split (sourceHigh s p offset) 0 hsource (sourceParts s p offset rows hfit x).2).2.val=0 := by
    have := (split (sourceHigh s p offset) 0 hsource (sourceParts s p offset rows hfit x).2).2.isLt
    simp only [pow_zero] at this
    omega
  simp only [pow_zero,hz,Nat.mul_one,Nat.add_zero] at ht
  have hpow := size p.before (sourceHigh s p offset) hs
  have hsourcepow := size (sourceHigh s p offset) 0 hsource
  simp only [pow_zero,Nat.mul_one,Nat.sub_zero] at hsourcepow
  unfold index
  rw [rectangle_val (prefixIndex s p offset rows hfit hsource hH hr hp x)
    (sourceParts s p offset rows hfit x).1.2 (middle s p offset rows hfit hsource hH hr hp x)
    (targetParts s p offset rows hfit hsource x).1.2 (tail s p offset rows hfit hsource hH hr hp x)]
  simp only [prefix_val,middle,tail,Fin.val_cast,pack_val,front]
  rw [←suffix_size s p offset rows hfit hsource hH hr hp]
  simp only [sourceParts] at ht
  rw [←split_val p.before (sourceHigh s p offset) hs x.activeBefore,←ht]
  simp only [←hpow,←hsourcepow]
  simp only [targetParts,sourceParts,Nat.sub_zero,gap,early]
  ring

def destination (x : Address s p rows) : Address s p rows :=
  { x with
    activeBefore := join p.before (sourceHigh s p offset) hs
      ((sourceParts s p offset rows hfit x).1,
        toggle (sourceHigh s p offset) 0 hsource (sourceParts s p offset rows hfit x).1.2
          (sourceParts s p offset rows hfit x).2) }

theorem source_destination (x : Address s p rows) :
    sourceParts s p offset rows hfit (destination s p offset rows hfit hsource x)=
      ((sourceParts s p offset rows hfit x).1,
        toggle (sourceHigh s p offset) 0 hsource (sourceParts s p offset rows hfit x).1.2
          (sourceParts s p offset rows hfit x).2) := by
  exact split_join _ _ _ _

theorem index_destination (x : Address s p rows) :
    index s p offset rows hfit hsource hH hr hp (destination s p offset rows hfit hsource x)=
      RadixRangePadding.index (prefixIndex s p offset rows hfit hsource hH hr hp x)
        (sourceParts s p offset rows hfit x).1.2 (middle s p offset rows hfit hsource hH hr hp x)
        (ActiveTargetHighestLaterValue.xorBit (targetParts s p offset rows hfit hsource x).1.2
          (sourceParts s p offset rows hfit x).1.2) (tail s p offset rows hfit hsource hH hr hp x) := by
  simp only [index,prefixIndex,middle,tail,front,targetParts,source_destination,split_toggle]
  rfl

end
end IntegerMultBounds.Machine.ActiveTargetHighestLayoutEarlyCoordinates
