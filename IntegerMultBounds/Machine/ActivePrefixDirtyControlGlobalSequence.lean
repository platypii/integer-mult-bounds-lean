import IntegerMultBounds.Machine.ActivePrefixDirtyControlGlobalConjugation
import IntegerMultBounds.Machine.ActivePrefixDirtyControlSourceSemantics

/-! Full-array forward semantics of the actual prepared later schedule, with
both early blocks reading the current compact U and both source conjugations
using the unchanged actual source coordinate. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlGlobalSequence
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes hiding targetShape
open ActivePrefixDirtyControlLayoutFields (targetShape compactShape)
open ActivePrefixDirtyControlSourceGeometry (sourceShape)
open ActivePrefixDirtyControlConjugationData (FullArray)
open ActivePrefixDirtyControlGlobalSwap (index)
open ActivePrefixDirtyControlGlobalConjugation (tDestination uDestination)
open ActivePrefixDirtyControlGlobalTarget (selectedDestination correctionDestination)

variable (s : Shape) (p : Parameters s) (rows offset : ℕ) (hfit : offset+p.f*p.q≤p.after)
variable (hn : 0<p.n) (hb : 2≤p.b) (hrecord : s.bits+1≤s.payload)
variable (hrows : 0<rows) (hK : 0<s.chunk) (hd : 0<s.axes) (hg : 0<s.guard)
local notation "g" => ActivePrefixDirtyControlSequenceGeometry.geometry s p rows offset hfit hn hb hrecord hrows hK hd hg

def pureOffsets := ActivePrefixDirtyControlLoadData.offsets (m := .pure) (compactShape s p) rows
def negativeOffsets := ActivePrefixDirtyControlLoadData.offsets (m := .negative) (compactShape s p) rows
def sourceOffsets := ActivePrefixDirtyControlLoadData.offsets (m := .pure) (sourceShape s p offset hfit) rows
def unloadOffsets := ActivePrefixDirtyControlNegativePureLoadData.offsets (sourceShape s p offset hfit) rows

def earlyDestination (x : Address s p rows) :=
  tDestination s p (negativeOffsets s p rows) (correctionDestination s p
    (tDestination s p (pureOffsets s p rows) (selectedDestination s p x)))
def destination (x : Address s p rows) :=
  uDestination s p (unloadOffsets s p rows offset hfit)
    (earlyDestination s p rows (uDestination s p (sourceOffsets s p rows offset hfit)
      (earlyDestination s p rows x)))

theorem pure_entry (array : FullArray s rows) (x : Address s p rows) :
    ActivePrefixDirtyControlSequenceData.pure g array
      (index s p (tDestination s p (pureOffsets s p rows) x))=array (index s p x) := by
  apply ActivePrefixDirtyControlGlobalConjugation.t_entry
  exact ActivePrefixDirtyControlLoadData.offsets_length (m := .pure) (compactShape s p) rows

theorem negative_entry (array : FullArray s rows) (x : Address s p rows) :
    ActivePrefixDirtyControlSequenceData.negative g array
      (index s p (tDestination s p (negativeOffsets s p rows) x))=array (index s p x) := by
  apply ActivePrefixDirtyControlGlobalConjugation.t_entry
  exact ActivePrefixDirtyControlLoadData.offsets_length (m := .negative) (compactShape s p) rows

theorem load_entry (array : FullArray s rows) (x : Address s p rows) :
    ActivePrefixDirtyControlSequenceData.load g array
      (index s p (uDestination s p (sourceOffsets s p rows offset hfit) x))=array (index s p x) := by
  apply ActivePrefixDirtyControlGlobalConjugation.u_entry
  exact ActivePrefixDirtyControlLoadData.offsets_length (m := .pure) (sourceShape s p offset hfit) rows

theorem unload_entry (array : FullArray s rows) (x : Address s p rows) :
    ActivePrefixDirtyControlSequenceData.unload g array
      (index s p (uDestination s p (unloadOffsets s p rows offset hfit) x))=array (index s p x) := by
  apply ActivePrefixDirtyControlGlobalConjugation.u_entry
  exact ActivePrefixDirtyControlNegativePureLoadData.offsets_length (sourceShape s p offset hfit) rows

theorem early_entry (array : FullArray s rows) (x : Address s p rows) :
    ActivePrefixDirtyControlSequenceData.early g array (index s p (earlyDestination s p rows x))=
      array (index s p x) := by
  have h₀ := ActivePrefixDirtyControlGlobalTarget.selected_entry s p array x
  have h₁ := pure_entry s p rows offset hfit hn hb hrecord hrows hK hd hg
    (ActivePrefixDirtyControlSequenceData.selected g array) (selectedDestination s p x)
  have h₂ := ActivePrefixDirtyControlGlobalTarget.correction_entry s p
    (ActivePrefixDirtyControlSequenceData.pure g (ActivePrefixDirtyControlSequenceData.selected g array))
    (tDestination s p (pureOffsets s p rows) (selectedDestination s p x))
  have h₃ := negative_entry s p rows offset hfit hn hb hrecord hrows hK hd hg
    (ActivePrefixDirtyControlSequenceData.correction g
      (ActivePrefixDirtyControlSequenceData.pure g (ActivePrefixDirtyControlSequenceData.selected g array)))
    (correctionDestination s p (tDestination s p (pureOffsets s p rows) (selectedDestination s p x)))
  exact h₃.trans (h₂.trans (h₁.trans h₀))

theorem entry (array : FullArray s rows) (x : Address s p rows) :
    ActivePrefixDirtyControlSequenceData.later g array (index s p (destination s p rows offset hfit x))=
      array (index s p x) := by
  have h₀ := early_entry s p rows offset hfit hn hb hrecord hrows hK hd hg array x
  have h₁ := load_entry s p rows offset hfit hn hb hrecord hrows hK hd hg
    (ActivePrefixDirtyControlSequenceData.early g array) (earlyDestination s p rows x)
  have h₂ := early_entry s p rows offset hfit hn hb hrecord hrows hK hd hg
    (ActivePrefixDirtyControlSequenceData.load g (ActivePrefixDirtyControlSequenceData.early g array))
    (uDestination s p (sourceOffsets s p rows offset hfit) (earlyDestination s p rows x))
  have h₃ := unload_entry s p rows offset hfit hn hb hrecord hrows hK hd hg
    (ActivePrefixDirtyControlSequenceData.early g
      (ActivePrefixDirtyControlSequenceData.load g (ActivePrefixDirtyControlSequenceData.early g array)))
    (earlyDestination s p rows (uDestination s p (sourceOffsets s p rows offset hfit) (earlyDestination s p rows x)))
  exact h₃.trans (h₂.trans (h₁.trans h₀))

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlGlobalSequence
