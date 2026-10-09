import IntegerMultBounds.Machine.ActiveTargetHighestLayoutWords

/-! Composing a verified low selected-bit action with the physical highest
bit action supplies every selected bit. The word theorem retains arbitrary
low spectators and every unselected bit of the retained high interval. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestLayoutCompose
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes (Parameters Address)
open ActiveTargetHighestPairLayoutGeometry (sourceHigh)
open ActiveTargetHighestLayoutGlobal
open ActiveTargetHighestLayoutWords
open ActivePrefixDirtyControlConjugationData (FullArray)
open ActivePrefixDirtyControlGlobalSwap (index)
open BinaryAddressTableData (row row_length)

variable (s : Shape) (p : Parameters s) (offset rows : ℕ)

def targetWord (lo : List Bool) (x : Address s p rows) :=
  lo++row (p.n*p.q) x.target.val++row p.before x.activeBefore.val

theorem early_entry (hfit : offset+p.f*p.q≤p.before) (hsource : 0<sourceHigh s p offset)
    (hH : 1≤s.H) (hr : 0<rows) (hp : 0<s.payload)
    (array low : FullArray s rows) (f : Address s p rows → Address s p rows)
    (hlow : ∀ x,low (index s p (f x))=array (index s p x)) (x : Address s p rows) :
    earlyAction s p offset rows hfit hsource hH hr hp low
      (index s p (ActiveTargetHighestLayoutEarlyCoordinates.destination s p offset rows hfit hsource (f x)))=
      array (index s p x) :=
  (ActiveTargetHighestLayoutGlobal.early_entry s p offset rows hfit hsource hH hr hp low (f x)).trans (hlow x)

theorem late_entry (hfit : offset+p.f*p.q≤p.after) (hbefore : 1≤p.before)
    (hH : 1≤s.H) (hr : 0<rows) (hp : 0<s.payload)
    (array low : FullArray s rows) (f : Address s p rows → Address s p rows)
    (hlow : ∀ x,low (index s p (f x))=array (index s p x)) (x : Address s p rows) :
    lateAction s p offset rows hfit hbefore hH hr hp low
      (index s p (ActiveTargetHighestLayoutLateCoordinates.destination s p offset rows hfit hbefore (f x)))=
      array (index s p x) :=
  (ActiveTargetHighestLayoutGlobal.late_entry s p offset rows hfit hbefore hH hr hp low (f x)).trans (hlow x)

theorem early_after_low_word (hfit : offset+p.f*p.q≤p.before) (hsource : 0<sourceHigh s p offset)
    (x y : Address s p rows) (lo Z : List Bool) (hZ : Z.length=p.n)
    (hbefore : y.activeBefore=x.activeBefore)
    (htarget : row (p.n*p.q) y.target.val=CountedIdealToggle.word p.q (row (p.n*p.q) x.target.val) Z) :
    targetWord s p rows lo (ActiveTargetHighestLayoutEarlyCoordinates.destination s p offset rows hfit hsource y)=
      List.zipWith xor (targetWord s p rows lo x)
        (List.replicate lo.length false++Compact.PowerTwo.toggleMask p.q Z++
          (earlyControl s p offset rows x::List.replicate (p.before-1) false)) := by
  change lo++row (p.n*p.q) y.target.val++
    row p.before (ActiveTargetHighestLayoutEarlyCoordinates.destination s p offset rows hfit hsource y).activeBefore.val=_
  rw [htarget,early_word]
  simp only [earlyControl,hbefore]
  have h := early_full_word s p offset rows hfit hsource x lo Z hZ
  rw [early_word] at h
  exact h

theorem late_after_low_word (hfit : offset+p.f*p.q≤p.after) (hbefore : 1≤p.before)
    (x y : Address s p rows) (lo Z : List Bool) (hZ : Z.length=p.n)
    (hbeforeWord : y.activeBefore=x.activeBefore) (hafterWord : y.activeAfter=x.activeAfter)
    (htarget : row (p.n*p.q) y.target.val=CountedIdealToggle.word p.q (row (p.n*p.q) x.target.val) Z) :
    targetWord s p rows lo (ActiveTargetHighestLayoutLateCoordinates.destination s p offset rows hfit hbefore y)=
      List.zipWith xor (targetWord s p rows lo x)
        (List.replicate lo.length false++Compact.PowerTwo.toggleMask p.q Z++
          (lateControl s p offset rows x::List.replicate (p.before-1) false)) := by
  change lo++row (p.n*p.q) y.target.val++
    row p.before (ActiveTargetHighestLayoutLateCoordinates.destination s p offset rows hfit hbefore y).activeBefore.val=_
  rw [htarget,late_word]
  simp only [lateControl,hbeforeWord,hafterWord]
  have h := late_full_word s p offset rows hfit hbefore x lo Z hZ
  rw [late_word] at h
  exact h

end
end IntegerMultBounds.Machine.ActiveTargetHighestLayoutCompose
