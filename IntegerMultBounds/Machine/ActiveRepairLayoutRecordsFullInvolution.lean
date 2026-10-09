import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullEarlySelected
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullLateSelected

/-! The complete selected-mask address actions are involutions. Earlier
source retention uses its explicit disjointness from target-high bit zero. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullInvolution
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes (Parameters Address)
open ActiveTargetHighestPairLayoutGeometry (sourceHigh)
open ActiveTargetHighestLayoutFullSelected
open ActiveTargetHighestLayoutWords
open ActiveTargetHighestLayoutCompose (targetWord)
open ActiveRepairLayoutPermutationFiber (controlWord sourceWord control_length)
open BinaryAddressTableData (row row_length row_rank)

private theorem xor_twice (xs ys : List Bool) (hl : xs.length=ys.length) :
    List.zipWith xor (List.zipWith xor xs ys) ys=xs := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp_all
    | cons y ys =>
      have ht : xs.length=ys.length := by simpa using hl
      cases x <;> cases y <;> simp [ih ys ht]

variable (s : Shape) (p : Parameters s) (offset rows : ℕ)
local notation "Z" => controlWord p.before p.after p.q p.rho p.n offset (p.f*p.q)

def earlyMask (x : Address s p rows) := Compact.PowerTwo.toggleMask p.q (Z .before (x.activeBefore,x.activeAfter))++
  (earlyControl s p offset rows x::List.replicate (p.before-1) false)
def lateMask (x : Address s p rows) := Compact.PowerTwo.toggleMask p.q (Z .after (x.activeBefore,x.activeAfter))++
  (lateControl s p offset rows x::List.replicate (p.before-1) false)

theorem early_mask (hfit : offset+p.f*p.q≤p.before) (hsource : 0<sourceHigh s p offset)
    (hoff : 0<offset) (x : Address s p rows) :
    earlyMask s p offset rows (earlyDestination s p offset rows hfit hsource x)=earlyMask s p offset rows x := by
  have hs := congrArg (fun W => SelectedSourceBitsData.selected W p.q p.rho (p.n+1))
    (early_source s p offset rows hfit hsource hoff x)
  change SelectedSourceBitsData.selected (sourceWord p.before p.after offset (p.f*p.q) .before
      ((earlyDestination s p offset rows hfit hsource x).activeBefore,
       (earlyDestination s p offset rows hfit hsource x).activeAfter)) p.q p.rho (p.n+1)=
    SelectedSourceBitsData.selected (sourceWord p.before p.after offset (p.f*p.q) .before
      (x.activeBefore,x.activeAfter)) p.q p.rho (p.n+1) at hs
  rw [early_selected,early_selected] at hs
  obtain ⟨hz,hc⟩ := List.append_inj hs (by simp)
  have hb := List.cons.inj hc
  simp only [earlyMask,hz,hb.1]

theorem late_mask (hfit : offset+p.f*p.q≤p.after) (hbefore : 1≤p.before) (x : Address s p rows) :
    lateMask s p offset rows (lateDestination s p offset rows hfit hbefore x)=lateMask s p offset rows x := by
  simp only [lateMask,controlWord,sourceWord,lateControl,late_source]

private theorem fields_word_eq {x y : Address s p rows}
    (hf : y={x with target:=y.target,activeBefore:=y.activeBefore})
    (hw : targetWord s p rows [] y=targetWord s p rows [] x) : y=x := by
  change row (p.n*p.q) y.target.val++row p.before y.activeBefore.val=
    row (p.n*p.q) x.target.val++row p.before x.activeBefore.val at hw
  obtain ⟨ht,hb⟩ := List.append_inj hw (by simp)
  have ht' : y.target=x.target := Fin.ext (by
    have hh := congrArg Counter.value ht
    simpa only [row_rank _ _ y.target.isLt,row_rank _ _ x.target.isLt] using hh)
  have hb' : y.activeBefore=x.activeBefore := Fin.ext (by
    have hh := congrArg Counter.value hb
    simpa only [row_rank _ _ y.activeBefore.isLt,row_rank _ _ x.activeBefore.isLt] using hh)
  rw [hf,ht',hb']

theorem early_involutive (hfit : offset+p.f*p.q≤p.before) (hsource : 0<sourceHigh s p offset)
    (hoff : 0<offset) (x : Address s p rows) :
    earlyDestination s p offset rows hfit hsource
      (earlyDestination s p offset rows hfit hsource x)=x := by
  let f := earlyDestination s p offset rows hfit hsource
  apply fields_word_eq s p rows
  · rw [early_fields,early_fields]
  · have h1 := early_target_word s p offset rows hfit hsource x []
    have h2 := early_target_word s p offset rows hfit hsource (f x) []
    change targetWord s p rows [] (f x)=List.zipWith xor (targetWord s p rows [] x) (earlyMask s p offset rows x) at h1
    change targetWord s p rows [] (f (f x))=List.zipWith xor (targetWord s p rows [] (f x)) (earlyMask s p offset rows (f x)) at h2
    rw [early_mask s p offset rows hfit hsource hoff x,h1] at h2
    exact h2.trans (xor_twice _ _ (by
      have hi := ActiveTargetHighestPairLayoutGeometry.source_high_lt s p offset p.before hfit
      simp only [targetWord,earlyMask,List.length_append,List.length_nil,row_length,List.length_cons,List.length_replicate,Compact.PowerTwo.toggleMask_length p.q (positive s p),control_length]
      have : 0<p.before := by omega
      omega))

theorem late_involutive (hfit : offset+p.f*p.q≤p.after) (hbefore : 1≤p.before) (x : Address s p rows) :
    lateDestination s p offset rows hfit hbefore
      (lateDestination s p offset rows hfit hbefore x)=x := by
  let f := lateDestination s p offset rows hfit hbefore
  apply fields_word_eq s p rows
  · rw [late_fields,late_fields]
  · have h1 := late_target_word s p offset rows hfit hbefore x []
    have h2 := late_target_word s p offset rows hfit hbefore (f x) []
    change targetWord s p rows [] (f x)=List.zipWith xor (targetWord s p rows [] x) (lateMask s p offset rows x) at h1
    change targetWord s p rows [] (f (f x))=List.zipWith xor (targetWord s p rows [] (f x)) (lateMask s p offset rows (f x)) at h2
    rw [late_mask s p offset rows hfit hbefore x,h1] at h2
    exact h2.trans (xor_twice _ _ (by
      simp only [targetWord,lateMask,List.length_append,List.length_nil,row_length,List.length_cons,List.length_replicate,Compact.PowerTwo.toggleMask_length p.q (positive s p),control_length]
      omega))

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullInvolution
