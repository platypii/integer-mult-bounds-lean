import IntegerMultBounds.Machine.BlankWordReturnAt
import IntegerMultBounds.Machine.WordMoves
import IntegerMultBounds.Machine.TwoTapeAt
import IntegerMultBounds.Machine.WordSegments

/-! Replace a retained stream by an equal-length result stream, physically
clear the result tape, and return both heads to zero. Every copy, erasure,
return and sequential join is charged; all other caller tapes are framed. -/
namespace IntegerMultBounds.Machine.BlankWordOverwriteAt
noncomputable section
open SharedPlacementAlphabet (setTape)
variable {t a : ℕ}

def erase (i : Fin t) := Placement.placed (EraseBack.program (a := a)) (FiniteReturnStackAt.placement i)
def copy (dst src : Fin t) (h : src≠dst) := TwoTapeAt.program (Copy.program (a := a) blank false) src dst h
def program (dst src : Fin t) (h : src≠dst) := seq (seq (copy dst src h) (erase src)) (BlankWordReturnAt.program (a := a) dst)

theorem overlays (xs ys : List (Fin (a+4))) (hl : xs.length=ys.length) :
    putWord (putWord (fun _ => blank) 0 xs) 0 ys=putWord (fun _ => blank) 0 ys := by
  funext z
  by_cases hz : 0≤z ∧ z<ys.length
  · have hn : (z.toNat : ℤ)=z := Int.toNat_of_nonneg hz.1
    have hi : z.toNat<ys.length := by omega
    have h1 := WordSegments.get (putWord (fun _ => (blank : Fin (a+4))) 0 xs) 0 ys z.toNat hi
    have h2 := WordSegments.get (fun _ => (blank : Fin (a+4))) 0 ys z.toNat hi
    simpa only [hn,zero_add] using h1.trans h2.symm
  · rw [putWord_outside _ _ _ _ (by omega),putWord_outside _ _ _ _ (by omega),
      putWord_outside _ _ _ _ (by omega)]

theorem erase_runs (v : Tapes t a) (i : Fin t) (xs : List (Fin (a+4)))
    (hx : ∀ x∈xs,x≠blank) (ht : v.tape i=putWord (fun _ => blank) 0 xs) (hh : v.head i=xs.length) :
    HoareTime (erase i) (fun z => z=v) (fun z => z=setTape v i (fun _ => blank) 0) (xs.length+2) := by
  have hs := EraseBack.erase_hoare (a := a) (fun _ => blank) 0 xs hx rfl (by intros; rfl)
  simp only [zero_add] at hs
  have h := Placement.hoare_at hs (FiniteReturnStackAt.placement i) v
    (by rw [FiniteReturnStackAt.active_bank,ht,hh]; rfl)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  exact FiniteReturnStackAt.replace_bank _ _ _ _

def output (v : Tapes t a) (dst src : Fin t) (ys : List (Fin (a+4))) :=
  setTape (setTape v dst (putWord (fun _ => blank) 0 ys) 0) src (fun _ => blank) 0

theorem runs (v : Tapes t a) (dst src : Fin t) (h : src≠dst)
    (xs ys : List (Fin (a+4))) (hl : xs.length=ys.length) (hy : ∀ y∈ys,y≠blank)
    (hd : v.tape dst=putWord (fun _ => blank) 0 xs ∧ v.head dst=0)
    (hs : v.tape src=putWord (fun _ => blank) 0 ys ∧ v.head src=0) :
    HoareTime (program dst src h) (fun z => z=v) (fun z => z=output v dst src ys) (3*ys.length+6) := by
  have hc := Copy.copy_hoare (a := a) blank false (fun _ => blank) (putWord (fun _ => blank) 0 xs) 0 0 ys hy rfl
  have hret : (Copy.retained false : Fin (a+4) → Fin (a+4))=id := by funext x; rfl
  rw [hret,List.map_id] at hc
  simp only [zero_add,overlays xs ys hl] at hc
  have h0 := TwoTapeAt.runs (Copy.program (a := a) blank false) src dst h v
    _ _ _ _ _ _ _ _ hs hd hc
  let mid := TwoTapeAt.result v src dst (putWord (fun _ => blank) 0 ys) (putWord (fun _ => blank) 0 ys) ys.length ys.length
  have h1 := erase_runs mid src ys hy
    (by simp [mid,TwoTapeAt.result,setTape,h]) (by simp [mid,TwoTapeAt.result,setTape,h])
  have h2 := BlankWordReturnAt.runs (setTape mid src (fun _ => blank) 0) dst ys hy
    (by simp [mid,TwoTapeAt.result,setTape,h.symm])
    (by simp [mid,TwoTapeAt.result,setTape,h.symm])
  refine ((h0.seq h1).seq h2).consequence (fun _ h => h) ?_ ?_
  · intro z hz
    rw [hz]
    apply congrArg₂ Tapes.mk <;> funext i
    all_goals by_cases hd : i=dst
    all_goals by_cases hs : i=src
    all_goals simp [mid,TwoTapeAt.result,setTape,hd,hs,h,h.symm]
  · omega

end
end IntegerMultBounds.Machine.BlankWordOverwriteAt
