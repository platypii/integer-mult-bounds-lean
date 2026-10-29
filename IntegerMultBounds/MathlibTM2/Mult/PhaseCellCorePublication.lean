module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.Mult.ChirpCyclicMath
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedSliceExec
public import IntegerMultBounds.NLogN.PhaseCellCoreWindows

/-! # Executed publication of an owned core

The existing counted slice program restores the complete input, counters,
left stacks and scratch. Only the destination prefix changes. The exact
cost explicitly includes traversal of the ambient prefix; a fused caller
must account for or eliminate this traversal, not hide it in halo volume.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {T Q A s : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def ownedCoreWords (width k : ℕ) (Z : ZMod s → GaussianInt) : List GaussianInt :=
  ((chirpLine s Z).drop (coreStart width k)).take (coreLength s width k)

@[simp] theorem ownedCoreWords_length (width k : ℕ) (Z : ZMod s → GaussianInt) :
    (ownedCoreWords width k Z).length = coreLength s width k := by
  simp only [ownedCoreWords,List.length_take,List.length_drop,length_chirpLine]
  exact min_eq_left (min_le_right _ _)

/-- Generated core publication with the exact traversal cost and arbitrary
source and destination suffixes. Control headers are borrowed, not consumed. -/
theorem publishOwnedCore_exec {skip count src dst savedSkip saved tmp : Fin T}
    (hreg : [skip,count,src,dst,savedSkip,saved,tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (wordWidth width k : ℕ)
    (hstart : coreStart width k ≤ s) (Z : ZMod s → GaussianInt)
    (tail : List (Fin (A+4)))
    (hsrc : S.R src = cstream A wordWidth (chirpLine s Z)++tail)
    (hskip : (S.R skip).length = coreStart width k*wordWidth)
    (hcount : (S.R count).length = coreLength s width k*wordWidth)
    (hsavedSkip : S.R savedSkip = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (copySlice skip count src dst savedSkip saved tmp) (mk v S)
        (6*(coreStart width k*wordWidth)+10*(coreLength s width k*wordWidth)+16)
        (mk v' {S with R := (Function.update S.R dst
          (cstream A wordWidth (ownedCoreWords width k Z)++S.R dst))}) := by
  have hpre : ((chirpLine s Z).take (coreStart width k)).length = coreStart width k := by
    simp only [List.length_take,length_chirpLine,min_eq_left hstart]
  obtain ⟨v',hu,he⟩ := copySlice_coeffs_exec (body := body) hreg v S wordWidth
    ((chirpLine s Z).take (coreStart width k)) (ownedCoreWords width k Z)
    (((chirpLine s Z).drop (coreStart width k)).drop (coreLength s width k)) tail
    (by simpa only [ownedCoreWords,slice_split] using hsrc)
    (by simpa only [hpre] using hskip)
    (by simpa only [ownedCoreWords_length] using hcount) hsavedSkip hsaved htmp
  exact ⟨v',hu,by simpa only [hpre,ownedCoreWords_length] using he⟩

/-- The published word retains its ambient coordinate, not a restarted phase. -/
theorem ownedCoreWords_get (width k j : ℕ) (Z : ZMod s → GaussianInt)
    (hj : j < coreLength s width k) :
    (ownedCoreWords width k Z)[j]'(by simpa using hj) = Z ((coreStart width k+j : ℕ) : ZMod s) := by
  simp only [ownedCoreWords,List.getElem_take,List.getElem_drop,chirpLine,
    List.getElem_map,List.getElem_range]

/-- Cropping a packed halo traverses its padding only, not the ambient prefix.
The same restoring slice machine therefore has a cost independent of the
core's position in the line. The packed solver must supply this source tape. -/
theorem publishPackedCore_exec {skip count src dst savedSkip saved tmp : Fin T}
    (hreg : [skip,count,src,dst,savedSkip,saved,tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (wordWidth width k radius : ℕ)
    (hleft : radius ≤ coreStart width k)
    (hright : coreStart width k+coreLength s width k+radius ≤ s)
    (Z : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (hsrc : S.R src = cstream A wordWidth
      (packedInterval (coreStart width k-radius) (coreLength s width k+2*radius) Z)++tail)
    (hskip : (S.R skip).length = radius*wordWidth)
    (hcount : (S.R count).length = coreLength s width k*wordWidth)
    (hsavedSkip : S.R savedSkip = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (copySlice skip count src dst savedSkip saved tmp) (mk v S)
        (6*(radius*wordWidth)+10*(coreLength s width k*wordWidth)+16)
        (mk v' {S with R := (Function.update S.R dst
          (cstream A wordWidth (ownedCoreWords width k Z)++S.R dst))}) := by
  obtain ⟨v',hu,he⟩ := packedSlice_exec (body := body) hreg
    (coreStart width k-radius) (coreLength s width k+2*radius) radius
    (coreLength s width k) wordWidth Z (by omega) (by omega) tail v S
    hsrc hskip hcount hsavedSkip hsaved htmp
  refine ⟨v',hu,?_⟩
  simpa only [Nat.sub_add_cancel hleft,packedInterval,ownedCoreWords] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
