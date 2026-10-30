module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCoreAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireCountedLine

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {T Q A s : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def packedCoreArchiveStep (skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T) : Pr P T Q A U :=
  .seq (copySlice skip count src dst savedSkip saved tmp)
    (retireCountedLine rows width src retireCount trash retireTmp)

def packedCoreArchiveStepCost (padding core halo w : ℕ) : ℕ :=
  6*(padding*w)+10*(core*w)+16+retireCountedLineCost halo w

theorem packedCoreArchiveStep_interval_exec
    (skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T)
    (hreg : [skip,count,src,dst,savedSkip,saved,tmp,rows,width,retireCount,trash,retireTmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (w a L offset length : ℕ)
    (hfit : a+L ≤ s) (hpart : offset+length ≤ L)
    (D : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (hsrc : S.R src = cstream A w
      (packedInterval a L D)++tail)
    (hskip : (S.R skip).length = offset*w)
    (hcount : (S.R count).length = length*w)
    (hrows : (S.R rows).length = L)
    (hwidth : (S.R width).length = w)
    (hclean : ∀ i ∈ [savedSkip,saved,tmp,retireCount,trash,retireTmp], S.R i = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ packedCoreArchiveStepCost offset length L w ∧
      Exec body (packedCoreArchiveStep skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp)
        (mk v S) n (mk v' {S with R := (Function.update (Function.update S.R dst
          (cstream A w (packedInterval (a+offset) length D)++S.R dst)) src tail)}) := by
  have hr := hreg
  regs_ne hr
  have h7 : [skip,count,src,dst,savedSkip,saved,tmp].Nodup := by simp_all [ne_comm]
  have h6 : [rows,width,src,retireCount,trash,retireTmp].Nodup := by simp_all [ne_comm]
  obtain ⟨v₁,hu₁,he₁⟩ := packedSlice_exec (body := body) h7 a L offset length w D hfit hpart
    tail v S hsrc hskip hcount (hclean _ (by simp)) (hclean _ (by simp)) (hclean _ (by simp))
  let M : Stacks T A := {S with R := Function.update S.R dst (cstream A w (packedInterval (a+offset) length D)++S.R dst)}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := retireCountedLine_exec (body := body) rows width src retireCount trash retireTmp
    h6 L w
    (cstream A w (packedInterval a L D)) tail
    (by rw [length_cstream,packedInterval_length D (by omega)]) v₁ M
    (by simpa [M,‹dst ≠ rows›.symm] using hrows) (by simpa [M,‹dst ≠ width›.symm] using hwidth)
    (by simpa [M,‹src ≠ dst›] using hsrc)
    (by simpa [M,‹dst ≠ retireCount›.symm] using hclean retireCount (by simp))
    (by simpa [M,‹dst ≠ trash›.symm] using hclean trash (by simp))
    (by simpa [M,‹dst ≠ retireTmp›.symm] using hclean retireTmp (by simp))
  exact ⟨v₂,_,hu₂.trans hu₁,Nat.add_le_add_left hn₂ _,Exec.seq he₁ he₂⟩


/-- Crop the first halo and retire precisely that halo, exposing the next one.
The controls and all temporary tapes are restored for the next replica. -/
theorem packedCoreArchiveStep_exec
    (skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T)
    (hreg : [skip,count,src,dst,savedSkip,saved,tmp,rows,width,retireCount,trash,retireTmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (w coreWidth k radius : ℕ)
    (hleft : radius ≤ coreStart coreWidth k)
    (hright : coreStart coreWidth k+coreLength s coreWidth k+radius ≤ s)
    (D : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (hsrc : S.R src = cstream A w
      (packedInterval (coreStart coreWidth k-radius) (coreLength s coreWidth k+2*radius) D)++tail)
    (hskip : (S.R skip).length = radius*w)
    (hcount : (S.R count).length = coreLength s coreWidth k*w)
    (hrows : (S.R rows).length = coreLength s coreWidth k+2*radius)
    (hwidth : (S.R width).length = w)
    (hclean : ∀ i ∈ [savedSkip,saved,tmp,retireCount,trash,retireTmp], S.R i = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ packedCoreArchiveStepCost radius (coreLength s coreWidth k) (coreLength s coreWidth k+2*radius) w ∧
      Exec body (packedCoreArchiveStep skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp)
        (mk v S) n (mk v' {S with R := (Function.update (Function.update S.R dst
          (cstream A w (ownedCoreWords coreWidth k D)++S.R dst)) src tail)}) := by
  obtain ⟨v',n,hu,hn,he⟩ := packedCoreArchiveStep_interval_exec
    skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp hreg
    v S w (coreStart coreWidth k-radius) (coreLength s coreWidth k+2*radius)
    radius (coreLength s coreWidth k) (by omega) (by omega) D tail hsrc
    hskip hcount hrows hwidth hclean
  refine ⟨v',n,hu,hn,?_⟩
  simpa only [Nat.sub_add_cancel hleft,packedInterval,ownedCoreWords] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
