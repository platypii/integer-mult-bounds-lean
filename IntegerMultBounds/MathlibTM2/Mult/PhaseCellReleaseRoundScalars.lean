module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClearInverseScalars
public import IntegerMultBounds.MathlibTM2.Fast.TableView

/-! Restore a scalar bank while retaining the actual published packet prefix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- The executed erasure restores every encoded scalar input and private scalar
slot. The only final change to the original bank is the published source. -/
theorem releaseRoundScalars_exec (rg : TblR 25 → Fin T) (hrg : Function.Injective rg)
    (W : ℕ) (wl : List (Fin (A+4))) (hwl : wl.length = W)
    (initial st : TblSt 25 A) (hfit : ∀ i, st.val i < 2^W)
    (hkeep : ∀ i : Fin 25, i.val < 8 → st.val i = initial.val i)
    (hzero : ∀ i : Fin 25, 8 ≤ i.val → initial.val i = 0) (hacc : st.acc = initial.acc)
    (src : Fin T) (hsrc : ∀ r, rg r ≠ src) (ys : List (Fin (A+4)))
    (v : HS T Q A U) (S F : Stacks T A)
    (hS : tblHolds rg S (tblRho W wl [] initial))
    (hF : tblHolds rg F (tblRho W wl [] st))
    (hin : F.inp = S.inp) (hout : F.out = S.out) (hL : F.L = S.L)
    (hframe : ∀ i, (∀ r, rg r ≠ i) → F.R i = Function.update S.R src ys i) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 17*tblC W 0 ∧
      Exec body (tblCompile rg tblClearInverseScalars) (mk v F) n
        (mk v' {S with R := Function.update S.R src ys}) := by
  have hc := tblClearInverseScalars_do (W := W) (e := 0) st initial hkeep hzero hacc
  obtain ⟨z,hz,hrun⟩ := hc.host (body := body) hrg wl [] hwl rfl (Nat.zero_le W) hfit
  subst z
  obtain ⟨v',G,n,hu,hn,he,hh,hg⟩ := hrun v F hF
  have hfinal : G = {S with R := Function.update S.R src ys} := by
    refine Stacks.ext (hg.1.trans hin) (hg.2.1.trans hout) (hg.2.2.1.trans hL) ?_
    funext i
    by_cases hi : ∃ r, rg r = i
    · obtain ⟨r,rfl⟩ := hi
      change G.R (rg r) = Function.update S.R src ys (rg r)
      rw [Function.update_of_ne (hsrc r)]
      exact (hh r).trans (hS r).symm
    · have hoff : ∀ r, rg r ≠ i := by simpa using hi
      exact (hg.2.2.2 i hoff).trans (hframe i hoff)
  exact ⟨v',n,hu,by simpa only [List.length_nil] using hn,he.cast rfl (congrArg (mk v') hfinal)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
