module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! Restoring reads from a packed interval use local offsets and retain ambient
coordinates in their result. The source and borrowed suffix are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem packedSlice_exec {T Q A s : ℕ} {P U : Type} {body : P → Pr P T Q A U}
    {skip count src dst savedSkip saved tmp : Fin T}
    (hreg : [skip,count,src,dst,savedSkip,saved,tmp].Nodup)
    (a L offset n w : ℕ) (F : ZMod s → GaussianInt)
    (hfit : a+L ≤ s) (hpart : offset+n ≤ L)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A w (packedInterval a L F)++tail)
    (hskip : (S.R skip).length = offset*w) (hcount : (S.R count).length = n*w)
    (hsavedSkip : S.R savedSkip = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (copySlice skip count src dst savedSkip saved tmp) (mk v S)
        (6*(offset*w)+10*(n*w)+16)
        (mk v' {S with R := (Function.update S.R dst
          (cstream A w (packedInterval (a+offset) n F)++S.R dst))}) := by
  let xs := packedInterval a L F
  have hpre : (xs.take offset).length = offset := by
    simp only [List.length_take,packedInterval_length F hfit,xs]
    omega
  have hcrop : (xs.drop offset).take n = packedInterval (a+offset) n F :=
    packedInterval_crop F hpart
  have hn : ((xs.drop offset).take n).length = n := by
    rw [hcrop,packedInterval_length F (by omega)]
  obtain ⟨v',hu,he⟩ := copySlice_coeffs_exec (body := body) hreg v S w
    (xs.take offset) ((xs.drop offset).take n) ((xs.drop offset).drop n) tail
    (by simpa only [slice_split] using hsrc)
    (by simpa only [hpre] using hskip) (by simpa only [hn] using hcount) hsavedSkip hsaved htmp
  exact ⟨v',hu,by simpa only [hpre,hn,hcrop,packedInterval_length F (show a+offset+n ≤ s by omega)] using he⟩

theorem packedWord_exec {T Q A s : ℕ} {P U : Type} {body : P → Pr P T Q A U}
    {skip count src dst savedSkip saved tmp : Fin T}
    (hreg : [skip,count,src,dst,savedSkip,saved,tmp].Nodup)
    (a L offset w : ℕ) (F : ZMod s → GaussianInt)
    (hfit : a+L ≤ s) (hpart : offset < L)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A w (packedInterval a L F)++tail)
    (hskip : (S.R skip).length = offset*w) (hcount : (S.R count).length = w)
    (hsavedSkip : S.R savedSkip = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (copySlice skip count src dst savedSkip saved tmp) (mk v S)
        (6*(offset*w)+10*w+16)
        (mk v' {S with R := (Function.update S.R dst
          (csyms A w (F ((a+offset : ℕ) : ZMod s))++S.R dst))}) := by
  obtain ⟨v',hu,he⟩ := packedSlice_exec (body := body) hreg a L offset 1 w F hfit
    (by omega) tail v S hsrc hskip (by simpa using hcount) hsavedSkip hsaved htmp
  exact ⟨v',hu,by simpa only [Nat.one_mul,packedInterval_singleton F (show a+offset < s by omega),
    cstream_cons,cstream_nil,List.append_nil] using he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
