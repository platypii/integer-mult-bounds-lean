module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoundPackedKey
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRoundAccuracy

/-! The existing list rounding program normalizes cyclic output without a new executor. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem roundCyclicInterval_exec (hA : 4 ≤ A)
    (rg : TblR 8 → Fin T) (hrg : Function.Injective rg)
    (ports : Fin 4 → Fin T) (hports : Function.Injective ports)
    (hsep : ∀ i r, rg r ≠ ports i)
    {rows width count src work saved tmp sp sg cy : Fin T}
    (hreg : [rows,width,count,src,work,saved,tmp,ports 0,ports 1,ports 2,ports 3,sp,sg,cy].Nodup)
    (hscalar : ∀ r, rg r ∉ [count,src,work,saved])
    (B w q p j E : ℕ) (wl : List (Fin (A+4))) (hwl : wl.length = B)
    (st : TblSt 8 A) (hval : st.val = ![w,q,p,j,E,0,0,0])
    (hp : p ≤ q) (hw : 1 ≤ w) (hsize : q-p+j+(p+E+5) ≤ w)
    (hroom : w < 2^B) (hfit : ∀ i, st.val i < 2^B)
    {s : ℕ} [NeZero s] (a n : ℕ) (ha : a < s)
    (D : ZMod s → GaussianInt) (z : ZMod s → ℂ) (e : ℝ) (he : e ≤ 1)
    (hz : ∀ i ∈ cyclicPrincipalVertices s a n, ‖z i‖ ≤ 4*(2 : ℝ)^E)
    (oldTail tail : List (Fin (A+4)))
    (hgood : PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
      (cyclicIntervalRead q w a (cstream A w (cyclicInterval a n D)++oldTail)) z e)
    (v : HS T Q A U) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho B wl [] st))
    (hrows : (S.R rows).length = n) (hwidth : (S.R width).length = w)
    (hsrc : S.R src = cstream A w (cyclicInterval a n D)++tail)
    (hblank : ∀ r ∈ [count,work,saved,tmp,sp,sg,cy], S.R r = [])
    (hheaders : ∀ i, S.R (ports i) = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ roundPackedKeyCost B w (p+E+5) n w n ∧
      Exec body (roundPackedKey rg ports rows width count src work saved tmp sp sg cy) (mk v S) m
        (mk v' {S with R := (Function.update S.R src
          (cstream A (p+E+5) (cyclicInterval a n (fun i => finalRoundWord w q p j (D i)))++tail))}) ∧
      PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
        (cyclicIntervalRead p (p+E+5) a
          (cstream A (p+E+5) (cyclicInterval a n (fun i => finalRoundWord w q p j (D i)))++tail))
        (fun i => ((2 : ℂ)^j)⁻¹*z i) (2/(2 : ℝ)^p+e/(2 : ℝ)^j) := by
  obtain ⟨v',m,hu,hm,hexec⟩ := roundPackedKey_exec (body := body) hA rg hrg ports hports hsep hreg hscalar
    B w q p j E n w wl hwl st hval hp hw hsize hroom hfit
    (cyclicInterval a n D) (by simp) tail v S hS hrows hwidth hsrc hblank hheaders
  refine ⟨v',m,hu,?_,?_,?_⟩
  · simpa only [cyclicInterval_length] using hm
  · simpa only [cyclicInterval,List.map_map,Function.comp_def] using hexec
  · exact cyclicFinalRound_accuracy hA p q j w (p+E+5) E a n hp hw le_rfl ha D z e he hz oldTail tail hgood

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
