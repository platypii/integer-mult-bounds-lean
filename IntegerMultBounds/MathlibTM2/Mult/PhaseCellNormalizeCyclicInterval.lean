module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallRetainedRoundScalars
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoundCyclicInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseScalarBank

/-! Generate, use and dispose rounding scalars around the existing cyclic list executor. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def normalizeCyclicInterval (rg : TblR 25 → Fin T) (ports : Fin 4 → Fin T)
    (header word saved tmp carry pSrc qSrc rows width count src work sp sg cy : Fin T) : Pr P T Q A U :=
  .seq (installRetainedRoundScalars rg header word saved tmp carry pSrc qSrc)
    (.seq (roundPackedKey (rg ∘ TblR.rename inverseRoundVariables) ports
      rows width count src work saved tmp sp sg cy) (releaseScalarBank rg))

theorem normalizeCyclicInterval_exec (hA : 4 ≤ A)
    (rg : TblR 25 → Fin T) (hrg : Function.Injective rg)
    (ports : Fin 4 → Fin T) (hports : Function.Injective ports)
    (header word saved tmp carry pSrc qSrc rows width count src work sp sg cy : Fin T)
    (hheader : ∀ r, rg r ≠ header)
    (hregs : ∀ k ∈ [pSrc,qSrc], [k,rg .wr,word,saved,tmp,header].Nodup)
    (hreg : [rows,width,count,src,work,saved,tmp,ports 0,ports 1,ports 2,ports 3,sp,sg,cy].Nodup)
    (hsep : ∀ k ∈ [rows,width,count,src,work,saved,tmp,ports 0,ports 1,ports 2,ports 3,sp,sg,cy], ∀ r, rg r ≠ k)
    (B p q : ℕ) (wl : List (Fin (A+4))) (hwl : wl.length = B)
    (hPRoom : 2^15*p < 2^B) (hselectionRoom : 8*(p+2) < 2^B) (hwidthRoom : 2*q+8 < 2^B)
    (hpq : p ≤ q) (hsize : q-p+inverseNormalizationShift p+(2*p+13) ≤ 2*q+8)
    {s : ℕ} [NeZero s] (a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (D : ZMod s → GaussianInt) (z : ZMod s → ℂ) (e : ℝ) (he : e ≤ 1)
    (hz : ∀ i ∈ cyclicPrincipalVertices s a n, ‖z i‖ ≤ 4*(2 : ℝ)^(p+8))
    (oldTail tail : List (Fin (A+4)))
    (hgood : PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
      (cyclicIntervalRead q (2*q+8) a (cstream A (2*q+8) (cyclicInterval a n D)++oldTail)) z e)
    (v : HS T Q A U) (S : Stacks T A) (hwidth : S.R (rg .wr) = wl)
    (hp : (S.R pSrc).length = 2^15*p) (hq : (S.R qSrc).length = q)
    (hrows : (S.R rows).length = n) (hwordWidth : (S.R width).length = 2*q+8)
    (hblank : ∀ r : TblR 25, r ≠ .wr → S.R (rg r) = [])
    (hwork : ∀ k ∈ [word,saved,tmp], S.R k = [])
    (hsmall : ∀ k ∈ [count,work,saved,tmp,sp,sg,cy], S.R k = [])
    (hheaders : ∀ i, S.R (ports i) = [])
    (hsrc : S.R src = cstream A (2*q+8) (cyclicInterval a n D)++tail) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ binaryHeaderQueueCost S.R B [pSrc,qSrc]+25*(4*B+4)+2*(8*B+8)+2+
        (18+(4*Nat.size (4*p)+31))*tblC B 0+
        roundPackedKeyCost B (2*q+8) (2*p+13) n (2*q+8) n+(2*(25*B)+2*25+1) ∧
      Exec body (normalizeCyclicInterval rg ports header word saved tmp carry pSrc qSrc
        rows width count src work sp sg cy) (mk v S) m
        (mk v' {S with R := (Function.update S.R src
          (cstream A (2*p+13) (cyclicInterval a n
            (fun i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i)))++tail))}) ∧
      (∀ x ∈ cyclicInterval a n
        (fun i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i)), Fits (2*p+13) x) ∧
      PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
        (cyclicIntervalRead p (2*p+13) a
          (cstream A (2*p+13) (cyclicInterval a n
            (fun i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i)))++tail))
        (fun i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*z i)
        (2/(2 : ℝ)^p+e/(2 : ℝ)^inverseNormalizationShift p) := by
  obtain ⟨v₁,F₁,m₁,st,hu₁,hm₁,he₁,hh₁,hview,hval,hfit,hacc,hin₁,hout₁,hL₁,hframe₁⟩ :=
    installRetainedRoundScalars_exec (body := body) rg hrg header word saved tmp carry pSrc qSrc
      hheader hregs B p q wl hwl hPRoom hselectionRoom hwidthRoom v S hwidth hp hq hblank hwork
  have hread k (hk : k ∈ [rows,width,count,src,work,saved,tmp,ports 0,ports 1,ports 2,ports 3,sp,sg,cy]) :
      F₁.R k = S.R k := hframe₁ k (hsep k hk)
  have hk : p+(p+8)+5 = 2*p+13 := by omega
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂,haccuracy⟩ := roundCyclicInterval_exec (body := body) hA
    (rg ∘ TblR.rename inverseRoundVariables) (hrg.comp (TblR.rename_injective inverseRoundVariables_injective))
    ports hports (by intro i r; exact hsep (ports i) (by fin_cases i <;> simp) _)
    hreg (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with h | h | h | h
      · exact hsep count (by simp) _ h
      · exact hsep src (by simp) _ h
      · exact hsep work (by simp) _ h
      · exact hsep saved (by simp) _ h)
    B (2*q+8) q p (inverseNormalizationShift p) (p+8) wl hwl (st.restrict inverseRoundVariables) hval
    hpq (by omega) (by omega) hwidthRoom (by intro i; exact hfit _)
    a n ha D z e he hz oldTail tail hgood v₁ F₁ hview
    (by simpa only [hread rows (by simp)] using hrows)
    (by simpa only [hread width (by simp)] using hwordWidth)
    (by simpa only [hread src (by simp)] using hsrc)
    (by intro k hk; rw [hread k (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)]; exact hsmall k hk)
    (by intro i; rw [hread (ports i) (by fin_cases i <;> simp)]; exact hheaders i)
  simp only [hk] at hm₂ he₂ haccuracy
  let ys := cstream A (2*p+13) (cyclicInterval a n
    (fun i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i)))++tail
  let F₂ : Stacks T A := {F₁ with R := Function.update F₁.R src ys}
  let F : Stacks T A := {S with R := Function.update S.R src ys}
  have hsrcSep : ∀ r, rg r ≠ src := hsep src (by simp)
  have hh₂ : tblHolds rg F₂ (tblRho B wl [] st) := by
    intro r
    simpa only [F₂,Function.update_of_ne (hsrcSep r)] using hh₁ r
  obtain ⟨v₃,hu₃,he₃⟩ := releaseScalarBank_to_state_exec (body := body) rg hrg B wl st hacc v₂ F₂ F hh₂
    (by simpa [F,hsrcSep .wr] using hwidth)
    (by intro r hr; simpa [F,hsrcSep r] using hblank r hr)
    hin₁ hout₁ hL₁ (by
      intro i hoff
      by_cases hi : i = src
      · subst i; simp [F₂,F]
      · simpa [F₂,F,hi] using hframe₁ i hoff)
  exact ⟨v₃,m₁+(m₂+(2*(25*B)+2*25+1)),hu₃.trans (hu₂.trans hu₁),
    by omega,Exec.seq he₁ (Exec.seq he₂ he₃),
    cyclicFinalRound_fits hA p q (inverseNormalizationShift p) (2*q+8) (2*p+13) (p+8)
      a n hpq (by omega) (by omega) ha hn D z e he hz oldTail hgood,haccuracy⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
