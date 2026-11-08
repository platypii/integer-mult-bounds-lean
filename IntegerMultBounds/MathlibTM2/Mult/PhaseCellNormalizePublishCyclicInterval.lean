module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCyclicRounding
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishRoundedScalar
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseScalarBank

/-! Round and publish at common width using one scalar setup and one disposal. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def normalizePublishCyclicInterval (rg : TblR 25 → Fin T) (ports : Fin 4 → Fin T)
    (header word saved tmp carry pSrc qSrc rows width count src work sp sg cy precision wide replicas : Fin T) : Pr P T Q A U :=
  .seq (prepareCyclicRounding rg ports header word saved tmp carry pSrc qSrc rows width count src work sp sg cy)
    (.seq (publishRoundedScalar rg precision wide (ports 0) replicas rows (ports 1) count src work saved tmp (ports 2))
      (releaseScalarBank rg))

theorem normalizePublishCyclicInterval_exec (hA : 4 ≤ A)
    (rg : TblR 25 → Fin T) (hrg : Function.Injective rg)
    (ports : Fin 4 → Fin T) (hports : Function.Injective ports)
    (header word saved tmp carry pSrc qSrc rows width count src work sp sg cy : Fin T)
    (hheader : ∀ r, rg r ≠ header)
    (hregs : ∀ k ∈ [pSrc,qSrc], [k,rg .wr,word,saved,tmp,header].Nodup)
    (hreg : [rows,width,count,src,work,saved,tmp,ports 0,ports 1,ports 2,ports 3,sp,sg,cy].Nodup)
    (hsep : ∀ k ∈ [rows,width,count,src,work,saved,tmp,ports 0,ports 1,ports 2,ports 3,sp,sg,cy], ∀ r, rg r ≠ k)
    (precision wide replicas : Fin T)
    (hpubreg : [precision,wide,ports 0,replicas,rows,ports 1,count,src,work,saved,tmp,ports 2].Nodup)
    (hpubsep : ∀ k ∈ [precision,wide,ports 0,replicas,rows,ports 1,count,src,work,saved,tmp,ports 2], ∀ r, rg r ≠ k)
    (B p q W : ℕ) (hW : 2*p+13 ≤ W) (wl : List (Fin (A+4))) (hwl : wl.length = B)
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
    (hwide : (S.R wide).length = W)
    (hpubblank : ∀ k ∈ [precision,replicas,ports 0,ports 1,count,work,saved,tmp,ports 2], S.R k = [])
    (hsrc : S.R src = cstream A (2*q+8) (cyclicInterval a n D)++tail) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ binaryHeaderQueueCost S.R B [pSrc,qSrc]+25*(4*B+4)+2*(8*B+8)+2+
        (18+(4*Nat.size (4*p)+31))*tblC B 0+
        roundPackedKeyCost B (2*q+8) (2*p+13) n (2*q+8) n+
        publishRoundedScalarCost B p W n+(2*(25*B)+2*25+1) ∧
      Exec body (normalizePublishCyclicInterval rg ports header word saved tmp carry pSrc qSrc
        rows width count src work sp sg cy precision wide replicas) (mk v S) m
        (mk v' {S with R := (Function.update S.R src
          (cstream A W (cyclicInterval a n
            (fun i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i)))++tail))}) ∧
      PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
        (cyclicIntervalRead p W a
          (cstream A W (cyclicInterval a n
            (fun i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i)))++tail))
        (fun i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*z i)
        (2/(2 : ℝ)^p+e/(2 : ℝ)^inverseNormalizationShift p) := by
  obtain ⟨v₁,F₁,m₁,st,hu₁,hm₁,he₁,hh₁,hval,hfit,hacc,hin₁,hout₁,hL₁,hframe₁,hfits,_⟩ :=
    prepareCyclicRounding_exec (body := body) hA rg hrg ports hports
      header word saved tmp carry pSrc qSrc rows width count src work sp sg cy
      hheader hregs hreg hsep B p q wl hwl hPRoom hselectionRoom hwidthRoom hpq hsize
      a n ha hn D z e he hz oldTail tail hgood v S hwidth hp hq hrows hwordWidth hblank hwork hsmall hheaders hsrc
  let xs := cyclicInterval a n (fun i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i))
  have hpScalar : st.val 0 = p := by
    simpa [TblSt.restrict,inverseRoundVariables] using congrFun hval (2 : Fin 8)
  have htop : ∀ x ∈ xs, TopFitsZ (2*p+13) x := by
    intro x hx
    have hf := hfits x hx
    exact ⟨⟨(abs_lt.mp hf.1).1.le,(abs_lt.mp hf.1).2⟩,
      ⟨(abs_lt.mp hf.2).1.le,(abs_lt.mp hf.2).2⟩⟩
  have hr := hpubreg
  regs_ne hr
  have hread k (hk : k ∈ [precision,wide,ports 0,replicas,rows,ports 1,count,src,work,saved,tmp,ports 2]) :
      F₁.R k = Function.update S.R src (cstream A (2*p+13) xs++tail) k := hframe₁ k (hpubsep k hk)
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := publishRoundedScalar_exec (body := body) rg hrg hpubreg
    (hpubsep precision (by simp)) B p W n hW wl st hpScalar hfit xs (by simp [xs]) htop tail v₁ F₁ hh₁
    (by simpa only [hread wide (by simp),Function.update_of_ne ‹wide ≠ src›] using hwide)
    (by simpa only [hread rows (by simp),Function.update_of_ne ‹rows ≠ src›] using hrows)
    (by simp only [hread src (by simp),Function.update_self])
    (by intro k hk
        have hmem : k ∈ [precision,wide,ports 0,replicas,rows,ports 1,count,src,work,saved,tmp,ports 2] := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
        have hne : k ≠ src := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with hk | hk | hk | hk | hk | hk | hk | hk | hk <;>
            subst k <;> first | assumption | exact Ne.symm (by assumption)
        rw [hread k hmem,Function.update_of_ne hne]
        exact hpubblank k hk)
  let ys := cstream A W xs++tail
  let F₂ : Stacks T A := {F₁ with R := Function.update F₁.R src ys}
  let F : Stacks T A := {S with R := Function.update S.R src ys}
  have hsrcSep : ∀ r, rg r ≠ src := hpubsep src (by simp)
  have hh₂ : tblHolds rg F₂ (tblRho B wl [] st) := by
    intro r
    simpa only [F₂,Function.update_of_ne (hsrcSep r)] using hh₁ r
  obtain ⟨v₃,hu₃,he₃⟩ := releaseScalarBank_to_state_exec (body := body) rg hrg B wl st hacc v₂ F₂ F hh₂
    (by simpa [F,hsrcSep .wr] using hwidth)
    (by intro r hr; simpa [F,hsrcSep r] using hblank r hr)
    hin₁ hout₁ hL₁ (by
      intro k hoff
      by_cases hk : k = src
      · subst k; simp [F₂,F]
      · simpa [F₂,F,hk] using hframe₁ k hoff)
  exact ⟨v₃,m₁+(m₂+(2*(25*B)+2*25+1)),hu₃.trans (hu₂.trans hu₁),by omega,
    Exec.seq he₁ (Exec.seq he₂ he₃),
    cyclicFinalRound_accuracy hA p q (inverseNormalizationShift p) (2*q+8) W (p+8) a n hpq
      (by omega) (by omega) ha D z e he hz oldTail tail hgood⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
