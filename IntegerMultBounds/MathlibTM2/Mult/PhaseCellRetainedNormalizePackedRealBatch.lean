module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizePackedRealBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallRetainedRoundScalars
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseScalarBank
public import IntegerMultBounds.MathlibTM2.Mult.ChirpUnaryCopies

/-! Retained kernel length and precision generate one scalar bank for an entire
real recovery archive. Common-width publication is followed by paid disposal. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def retainedNormalizePackedRealBatch (rg : TblR 25 → Fin T) (ports : Fin 4 → Fin T)
    (header word saved tmp carry pSrc qSrc precision wide rows replicas inputWidth count src work sp sg cy : Fin T) : Pr P T Q A U :=
  .seq (installRetainedRoundScalars rg header word saved tmp carry pSrc qSrc)
    (.seq (tblUnaryCopies rg [(0,precision)])
      (.seq (normalizePackedBatch (rg ∘ TblR.rename inverseRoundVariables) ports
        precision wide rows replicas inputWidth count src work saved tmp sp sg cy)
        (.seq (uclear precision) (releaseScalarBank rg))))

theorem retainedNormalizePackedRealBatch_exec (hA : 4 ≤ A)
    (rg : TblR 25 → Fin T) (hrg : Function.Injective rg)
    (ports : Fin 4 → Fin T) (hportsInj : Function.Injective ports)
    (header word saved tmp carry pSrc qSrc precision wide rows replicas inputWidth count src work sp sg cy : Fin T)
    (hheader : ∀ r, rg r ≠ header)
    (hregs : ∀ k ∈ [pSrc,qSrc], [k,rg .wr,word,saved,tmp,header].Nodup)
    (hreg : [precision,wide,rows,replicas,inputWidth,count,src,work,saved,tmp,
      ports 0,ports 1,ports 2,ports 3,sp,sg,cy].Nodup)
    (hsep : ∀ k ∈ [precision,wide,rows,replicas,inputWidth,count,src,work,saved,tmp,sp,sg,cy], ∀ r, rg r ≠ k)
    (hports : ∀ i r, rg r ≠ ports i)
    (B p q W : ℕ) (wl : List (Fin (A+4))) (hwl : wl.length = B)
    (hPRoom : 2^15*p < 2^B) (hselectionRoom : 8*(p+2) < 2^B) (hwidthRoom : 2*q+8 < 2^B)
    (hpq : p ≤ q) (hsize : q-p+inverseNormalizationShift p+(2*p+13) ≤ 2*q+8)
    (hW : 2*p+13 ≤ W)
    {s : ℕ} [NeZero s] (a L : ℕ) (hinterval : a+L ≤ s)
    (active : Finset (ZMod s)) (hactive : ∀ i ∈ active, a ≤ i.val ∧ i.val < a+L)
    (hcover : ∀ i : ZMod s, a ≤ i.val → i.val < a+L → i ∈ active)
    (xs : List (ZMod s → ℝ)) (Ds : List (ZMod s → GaussianInt)) (e : ℝ) (he : e ≤ 1)
    (hx : ∀ x ∈ xs, ∀ i ∈ active, ‖x i‖ ≤ 4*(2 : ℝ)^(p+8))
    (hreal : ∀ D ∈ Ds, ∀ i, (D i).im = 0) (hfits : ∀ D ∈ Ds, ∀ i, Fits (2*q+8) (D i))
    (tail : List (Fin (A+4)))
    (hgood : List.Forall₂ (fun x D =>
      PhaseCellInterface.ErrorOn active (fun i => (value q (D i)).re) x e) xs Ds)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg .wr) = wl) (hbankBlank : ∀ r : TblR 25, r ≠ .wr → S.R (rg r) = [])
    (hp : (S.R pSrc).length = 2^15*p) (hq : (S.R qSrc).length = q)
    (hwork : ∀ k ∈ [word,saved,tmp], S.R k = [])
    (hprecision : S.R precision = []) (hwide : (S.R wide).length = W)
    (hrows : (S.R rows).length = L) (hreplicas : (S.R replicas).length = Ds.length)
    (hinputWidth : (S.R inputWidth).length = L*(2*q+8))
    (hsrc : S.R src = (Ds.map (fun D => cstream A (2*q+8) (packedInterval a L D))).flatten++tail)
    (hblank : ∀ r ∈ [count,work,saved,tmp,sp,sg,cy], S.R r = [])
    (hheaders : ∀ i, S.R (ports i) = []) :
    let Gs := Ds.map (fun D i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i))
    ∃ v' n, v'.user = v.user ∧
      n ≤ binaryHeaderQueueCost S.R B [pSrc,qSrc]+25*(4*B+4)+2*(8*B+8)+2+
        (18+(4*Nat.size (4*p)+31))*tblC B 0+
        normalizePackedBatchCost B (2*q+8) p W Ds.length L+(8*p+11*B+9)+(2*(25*B)+2*25+1) ∧
      Exec body (retainedNormalizePackedRealBatch rg ports header word saved tmp carry pSrc qSrc
        precision wide rows replicas inputWidth count src work sp sg cy)
        (mk v S) n (mk v' {S with R := (Function.update S.R src
          ((Gs.map (fun D => cstream A W (packedInterval a L D))).flatten++tail))}) ∧
      List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn active
        (packedIntervalRead p W a (cstream A W (packedInterval a L D)++tail))
        (fun i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*(x i : ℂ))
        (2/(2 : ℝ)^p+e/(2 : ℝ)^inverseNormalizationShift p)) xs Gs := by
  dsimp only
  obtain ⟨v₁,F,m₁,z,hu₁,hm₁,he₁,hh₁,hview,hval,hfit,hacc,hin,hout,hL,hframe⟩ :=
    installRetainedRoundScalars_exec (body := body) rg hrg header word saved tmp carry pSrc qSrc
      hheader hregs B p q wl hwl hPRoom hselectionRoom hwidthRoom v S hwidth hp hq hbankBlank hwork
  have hread k (hk : k ∈ [precision,wide,rows,replicas,inputWidth,count,src,work,saved,tmp,sp,sg,cy]) :
      F.R k = S.R k := hframe k (hsep k hk)
  have hprecisionOff : ∀ r, rg r ≠ precision := hsep precision (by simp)
  have hpScalar : z.val 0 = p := by
    simpa [TblSt.restrict,inverseRoundVariables] using congrFun hval (2 : Fin 8)
  obtain ⟨vi,mi,hui,hmi,hei⟩ := tblUnaryCopies_exec (body := body) hrg wl [] z hfit
    [(0,precision)] (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact hprecisionOff) v₁ F hh₁
  let F' : Stacks T A := {F with R := Function.update F.R precision (List.replicate p tick)}
  have hprecF : F.R precision = [] := (hread precision (by simp)).trans hprecision
  have hei' : Exec body (tblUnaryCopies rg [(0,precision)]) (mk v₁ F) mi (mk vi F') := by
    simpa only [F',unaryCopiesR,hpScalar,hprecF,List.append_nil] using hei
  have hmi' : mi ≤ 6*p+11*B+7 := by simpa [unaryCopiesCost,hpScalar] using hmi
  have hview' : tblHolds (rg ∘ TblR.rename inverseRoundVariables) F'
      (tblRho B wl [] (z.restrict inverseRoundVariables)) := by
    intro r
    simpa [F',hprecisionOff] using hview r
  have hr := hreg
  regs_ne hr
  have hread' k (hk : k ∈ [wide,rows,replicas,inputWidth,count,src,work,saved,tmp,sp,sg,cy]) :
      F'.R k = S.R k := by
    have hkprec : k ≠ precision := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk <;>
        subst k <;> first | assumption | exact Ne.symm (by assumption)
    have hm : k ∈ [precision,wide,rows,replicas,inputWidth,count,src,work,saved,tmp,sp,sg,cy] :=
      List.mem_cons_of_mem precision hk
    simpa [F',hkprec] using hread k hm
  obtain ⟨_,v₂,m₂,hu₂,hm₂,he₂,haccuracy⟩ := normalizePackedRealBatch_exec (body := body) hA
    (rg ∘ TblR.rename inverseRoundVariables)
    (hrg.comp (TblR.rename_injective inverseRoundVariables_injective)) ports hportsInj
    (by intro i r; exact hports i _) hreg
    (by intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with hr | hr | hr | hr <;> exact hsep _ (by simp) _ hr)
    B (2*q+8) q p (inverseNormalizationShift p) W wl hwl (z.restrict inverseRoundVariables)
    hval hpq (by omega) hsize hwidthRoom (by intro i; exact hfit _) hW
    a L hinterval active hactive hcover xs Ds e he hx hreal hfits tail hgood vi F' hview'
    (by simp [F'])
    (by simpa only [hread' wide (by simp)] using hwide)
    (by simpa only [hread' rows (by simp)] using hrows)
    (by simpa only [hread' replicas (by simp)] using hreplicas)
    (by simpa only [hread' inputWidth (by simp)] using hinputWidth)
    (by simpa only [hread' src (by simp)] using hsrc)
    (by intro k hk
        have hm : k ∈ [wide,rows,replicas,inputWidth,count,src,work,saved,tmp,sp,sg,cy] := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
        exact (hread' k hm).trans (hblank k hk))
    (by intro i
        have hne : ports i ≠ precision := by
          fin_cases i <;> first | assumption | exact Ne.symm (by assumption)
        simpa [F',hne] using (hframe _ (hports i)).trans (hheaders i))
  let ys := ((Ds.map (fun D i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i))).map
    (fun D => cstream A W (packedInterval a L D))).flatten++tail
  let G : Stacks T A := {F' with R := Function.update F'.R src ys}
  obtain ⟨vc,huc,hec⟩ := uclear_exec body precision v₂ G
  let G' : Stacks T A := {G with R := Function.update G.R precision []}
  have hec' : Exec body (uclear precision) (mk v₂ G) (2*p+2) (mk vc G') := by
    simpa [G,F',‹precision ≠ src›] using hec
  let S' : Stacks T A := {S with R := Function.update S.R src ys}
  have hsrcOff : ∀ r, rg r ≠ src := hsep src (by simp)
  have hhG : tblHolds rg G' (tblRho B wl [] z) := by
    intro r
    simpa [G',G,F',hsrcOff r,hprecisionOff r] using hh₁ r
  obtain ⟨v₃,hu₃,he₃⟩ := releaseScalarBank_to_state_exec (body := body) rg hrg B wl z hacc vc G' S' hhG
    (by simpa [S',hsrcOff .wr] using hwidth)
    (by intro r hr; simpa [S',hsrcOff r] using hbankBlank r hr) hin hout hL
    (by intro k hoff
        by_cases hk : k = src
        · subst k; simp [G',G,S',‹precision ≠ src›.symm]
        · by_cases hkp : k = precision
          · subst k; simp [G',S',‹precision ≠ src›,hprecision]
          · simpa [G',G,F',S',hk,hkp] using hframe k hoff)
  exact ⟨v₃,m₁+(mi+(m₂+((2*p+2)+(2*(25*B)+2*25+1)))),
    hu₃.trans (huc.trans (hu₂.trans (hui.trans hu₁))),by omega,
    Exec.seq he₁ (Exec.seq hei' (Exec.seq he₂ (Exec.seq hec' he₃))),haccuracy⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
