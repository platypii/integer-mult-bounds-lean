module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedNormalizePackedBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallInverseParameters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseScalarBank

/-! A complete local normalization caller from ordinary parameter words and blank scalars. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def ordinaryNormalizePackedBatch (rg : TblR 25 → Fin T) (ports : Fin 4 → Fin T)
    (headerSrc precision wide rows replicas inputWidth count src work saved tmp sp sg cy : Fin T) : Pr P T Q A U :=
  .seq (installInverseParameters rg headerSrc)
    (.seq (preparedNormalizePackedBatch rg ports precision wide rows replicas inputWidth count src work saved tmp sp sg cy)
      (releaseScalarBank rg))

/-- Start from actual ordinary parameter words and blank scalar storage, not an
encoded table. Only the parameter queue and normalized output change; the
entire scalar bank returns to blank storage except its borrowed width word. -/
theorem ordinaryNormalizePackedBatch_exec (hA : 4 ≤ A)
    (rg : TblR 25 → Fin T) (hrg : Function.Injective rg)
    (ports : Fin 4 → Fin T) (hports : Function.Injective ports)
    {headerSrc precision wide rows replicas inputWidth count src work saved tmp sp sg cy : Fin T}
    (hreg : [headerSrc,precision,wide,rows,replicas,inputWidth,count,src,work,saved,tmp,
      ports 0,ports 1,ports 2,ports 3,sp,sg,cy].Nodup)
    (hsep : ∀ i ∈ [precision,wide,rows,replicas,inputWidth,count,src,work,saved,tmp,sp,sg,cy], ∀ r, rg r ≠ i)
    (hsepPorts : ∀ i r, rg r ≠ ports i) (hsepHeader : ∀ r, rg r ≠ headerSrc)
    {B p u l target s t a b : ℕ} [NeZero s]
    (hvaluesFit : ∀ i : Fin 8, ![p,u,l,target,s,t,a,b] i < 2^B)
    (wl : List (Fin (A+4))) (hwl : wl.length = B)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : PhaseCellBand.width p u ≤ s)
    (hbandRoom : 64*(p+1)+u < 2^B)
    (hgeometryRoom : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^B)
    (hprecisionRoom : inversePrecisionRoom p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card
      (PhaseCellBand.width p u) < 2^B)
    (W c L : ℕ) (hW : 2*p+13 ≤ W) (hinterval : c+L ≤ s)
    (active : Finset (ZMod s)) (hactive : ∀ i ∈ active, c ≤ i.val ∧ i.val < c+L)
    (hcover : ∀ i : ZMod s, c ≤ i.val → i.val < c+L → i ∈ active)
    (Zs : List (ZMod s → ℂ)) (Ds : List (ZMod s → GaussianInt)) (e : ℝ) (he : e ≤ 1)
    (hz : ∀ z ∈ Zs, ∀ i ∈ active, ‖z i‖ ≤ 4*(2 : ℝ)^(p+8))
    (oldTail tail headerTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg .wr) = wl) (hbankBlank : ∀ r : TblR 25, r ≠ .wr → S.R (rg r) = [])
    (hparameters : S.R headerSrc = (inverseParameterWords p u l target s t a b).flatMap
      (fun r => binSyms B r.2)++headerTail)
    (hprecision : (S.R precision).length = p) (hwide : (S.R wide).length = W)
    (hrows : (S.R rows).length = L) (hreplicas : (S.R replicas).length = Ds.length)
    (hblank : ∀ r ∈ [count,work,saved,tmp,sp,sg,cy], S.R r = [])
    (hheaders : ∀ i, S.R (ports i) = []) :
    let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card
      (PhaseCellBand.width p u)
    let q := 4*E
    let w := 8*E+8
    let j := inverseNormalizationShift p
    (S.R inputWidth).length = L*w →
    S.R src = (Ds.map (fun D => cstream A w (packedInterval c L D))).flatten++tail →
    List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
      (packedIntervalRead q w c (cstream A w (packedInterval c L D)++oldTail)) z e) Zs Ds →
    let Gs := Ds.map (fun D i => finalRoundWord w q p j (D i))
    Gs.length = Ds.length ∧
    ∃ v' n, v'.user = v.user ∧
      n ≤ preparedNormalizePackedBatchCost B p u l target s t a b W Ds.length L+214*B+217 ∧
      Exec body (ordinaryNormalizePackedBatch rg ports headerSrc precision wide rows replicas inputWidth count src work saved tmp sp sg cy)
        (mk v S) n (mk v' {S with R := (Function.update (Function.update S.R headerSrc headerTail) src
          ((Gs.map (fun D => cstream A W (packedInterval c L D))).flatten++tail))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
        (packedIntervalRead p W c (cstream A W (packedInterval c L D)++tail)) z
          (2/(2 : ℝ)^p+e/(2 : ℝ)^j)) (Zs.map (fun z i => ((2 : ℂ)^j)⁻¹*z i)) Gs := by
  dsimp only
  let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card
    (PhaseCellBand.width p u)
  let q := 4*E
  let w := 8*E+8
  let j := inverseNormalizationShift p
  intro hinputWidth hsrc hgood
  obtain ⟨v₁,S₁,hu₁,he₁,hh₁,hfit,hs₁,hi₁,ho₁,hL₁,hf₁⟩ := installInverseParameters_exec (body := body)
    rg hrg headerSrc hsepHeader B p u l target s t a b hvaluesFit wl hwl headerTail v S hwidth hbankBlank hparameters
  have hheaderNe i (hi : i ∈ [precision,wide,rows,replicas,inputWidth,count,src,work,saved,tmp,
      ports 0,ports 1,ports 2,ports 3,sp,sg,cy]) : i ≠ headerSrc := by
    intro heq
    subst i
    exact (List.nodup_cons.mp hreg).1 hi
  have hread i (hi : i ∈ [precision,wide,rows,replicas,inputWidth,count,src,work,saved,tmp,sp,sg,cy]) :
      S₁.R i = S.R i := by
    apply hf₁ i ?_ (hsep i hi)
    apply hheaderNe
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have hsmall : ∀ r ∈ [count,work,saved,tmp,sp,sg,cy], S₁.R r = [] := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (hread _ (by simp)).trans (hblank _ (by simp))
  have hhead i : S₁.R (ports i) = [] :=
    (hf₁ _ (hheaderNe _ (by fin_cases i <;> simp)) (hsepPorts i)).trans (hheaders i)
  have hv i := inverseParameterState_inputs (A := A) p u l target s t a b i
  obtain ⟨hlen,v₂,n₂,hu₂,hn₂,he₂,haccuracy⟩ := preparedNormalizePackedBatch_exec (body := body) hA rg hrg ports hports
    (List.nodup_cons.mp hreg).2 hsep hsepPorts
    (B := B) (p := p) (u := u) (l := l) (target := target) (s := s) (t := t) (a := a) (b := b)
    wl hwl (inverseParameterState p u l target s t a b)
    (hv 0) (hv 1) (hv 2) (hv 3) (hv 4) (hv 5) (hv 6) (hv 7)
    (inverseParameterState_zero p u l target s t a b) hst haS hbS hbandS hbandRoom hgeometryRoom hprecisionRoom hfit
    W c L hW hinterval active hactive hcover Zs Ds e he hz oldTail tail v₁ S₁ hh₁
    (hread precision (by simp) ▸ hprecision) (hread wide (by simp) ▸ hwide)
    (hread rows (by simp) ▸ hrows) (hread replicas (by simp) ▸ hreplicas) hsmall hhead
    (hread inputWidth (by simp) ▸ hinputWidth) (hread src (by simp) ▸ hsrc) hgood
  let ys := ((Ds.map (fun D i => finalRoundWord w q p j (D i))).map
    (fun D => cstream A W (packedInterval c L D))).flatten++tail
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R src ys}
  let M : Stacks T A := {S with R := Function.update (Function.update S.R headerSrc headerTail) src ys}
  have hh₂ : tblHolds rg S₂ (tblRho B wl [] (inverseParameterState p u l target s t a b)) := by
    intro r
    simpa only [S₂,Function.update_of_ne (hsep src (by simp) r)] using hh₁ r
  obtain ⟨v₃,hu₃,he₃⟩ := releaseScalarBank_to_state_exec (body := body) rg hrg B wl
    (inverseParameterState p u l target s t a b) (inverseParameterState_acc ..) v₂ S₂ M hh₂
    (by simpa only [M,Function.update_of_ne (hsep src (by simp) .wr),Function.update_of_ne (hsepHeader .wr)] using hwidth)
    (by
      intro r hr
      simpa only [M,Function.update_of_ne (hsep src (by simp) r),Function.update_of_ne (hsepHeader r)] using hbankBlank r hr)
    hi₁ ho₁ hL₁ (by
      intro i hoff
      by_cases his : i = src
      · subst i; simp [S₂,M]
      · simp only [S₂,M,Function.update_of_ne his]
        by_cases hih : i = headerSrc
        · subst i; simpa using hs₁
        · rw [Function.update_of_ne hih]
          exact hf₁ i hih hoff)
  refine ⟨hlen,v₃,(164*B+166)+n₂+(2*(25*B)+2*25+1),hu₃.trans (hu₂.trans hu₁),by omega,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by omega) rfl,haccuracy⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
