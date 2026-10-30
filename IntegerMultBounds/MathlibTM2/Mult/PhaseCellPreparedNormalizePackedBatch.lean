module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizePackedBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareRoundScalars
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseRoundScalars

/-! Compute normalization scalars, execute the local batch and restore the scalar bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def preparedNormalizePackedBatch (rg : TblR 25 → Fin T) (ports : Fin 4 → Fin T)
    (precision wide rows replicas inputWidth count src work saved tmp sp sg cy : Fin T) : Pr P T Q A U :=
  .seq (tblCompile rg tblPrepareInverseRound)
    (.seq (normalizePackedBatch (rg ∘ TblR.rename inverseRoundVariables) ports
      precision wide rows replicas inputWidth count src work saved tmp sp sg cy)
      (tblCompile rg tblClearInverseScalars))

noncomputable def preparedNormalizePackedBatchCost
    (B p u l target s t a b W N L : ℕ) [NeZero s] : ℕ :=
  let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card
    (PhaseCellBand.width p u)
  (inverseScalarAtoms p s t u a b+(4*Nat.size (4*p)+39))*tblC B 0+
    normalizePackedBatchCost B (8*E+8) p W N L

/-- The initial scalar bank contains only ordinary inverse inputs and zero
private variables. The actual setup, local rounding/publication and scalar
cleanup return that exact bank, changing only the output prefix. -/
theorem preparedNormalizePackedBatch_exec (hA : 4 ≤ A)
    (rg : TblR 25 → Fin T) (hrg : Function.Injective rg)
    (ports : Fin 4 → Fin T) (hports : Function.Injective ports)
    {precision wide rows replicas inputWidth count src work saved tmp sp sg cy : Fin T}
    (hreg : [precision,wide,rows,replicas,inputWidth,count,src,work,saved,tmp,
      ports 0,ports 1,ports 2,ports 3,sp,sg,cy].Nodup)
    (hsep : ∀ i ∈ [precision,wide,rows,replicas,inputWidth,count,src,work,saved,tmp,sp,sg,cy], ∀ r, rg r ≠ i)
    (hsepPorts : ∀ i r, rg r ≠ ports i)
    {B p u l target s t a b : ℕ} [NeZero s]
    (wl : List (Fin (A+4))) (hwl : wl.length = B) (st : TblSt 25 A)
    (h0 : st.val 0 = p) (h1 : st.val 1 = u) (h2 : st.val 2 = l) (h3 : st.val 3 = target)
    (h4 : st.val 4 = s) (h5 : st.val 5 = t) (h6 : st.val 6 = a) (h7 : st.val 7 = b)
    (hzero : ∀ i : Fin 25, 8 ≤ i.val → st.val i = 0)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : PhaseCellBand.width p u ≤ s)
    (hbandRoom : 64*(p+1)+u < 2^B)
    (hgeometryRoom : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^B)
    (hprecisionRoom : inversePrecisionRoom p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card
      (PhaseCellBand.width p u) < 2^B) (hfit : ∀ i, st.val i < 2^B)
    (W c L : ℕ) (hW : 2*p+13 ≤ W) (hinterval : c+L ≤ s)
    (active : Finset (ZMod s)) (hactive : ∀ i ∈ active, c ≤ i.val ∧ i.val < c+L)
    (hcover : ∀ i : ZMod s, c ≤ i.val → i.val < c+L → i ∈ active)
    (Zs : List (ZMod s → ℂ)) (Ds : List (ZMod s → GaussianInt)) (e : ℝ) (he : e ≤ 1)
    (hz : ∀ z ∈ Zs, ∀ i ∈ active, ‖z i‖ ≤ 4*(2 : ℝ)^(p+8))
    (oldTail tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho B wl [] st))
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
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedNormalizePackedBatchCost B p u l target s t a b W Ds.length L ∧
      Exec body (preparedNormalizePackedBatch rg ports precision wide rows replicas inputWidth count src work saved tmp sp sg cy)
        (mk v S) n (mk v' {S with R := (Function.update S.R src
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
  obtain ⟨v₁,S₁,n₁,z,hu₁,hn₁,he₁,hh₁,hview,hval,hkeep,hacc,hfitZ,hin,hout,hL,hframe⟩ :=
    prepareRoundScalars_exec (body := body) rg hrg wl hwl st h0 h1 h2 h3 h4 h5 h6 h7 hst haS hbS hbandS
      hbandRoom hgeometryRoom hprecisionRoom hfit v S hS
  have hread i (hi : i ∈ [precision,wide,rows,replicas,inputWidth,count,src,work,saved,tmp,sp,sg,cy]) :
      S₁.R i = S.R i := hframe i (hsep i hi)
  have hsmall : ∀ r ∈ [count,work,saved,tmp,sp,sg,cy], S₁.R r = [] := by
    intro r hr
    have hr' : r ∈ [precision,wide,rows,replicas,inputWidth,count,src,work,saved,tmp,sp,sg,cy] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    exact (hread r hr').trans (hblank r hr)
  have hhead i : S₁.R (ports i) = [] := (hframe _ (hsepPorts i)).trans (hheaders i)
  have hscalar : ∀ r : TblR 8, (rg ∘ TblR.rename inverseRoundVariables) r ∉ [count,src,work,saved] := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with hr | hr | hr | hr <;>
      exact (hsep _ (by simp) (r.rename inverseRoundVariables)) hr
  have hdim := inverse_round_dimensions p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card
    (PhaseCellBand.width p u) j (inverseNormalizationShift_le p)
  have hwroom : w < 2^B := by
    have hh := congrFun hval 0
    change z.val 20 = w at hh
    rw [←hh]
    exact hfitZ 20
  obtain ⟨hlen,v₂,n₂,hu₂,hn₂,he₂,haccuracy⟩ := normalizePackedBatch_exec (body := body) hA
    (rg ∘ TblR.rename inverseRoundVariables) (hrg.comp (TblR.rename_injective inverseRoundVariables_injective))
    ports hports (fun i r => hsepPorts i (r.rename inverseRoundVariables)) hreg hscalar
    B w q p j W wl hwl (z.restrict inverseRoundVariables) hval
    hdim.1 (by dsimp [w]; omega)
    (by have hh := hdim.2.2; change q-p+j+(p+(p+8)+5) ≤ w at hh; omega) hwroom
    (fun i => hfitZ (inverseRoundVariables i)) hW c L hinterval active hactive hcover Zs Ds e he hz
    oldTail tail hgood v₁ S₁ hview
    ((hread precision (by simp) ▸ hprecision)) ((hread wide (by simp) ▸ hwide))
    ((hread rows (by simp) ▸ hrows)) ((hread replicas (by simp) ▸ hreplicas))
    ((hread inputWidth (by simp) ▸ hinputWidth)) ((hread src (by simp) ▸ hsrc)) hsmall hhead
  let ys := ((Ds.map (fun D i => finalRoundWord w q p j (D i))).map
    (fun D => cstream A W (packedInterval c L D))).flatten++tail
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R src ys}
  have hh₂ : tblHolds rg S₂ (tblRho B wl [] z) := by
    intro r
    simpa only [S₂,Function.update_of_ne (hsep src (by simp) r)] using hh₁ r
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := releaseRoundScalars_exec (body := body) rg hrg B wl hwl st z hfitZ
    (by intro i hi; exact hkeep ⟨i.val,hi⟩) hzero hacc src (hsep src (by simp)) ys v₂ S S₂ hS hh₂
    hin hout hL (by
      intro i hoff
      by_cases hi : i = src
      · subst i; simp [S₂]
      · simpa only [S₂,Function.update_of_ne hi] using hframe i hoff)
  refine ⟨hlen,v₃,n₁+n₂+n₃,hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by omega) rfl,haccuracy⟩
  unfold preparedNormalizePackedBatchCost
  change n₁+n₂+n₃ ≤ (inverseScalarAtoms p s t u a b+(4*Nat.size (4*p)+39))*tblC B 0+
    normalizePackedBatchCost B w p W Ds.length L
  nlinarith only [hn₁,hn₂,hn₃]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
