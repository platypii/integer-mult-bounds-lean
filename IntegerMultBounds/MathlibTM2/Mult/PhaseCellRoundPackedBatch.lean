module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoundPackedKey
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRoundAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBatchInputData

/-! Execute local batch normalization and certify those same emitted packets. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem packedBatch_round_source {s : ℕ} (A w q p j k a L : ℕ)
    (Ds : List (ZMod s → GaussianInt)) :
    cstream A k (((Ds.map (packedInterval a L)).flatten).map (finalRoundWord w q p j)) =
      ((Ds.map (fun D => cstream A k (packedInterval a L (fun i => finalRoundWord w q p j (D i)))))).flatten := by
  rw [packedBatch_map,cstream_flatten]
  simp only [List.map_map,Function.comp_def]

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Normalize only the actual local numerical packets, generate/erase their
count, and return the decoded accuracy for the same ordered output fields. -/
theorem roundPackedBatch_exec (hA : 4 ≤ A)
    (rg : TblR 8 → Fin T) (hrg : Function.Injective rg)
    (ports : Fin 4 → Fin T) (hports : Function.Injective ports)
    (hsep : ∀ i r, rg r ≠ ports i)
    {replicas width count src work saved tmp sp sg cy : Fin T}
    (hreg : [replicas,width,count,src,work,saved,tmp,ports 0,ports 1,ports 2,ports 3,sp,sg,cy].Nodup)
    (hscalar : ∀ r, rg r ∉ [count,src,work,saved])
    (B w q p j E : ℕ) (wl : List (Fin (A+4))) (hwl : wl.length = B)
    (st : TblSt 8 A) (hval : st.val = ![w,q,p,j,E,0,0,0])
    (hp : p ≤ q) (hw : 1 ≤ w) (hsize : q-p+j+(p+E+5) ≤ w)
    (hroom : w < 2^B) (hfit : ∀ i, st.val i < 2^B)
    {s : ℕ} [NeZero s] (a L : ℕ) (hinterval : a+L ≤ s)
    (active : Finset (ZMod s)) (hactive : ∀ i ∈ active, a ≤ i.val ∧ i.val < a+L)
    (Zs : List (ZMod s → ℂ)) (Ds : List (ZMod s → GaussianInt)) (e : ℝ) (he : e ≤ 1)
    (hz : ∀ z ∈ Zs, ∀ i ∈ active, ‖z i‖ ≤ 4*(2 : ℝ)^E)
    (oldTail tail : List (Fin (A+4)))
    (hgood : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
      (packedIntervalRead q w a (cstream A w (packedInterval a L D)++oldTail)) z e) Zs Ds)
    (v : HS T Q A U) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho B wl [] st))
    (hreplicas : (S.R replicas).length = Ds.length) (hwidth : (S.R width).length = L*w)
    (hsrc : S.R src = (Ds.map (fun D => cstream A w (packedInterval a L D))).flatten++tail)
    (hblank : ∀ r ∈ [count,work,saved,tmp,sp,sg,cy], S.R r = [])
    (hheaders : ∀ i, S.R (ports i) = []) :
    let Gs := Ds.map (fun D i => finalRoundWord w q p j (D i))
    Gs.length = Ds.length ∧
    ∃ v' n, v'.user = v.user ∧
      n ≤ roundPackedKeyCost B w (p+E+5) Ds.length (L*w) (Ds.length*L) ∧
      Exec body (roundPackedKey rg ports replicas width count src work saved tmp sp sg cy) (mk v S) n
        (mk v' {S with R := (Function.update S.R src
          ((Gs.map (fun D => cstream A (p+E+5) (packedInterval a L D))).flatten++tail))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
        (packedIntervalRead p (p+E+5) a (cstream A (p+E+5) (packedInterval a L D)++tail)) z
          (2/(2 : ℝ)^p+e/(2 : ℝ)^j)) (Zs.map (fun z i => ((2 : ℂ)^j)⁻¹*z i)) Gs := by
  dsimp only
  have hlen := packedBatch_length a L Ds hinterval
  obtain ⟨v',n,hu,hn,hexec⟩ := roundPackedKey_exec (body := body) hA rg hrg ports hports hsep hreg hscalar
    B w q p j E Ds.length (L*w) wl hwl st hval hp hw hsize hroom hfit
    (Ds.map (packedInterval a L)).flatten (by rw [hlen]; ring) tail v S hS hreplicas hwidth
    (by simpa only [cstream_flatten,List.map_map,Function.comp_def] using hsrc) hblank hheaders
  refine ⟨List.length_map ..,v',n,hu,?_,?_,?_⟩
  · simpa only [hlen] using hn
  · simpa only [packedBatch_round_source,List.map_map,Function.comp_def] using hexec
  · exact packedFinalRoundBatch_accuracy hA p q j w (p+E+5) E a L hp hw le_rfl active hinterval hactive
      Zs Ds e he hz oldTail tail hgood

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
