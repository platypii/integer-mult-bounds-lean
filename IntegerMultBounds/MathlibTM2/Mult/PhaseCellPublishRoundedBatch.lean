module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishRoundedKey
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoundPackedBatch

/-! Common-width publication derives its fits and accuracy from the solver output. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- The supplied decoded scalar certificate determines both signed fits and
the final common-width error. Publication constructs all private dimensions;
neither output fits nor a common-width accuracy witness is supplied. -/
theorem publishRoundedBatch_exec {precision wide width replicas rows rowWidth count src work saved tmp extra : Fin T}
    (hreg : [precision,wide,width,replicas,rows,rowWidth,count,src,work,saved,tmp,extra].Nodup)
    (hA : 4 ≤ A) (p q j w W : ℕ) (hp : p ≤ q) (hw : 1 ≤ w) (hW : 2*p+13 ≤ W)
    {s : ℕ} [NeZero s] (a L : ℕ) (hinterval : a+L ≤ s)
    (active : Finset (ZMod s)) (hactive : ∀ i ∈ active, a ≤ i.val ∧ i.val < a+L)
    (hcover : ∀ i : ZMod s, a ≤ i.val → i.val < a+L → i ∈ active)
    (Zs : List (ZMod s → ℂ)) (Ds : List (ZMod s → GaussianInt)) (e : ℝ) (he : e ≤ 1)
    (hz : ∀ z ∈ Zs, ∀ i ∈ active, ‖z i‖ ≤ 4*(2 : ℝ)^(p+8))
    (oldTail tail : List (Fin (A+4)))
    (hgood : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
      (packedIntervalRead q w a (cstream A w (packedInterval a L D)++oldTail)) z e) Zs Ds)
    (v : HS T Q A U) (S : Stacks T A)
    (hprecision : (S.R precision).length = p) (hwide : (S.R wide).length = W)
    (hreplicas : (S.R replicas).length = Ds.length) (hrows : (S.R rows).length = L)
    (hsrc : S.R src = (Ds.map (fun D => cstream A (2*p+13)
      (packedInterval a L (fun i => finalRoundWord w q p j (D i))))).flatten++tail)
    (hblank : ∀ r ∈ [width,rowWidth,count,work,saved,tmp,extra], S.R r = []) :
    let Gs := Ds.map (fun D i => finalRoundWord w q p j (D i))
    Gs.length = Ds.length ∧
    ∃ v' n, v'.user = v.user ∧ n ≤ publishRoundedKeyCost p W Ds.length L ∧
      Exec body (publishRoundedKey precision wide width replicas rows rowWidth count src work saved tmp extra)
        (mk v S) n (mk v' {S with R := (Function.update S.R src
          ((Gs.map (fun D => cstream A W (packedInterval a L D))).flatten++tail))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
        (packedIntervalRead p W a (cstream A W (packedInterval a L D)++tail)) z
          (2/(2 : ℝ)^p+e/(2 : ℝ)^j)) (Zs.map (fun z i => ((2 : ℂ)^j)⁻¹*z i)) Gs := by
  dsimp only
  let xs := ((Ds.map (packedInterval a L)).flatten).map (finalRoundWord w q p j)
  have hlen : xs.length = Ds.length*L := by
    dsimp only [xs]
    rw [List.length_map,packedBatch_length a L Ds hinterval]
  have hfits : ∀ x ∈ xs, Fits (2*p+13) x :=
    packedFinalRoundBatch_fits hA p q j w (2*p+13) (p+8) a L hp hw (by omega)
      active hinterval hcover Zs Ds e he hz oldTail hgood
  have htop : ∀ x ∈ xs, TopFitsZ (2*p+13) x := by
    intro x hx
    have hf := hfits x hx
    exact ⟨⟨(abs_lt.mp hf.1).1.le,(abs_lt.mp hf.1).2⟩,
      ⟨(abs_lt.mp hf.2).1.le,(abs_lt.mp hf.2).2⟩⟩
  obtain ⟨v',n,hu,hn,hexec⟩ := publishRoundedKey_exec (body := body) hreg p W Ds.length L hW xs hlen htop
    tail v S hprecision hwide hreplicas hrows
    (by simpa only [xs,packedBatch_round_source] using hsrc) hblank
  refine ⟨List.length_map ..,v',n,hu,hn,?_,?_⟩
  · simpa only [xs,packedBatch_round_source,List.map_map,Function.comp_def] using hexec
  · exact packedFinalRoundBatch_accuracy hA p q j w W (p+8) a L hp hw (by omega) active hinterval hactive
      Zs Ds e he hz oldTail tail hgood

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
