module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishRoundedKey
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRoundAccuracy

/-! Common-width publication preserves the normalized cyclic packet's coefficients and error. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem publishCyclicRoundedInterval_exec {precision wide width replicas rows rowWidth count src work saved tmp extra : Fin T}
    (hreg : [precision,wide,width,replicas,rows,rowWidth,count,src,work,saved,tmp,extra].Nodup)
    (hA : 4 ≤ A) (p q j w W : ℕ) (hp : p ≤ q) (hw : 1 ≤ w) (hW : 2*p+13 ≤ W)
    {s : ℕ} [NeZero s] (a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (D : ZMod s → GaussianInt) (z : ZMod s → ℂ) (e : ℝ) (he : e ≤ 1)
    (hz : ∀ i ∈ cyclicPrincipalVertices s a n, ‖z i‖ ≤ 4*(2 : ℝ)^(p+8))
    (oldTail tail : List (Fin (A+4)))
    (hgood : PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
      (cyclicIntervalRead q w a (cstream A w (cyclicInterval a n D)++oldTail)) z e)
    (v : HS T Q A U) (S : Stacks T A)
    (hprecision : (S.R precision).length = p) (hwide : (S.R wide).length = W)
    (hreplicas : (S.R replicas).length = 1) (hrows : (S.R rows).length = n)
    (hsrc : S.R src = cstream A (2*p+13)
      (cyclicInterval a n (fun i => finalRoundWord w q p j (D i)))++tail)
    (hblank : ∀ r ∈ [width,rowWidth,count,work,saved,tmp,extra], S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ publishRoundedKeyCost p W 1 n ∧
      Exec body (publishRoundedKey precision wide width replicas rows rowWidth count src work saved tmp extra)
        (mk v S) m (mk v' {S with R := (Function.update S.R src
          (cstream A W (cyclicInterval a n (fun i => finalRoundWord w q p j (D i)))++tail))}) ∧
      PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
        (cyclicIntervalRead p W a
          (cstream A W (cyclicInterval a n (fun i => finalRoundWord w q p j (D i)))++tail))
        (fun i => ((2 : ℂ)^j)⁻¹*z i) (2/(2 : ℝ)^p+e/(2 : ℝ)^j) := by
  have hfits := cyclicFinalRound_fits hA p q j w (2*p+13) (p+8) a n hp hw (by omega)
    ha hn D z e he hz oldTail hgood
  have htop : ∀ x ∈ cyclicInterval a n (fun i => finalRoundWord w q p j (D i)), TopFitsZ (2*p+13) x := by
    intro x hx
    have hf := hfits x hx
    exact ⟨⟨(abs_lt.mp hf.1).1.le,(abs_lt.mp hf.1).2⟩,
      ⟨(abs_lt.mp hf.2).1.le,(abs_lt.mp hf.2).2⟩⟩
  obtain ⟨v',m,hu,hm,hexec⟩ := publishRoundedKey_exec (body := body) hreg p W 1 n hW
    (cyclicInterval a n (fun i => finalRoundWord w q p j (D i))) (by simp) htop
    tail v S hprecision hwide hreplicas hrows hsrc hblank
  exact ⟨v',m,hu,hm,hexec,cyclicFinalRound_accuracy hA p q j w W (p+8) a n hp hw
    (by omega) ha D z e he hz oldTail tail hgood⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
