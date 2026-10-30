module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientPaddingData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedPrefixPadding

/-! The executed short-tile padding produces genuine zero coefficient replicas. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem coefficientReplicaPadding_exec {N : ℕ} (c : ℕ)
    (exponent width src totalExponent pad tmp saved : Fin T)
    (hreg : [exponent,width,src,totalExponent,pad,tmp,saved].Nodup)
    (d L w : ℕ) (hpacket : 0 < L*w) (hN : N ≤ (2^d)^c)
    (f : Fin N → Fin (2^d) → Fin L → GaussianInt)
    (v : HS T Q A U) (S : Stacks T A)
    (hd : (S.R exponent).length = d) (hwidth : (S.R width).length = L*w)
    (hsrc : S.R src = cstream A w (replicaKeyWords f))
    (htotal : S.R totalExponent = []) (hpad : S.R pad = [])
    (htmp : S.R tmp = []) (hsaved : S.R saved = []) :
    let V := (2^d)^c*(2^d*(L*w))
    ∃ g : Fin ((2^d)^c) → Fin (2^d) → Fin L → GaussianInt,
      replicaKeyWords g = tilePrefixPad ((2^d)^c*(2^d*L)) 0 (replicaKeyWords f) ∧
      (replicaKeyWords g).drop (((2^d)^c-N)*(2^d*L)) = replicaKeyWords f ∧
      ∃ v' n, v'.user = v.user ∧ n ≤ 29*V+20 ∧
        Exec body (generatedTilePrefixPadding c exponent width src totalExponent pad tmp saved
          (pairSym A false false)) (mk v S) n
          (mk v' {S with R := Function.update S.R src (cstream A w (replicaKeyWords g))}) := by
  dsimp only
  let V := (2^d)^c*(2^d*(L*w))
  have hlen : (S.R src).length = N*(2^d*(L*w)) := by
    simp [hsrc,replicaKeyWords,Nat.mul_assoc]
  have hfit : (S.R src).length ≤ V := by
    rw [hlen]
    exact Nat.mul_le_mul_right (2^d*(L*w)) hN
  obtain ⟨g,hg,hencode,hsuffix⟩ := coefficientPadding_view A w ((2^d)^c) f hN
  obtain ⟨v',n,hu,hn,he⟩ := generatedTilePrefixPadding_exec (body := body) c
    exponent width src totalExponent pad tmp saved hreg (pairSym A false false) d (L*w)
    v S hd hwidth htotal hpad htmp hsaved
  have hword : List.replicate (V-(S.R src).length) (pairSym A false false)++S.R src =
      cstream A w (replicaKeyWords g) := by
    simpa only [tilePrefixPad,hsrc] using hencode.symm
  refine ⟨g,hg,hsuffix,v',n,hu,hn.trans (generatedTilePrefixPaddingCost_le c d (L*w) _ hpacket hfit),?_⟩
  dsimp only [V] at hword
  simpa only [hword] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
