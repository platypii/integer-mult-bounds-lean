module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedPrefixPadding
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTilePaddingData

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Layer

/-- Pad a short owned replica tile to the exact router capacity. The returned
bit-plane arrays are derived from actual generated data, and their real suffix
is exactly the original packed payload. No routing-format witness is supplied. -/
theorem generatedReplicaTilePadding_exec {T Q A N : ℕ} {P U : Type} {body : P → Pr P T Q A U}
    (c : ℕ) (exponent width src totalExponent pad tmp saved : Fin T)
    (hreg : [exponent,width,src,totalExponent,pad,tmp,saved].Nodup)
    (d w : ℕ) (hw : 0 < w) (hN : N ≤ (2^d)^c)
    (realBits imagBits : Fin N → Fin (2^d) → Fin w → Bool)
    (v : HS T Q A U) (S : Stacks T A)
    (hd : (S.R exponent).length = d) (hwidth : (S.R width).length = w)
    (hsrc : S.R src = replicaKeyWords (fun r k b => pairSym A (realBits r k b) (imagBits r k b)))
    (htotal : S.R totalExponent = []) (hpad : S.R pad = []) (htmp : S.R tmp = []) (hsaved : S.R saved = []) :
    let V := (2^d)^c*(2^d*w)
    ∃ (r i : Fin ((2^d)^c) → Fin (2^d) → Fin w → Bool), ∃ v' n,
      v'.user = v.user ∧ n ≤ 29*V+20 ∧
      Exec body (generatedTilePrefixPadding c exponent width src totalExponent pad tmp saved (pairSym A false false))
        (mk v S) n (mk v' {S with R := (Function.update S.R src
          (replicaKeyWords (fun a k b => pairSym A (r a k b) (i a k b))))}) ∧
      (replicaKeyWords (fun a k b => pairSym A (r a k b) (i a k b))).drop
        (((2^d)^c-N)*(2^d*w)) = S.R src := by
  dsimp only
  let V := (2^d)^c*(2^d*w)
  have hlength : (S.R src).length = N*(2^d*w) := by simp [hsrc,replicaKeyWords]
  have hfit : (S.R src).length ≤ V := by
    rw [hlength]
    exact Nat.mul_le_mul_right (2^d*w) hN
  obtain ⟨v',n,hu,hn,he⟩ := generatedTilePrefixPadding_exec (body := body) c exponent width src totalExponent pad tmp saved
    hreg (pairSym A false false) d w v S hd hwidth htotal hpad htmp hsaved
  obtain ⟨r,i,hview⟩ := tilePrefixPad_pair_view ((2^d)^c) (pairSym A) realBits imagBits hN
  have hword : List.replicate (V-(S.R src).length) (pairSym A false false)++S.R src =
      replicaKeyWords (fun a k b => pairSym A (r a k b) (i a k b)) := by
    rw [hsrc]
    exact hview
  have hmissing : V-(S.R src).length = ((2^d)^c-N)*(2^d*w) := by
    rw [hlength, Nat.sub_mul]
  refine ⟨r,i,v',n,hu,hn.trans (generatedTilePrefixPaddingCost_le c d w _ hw hfit),?_,?_⟩
  · simpa only [←hword] using he
  · rw [←hmissing,←hword]
    exact tilePrefixPad_drop V (pairSym A false false) (S.R src)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
