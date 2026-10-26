module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMaskedHaloLookup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightStream

/-! Compute original halo membership, release its table, and gather one masked
ambient input word. The raw source and all outside registers restore. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem maskedHaloLookup_spec {V w q inputExp s t band a b k : ℕ} [NeZero s]
    (boundary : Bool) (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band) (hk : st.val 3 = k)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hacc : st.acc = [])
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hkS : k < s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hbound : ∀ r, st.val r < 2^V)
    (hA : 96 ≤ A) (hw : q+inputExp+2 ≤ w)
    (C : ZMod s → GaussianInt) (x : ZMod s → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hC : ∀ j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b),
      ‖value q (C j)‖ ≤ (2 : ℝ)^inputExp)
    (hx : ∀ j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b),
      |(value q (C j)).re-x j| ≤ ε)
    (tail : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A) (h109 : S.R 109 = [])
    (hindex : (S.R 108).length = k) (hwidth : (S.R 94).length = w)
    (hsrc : S.R 92 = cstream A w (chirpLine s C)++tail)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    let T := if boundary then haloBoundary s t band a b else haloInterior s t band a b
    let z := if (k : ZMod s) ∈ T then C (k : ZMod s) else 0
    ∃ v' m, v'.user = v.user ∧ m ≤ maskedHaloLookupCost V w k ∧
      Exec body (maskedHaloLookup boundary) (mk v S) m
        (mk v' {S with R := (fun r => if r.val < 31 then [] else if r = 110 then
          csyms A w z++S.R 110 else S.R r)}) ∧
      |(value q (decodeWord ((csyms A w z++S.R 110).take w))).re-
        (if (k : ZMod s) ∈ T then x (k : ZMod s) else 0)| ≤ ε := by
  dsimp only
  let T := if boundary then haloBoundary s t band a b else haloInterior s t band a b
  let z := if (k : ZMod s) ∈ T then C (k : ZMod s) else 0
  obtain ⟨v',m,hu,hm,he⟩ := maskedHaloLookup_exec (body := body) boundary st
    hs ht hband hk ha hb hacc hst haS hbS hbandS hkS hwide hbound C tail v S h109 hindex hwidth hsrc hS
  refine ⟨v',m,hu,hm,he,?_⟩
  have hfit : Fits w z := by
    by_cases hmem : (k : ZMod s) ∈ T
    · simpa only [z,if_pos hmem] using fits_of_value_power hw _ (hC _ hmem)
    · simp only [z,if_neg hmem]
      constructor <;> simp
  have hlen : (csyms A w z).length = w := by simp [csyms]
  have hword : (csyms A w z++S.R 110).take w = csyms A w z := by
    simp only [List.take_append,hlen,Nat.sub_self,List.take_zero,List.append_nil]
    simpa only [hlen] using (show (csyms A w z).take (csyms A w z).length = csyms A w z from List.take_length)
  rw [hword,decodeWord_of_fits (by omega) (by omega) z hfit]
  change |(value q z).re-(if (k : ZMod s) ∈ T then x (k : ZMod s) else 0)| ≤ ε
  by_cases hmem : (k : ZMod s) ∈ T
  · simpa only [z,if_pos hmem] using hx (k : ZMod s) hmem
  · simpa [z,hmem,value] using hε

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
