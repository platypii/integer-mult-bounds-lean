module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCouplingOffsetLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCouplingReset

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def packedCouplingOffsetPass {P U : Type} {Q A : ℕ} (negative boundary : Bool) : Pr P 117 Q A U :=
  .seq (packedCouplingOffsetLoop negative boundary) packedCouplingReset

theorem packedCouplingOffsetPass_exec {P U : Type} {Q A V s t band a b i : ℕ} [NeZero s]
    {body : P → Pr P 117 Q A U} (negative boundary : Bool) (value : Fin 117 → ℕ)
    (hs : value 97 = s) (ht : value 98 = t) (hband : value 100 = band)
    (hi : value 107 = i) (hd' : value 105 = 0) (ha : value 101 = a) (hb : value 103 = b)
    (hst : s < t) (hab : a ≤ b) (hbS : b ≤ s) (hfit : i+band*s+band < 2^V)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hbound : ∀ i, value (packedLookupBankSource i) < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A) (hV : (S.R 115).length = V)
    (hmeta : ∀ i, S.R (packedLookupBankSource i) = binSyms V (value (packedLookupBankSource i)))
    (hblank : ∀ r, S.R (originReg r) = []) (w : ℕ) (F : ZMod s → GaussianInt)
    (tail : List (Fin (A+4))) (hwidth : (S.R 94).length = w)
    (hsrc : S.R 92 = cstream A w (packedInterval a (b-a) F)++tail)
    (hlow : ∀ r : Fin 117, r.val < 31 → S.R r = [])
    (h108 : S.R 108 = []) (h109 : S.R 109 = []) (hcount : (S.R 116).length = band)
    (hz : S.R 106 = binSyms V 0) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ band*(14*V+15+(136*V+137+(33*tblC V V+6*(b-a+1)+84*V+76+((b-a)*(12*w+11)+10*w+30)))+3)+2+(6*V+6) ∧
      Exec body (packedCouplingOffsetPass negative boundary) (mk v S) n
        (mk v' {S with R := Function.update (Function.update S.R 110
          (cstream A w (couplingInputOffsetWords negative boundary t band a b i band F)++S.R 110)) 116 []}) := by
  obtain ⟨v₁,n,hu₁,hn,he₁⟩ := packedCouplingOffsetLoop_exec (body := body) negative boundary value
    hs ht hband hi hd' ha hb hst hab hbS hfit hwide hbound v S hV hmeta hblank w F tail hwidth hsrc
    hlow h108 h109 hcount
  let S₁ : Stacks 117 A := {S with R := Function.update (Function.update (Function.update S.R
    105 (binSyms V band)) 110
    (cstream A w (couplingInputOffsetWords negative boundary t band a b i band F)++S.R 110)) 116 []}
  obtain ⟨v₂,hu₂,he₂⟩ := packedCouplingReset_exec (body := body) (V := V) (d := band) v₁ S₁
    (by simp [S₁]) (by simpa [S₁] using hz) (by simpa [S₁] using hlow 0 (by decide))
  have h105 : S.R 105 = binSyms V 0 := by simpa [packedLookupBankSource,hd'] using hmeta 8
  refine ⟨v₂,n+(6*V+6),hu₂.trans hu₁,Nat.add_le_add_right hn _,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext r
  by_cases h1 : r = 105 <;> by_cases h2 : r = 110 <;> by_cases h3 : r = 116 <;>
    simp_all [S₁]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
