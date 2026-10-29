module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCouplingAdvance
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCouplingLookup

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def packedCouplingOffsetStep {P U : Type} {Q A : ℕ} (negative boundary : Bool) : Pr P 117 Q A U :=
  .seq packedCouplingAdvance (.seq loadPackedLookupBank
    (.seq (packedLookupCountersFor (guardedPackedCouplingLookupCode negative boundary)) packedHaloRead))

theorem packedCouplingOffsetStep_exec {P U : Type} {Q A V s t band a b i d : ℕ} [NeZero s]
    {body : P → Pr P 117 Q A U} (negative boundary : Bool) (value : Fin 117 → ℕ)
    (hs : value 97 = s) (ht : value 98 = t) (hband : value 100 = band)
    (hi : value 107 = i) (hd' : value 105 = d) (ha : value 101 = a) (hb : value 103 = b)
    (hst : s < t) (hab : a ≤ b) (hbS : b ≤ s) (hd : d+1 ≤ band) (hfit : i+band*s+(d+1) < 2^V)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hbound : ∀ i, value (packedLookupBankSource i) < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A) (hV : (S.R 115).length = V)
    (hmeta : ∀ i, S.R (packedLookupBankSource i) = binSyms V (value (packedLookupBankSource i)))
    (hblank : ∀ r, S.R (originReg r) = []) (w : ℕ) (F : ZMod s → GaussianInt)
    (tail : List (Fin (A+4))) (hwidth : (S.R 94).length = w)
    (hsrc : S.R 92 = cstream A w (packedInterval a (b-a) F)++tail)
    (hlow : ∀ r : Fin 117, r.val < 31 → S.R r = [])
    (h108 : S.R 108 = []) (h109 : S.R 109 = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 14*V+15+(136*V+137+(33*tblC V V+6*(b-a+1)+84*V+76+((b-a)*(12*w+11)+10*w+30))) ∧
      Exec body (packedCouplingOffsetStep negative boundary) (mk v S) n
        (mk v' {S with R := (fun r => if r.val < 31 then [] else if r = 110 then
          csyms A w (maskedCouplingInputWord negative boundary t band a b i (d+1) F)++S.R 110
          else if r = 105 then binSyms V (d+1) else S.R r)}) := by
  have h105 : S.R 105 = binSyms V d := by
    simpa [packedLookupBankSource,hd'] using hmeta 8
  obtain ⟨v₁,hu₁,he₁⟩ := packedCouplingAdvance_exec (body := body) v S hV h105 hlow
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 105 (binSyms V (d+1))}
  let value₁ := Function.update value 105 (d+1)
  have hbound₁ : ∀ j, value₁ (packedLookupBankSource j) < 2^V := by
    intro j
    by_cases hj : packedLookupBankSource j = 105
    · simp only [value₁,hj,Function.update_self]; omega
    · simpa only [value₁,Function.update_of_ne hj] using hbound j
  obtain ⟨v₂,n,hu₂,hn,he₂⟩ := binaryGuardedPackedCouplingLookup_state_exec
    (body := body) negative boundary value₁
    (by simpa [value₁] using hs) (by simpa [value₁] using ht)
    (by simpa [value₁] using hband) (by simpa [value₁] using hi) (by simp [value₁])
    (by simpa [value₁] using ha) (by simpa [value₁] using hb)
    hst hab hbS hd hfit hwide hbound₁ v₁ S₁
    (by simpa [S₁] using hV) (packedCouplingAdvance_metadata S value hmeta)
    (by intro r; have hr := originReg_range r
        have hne : originReg r ≠ 105 := by intro he; rw [he] at hr; omega
        simpa only [S₁,Function.update_of_ne hne] using hblank r)
    w F tail (by simpa [S₁] using hwidth) (by simpa [S₁] using hsrc)
    (by simpa [S₁] using h108) (by simpa [S₁] using h109)
  refine ⟨v₂,14*V+15+n,hu₂.trans hu₁,Nat.add_le_add_left hn _,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext r
  by_cases h110 : r = 110
  · subst r; simp [S₁]
  · by_cases h105 : r = 105
    · subst r; simp [S₁]
    · simp [S₁,h110,h105]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
