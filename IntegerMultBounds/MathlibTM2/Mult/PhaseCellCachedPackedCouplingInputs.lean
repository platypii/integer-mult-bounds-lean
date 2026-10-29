module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratePackedCouplingInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedCouplingWorkspace

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def cachedPackedCouplingInputs {P U : Type} {Q A : ℕ} (boundary : Bool) : Pr P 118 Q A U :=
  embProg cachedCouplingLookupReg Empty.elim (generatePackedCouplingInputs (P := Empty) boundary)

theorem cachedPackedCouplingInputs_exec {P U : Type} {Q A V s t band a b i : ℕ} [NeZero s]
    {body : P → Pr P 118 Q A U} (boundary : Bool) (value : Fin 117 → ℕ)
    (hs : value 97 = s) (ht : value 98 = t) (hband : value 100 = band)
    (hi : value 107 = i) (hd' : value 105 = 0) (ha : value 101 = a) (hb : value 103 = b)
    (hst : s < t) (hab : a ≤ b) (hbS : b ≤ s) (hfit : i+band*s+band < 2^V)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hbound : ∀ i, value (packedLookupBankSource i) < 2^V)
    (v : HS 118 Q A U) (S : Stacks 118 A) (hV : ((embStk cachedCouplingLookupReg S).R 115).length = V)
    (hmeta : ∀ i, (embStk cachedCouplingLookupReg S).R (packedLookupBankSource i) = binSyms V (value (packedLookupBankSource i)))
    (hblank : ∀ r, (embStk cachedCouplingLookupReg S).R (originReg r) = []) (w : ℕ) (F : ZMod s → GaussianInt)
    (tail : List (Fin (A+4))) (hwidth : ((embStk cachedCouplingLookupReg S).R 94).length = w)
    (hsrc : (embStk cachedCouplingLookupReg S).R 92 = cstream A w (packedInterval a (b-a) F)++tail)
    (hlow : ∀ r : Fin 117, r.val < 31 → (embStk cachedCouplingLookupReg S).R r = [])
    (h108 : (embStk cachedCouplingLookupReg S).R 108 = []) (h109 : (embStk cachedCouplingLookupReg S).R 109 = []) (h116 : (embStk cachedCouplingLookupReg S).R 116 = [])
    (hz : (embStk cachedCouplingLookupReg S).R 106 = binSyms V 0) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (136*V+137+(33*tblC V V+6*(b-a+1)+84*V+76+((b-a)*(12*w+11)+10*w+30)))+2*(6*band+11*V+6+(band*(14*V+15+(136*V+137+(33*tblC V V+6*(b-a+1)+84*V+76+((b-a)*(12*w+11)+10*w+30)))+3)+2+(6*V+6))) ∧
      Exec body (cachedPackedCouplingInputs boundary) (mk v S) n
        (mk v' {S with R := (Function.update S.R 110
          (cstream A w (couplingInputWords boundary t band a b i F)++S.R 110))}) := by
  obtain ⟨v₁,n,hu₁,hn,he⟩ := generatePackedCouplingInputs_exec
    (body := fun p : Empty => nomatch p) boundary value hs ht hband hi hd' ha hb hst hab hbS hfit
    hwide hbound (embDn cachedCouplingLookupReg v) (embStk cachedCouplingLookupReg S)
    hV hmeta hblank w F tail hwidth hsrc hlow h108 h109 h116 hz
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    cachedCouplingLookupReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,n,hu₂.trans hu₁,hn,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  rw [embOvr_updR cachedCouplingLookupReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
