module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryGuardMaskHost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloLookupFromHeaders

/-! Generate either complete halo mask from retained unary geometry headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def recoveryGuardMaskFromHeaders (boundary : Bool) : Pr P₀ 117 Q A U :=
  .seq (initializeOriginHeaders haloLookupHeaders) (recoveryGuardMaskHost boundary)

def recoveryGuardMaskFromHeadersCost (V s t band a b : ℕ) : ℕ :=
  (104*V+137)+((s+t+band+a+b)*(4*V+10)+36*V+61)+recoveryGuardMaskHostCost V s

theorem recoveryGuardMaskFromHeaders_exec (boundary : Bool) {V s t band a b : ℕ} [NeZero s]
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (hbandSrc : (S.R 100).length = band) (haSrc : (S.R 101).length = a)
    (hbSrc : (S.R 103).length = b) (hindex : S.R 108 = [])
    (hVsrc : (S.R 115).length = V) (h106 : S.R 106 = [])
    (hblank : ∀ r : Fin 117, r.val < 31 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ recoveryGuardMaskFromHeadersCost V s t band a b ∧
      Exec body (recoveryGuardMaskFromHeaders boundary) (mk v S) m
        (mk v' {S with R := Function.update S.R 109 (recoveryGuardMaskSymbols boundary A s t band a b++S.R 109)}) := by
  let initial : TblSt 16 A := ⟨fun _ => 0,[]⟩
  let st := haloLookupHeaderState (A := A) s t band a b 0
  let value := fun r : Fin 117 => (S.R r).length
  have hsep : ∀ r ∈ haloLookupHeaders, ∀ x, originReg x ≠ r.1 := by
    intro r hr x he
    have hv : 31 ≤ r.1.val := by
      simp only [haloLookupHeaders,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hx := originReg_range x
    have hh := congrArg Fin.val he
    omega
  obtain ⟨v₁,S₁,n₁,hu₁,hn₁,he₁,hh₁,hf₁⟩ := initializeOriginHeaders_exec (body := body)
    haloLookupHeaders hsep V value v S (by intros; rfl) hVsrc h106 hblank
  have hstate : loadedOriginState value haloLookupHeaders initial = st := by
    simp [loadedOriginState,haloLookupHeaders,initial,st,haloLookupHeaderState,
      value,hsSrc,htSrc,hbandSrc,hindex,haSrc,hbSrc]
  rw [hstate] at hh₁
  have hoff₁ (r : Fin 117) (hr : 31 ≤ r.val) : S₁.R r = S.R r :=
    hf₁.2.2.2 r (fun x he => by have hx := originReg_range x; have hv := congrArg Fin.val he; omega)
  have hstV : ∀ r, st.val r < 2^V := by
    have htV : t < 2^V := by nlinarith [hwide, Nat.zero_le (t*t)]
    intro r
    simp only [st,haloLookupHeaderState,Function.update_apply]
    split_ifs <;> omega
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := recoveryGuardMaskHost_exec boundary (body := body) (V := V)
    (s := s) (t := t) (band := band) (a := a) (b := b) st
    (by simp [st,haloLookupHeaderState]) (by simp [st,haloLookupHeaderState])
    (by simp [st,haloLookupHeaderState]) (by simp [st,haloLookupHeaderState])
    (by simp [st,haloLookupHeaderState]) rfl (NeZero.pos s) hst haS hbS hwide hstV v₁ S₁ hh₁
  have hcost : loadOriginListCost V value haloLookupHeaders =
      (s+t+band+a+b)*(4*V+10)+36*V+61 := by
    simp [loadOriginListCost,haloLookupHeaders,value,hsSrc,htSrc,hbandSrc,hindex,haSrc,hbSrc]
    ring
  rw [hcost] at hn₁
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
  · dsimp only [recoveryGuardMaskFromHeadersCost]
    omega
  · apply congrArg (mk v₂)
    refine Stacks.ext hf₁.1 hf₁.2.1 hf₁.2.2.1 ?_
    funext r
    by_cases hr : r.val < 31
    · have hr109 : r ≠ 109 := by intro he; subst r; norm_num at hr
      simp [hr,hr109,hblank r hr]
    · have hv : 31 ≤ r.val := by omega
      by_cases hr109 : r = 109
      · subst r; simp [hoff₁ 109 (by decide)]
      · simp [hr,hr109,hoff₁ r hv]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
