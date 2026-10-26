module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMaskedHaloLookup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeOriginHeaders

/-! Load ordinary halo geometry, execute the masked lookup, and release its table. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def haloLookupHeaders : List (Fin 117 × Fin 16) :=
  [(97,0),(98,1),(100,2),(108,3),(101,4),(103,5)]

def haloLookupHeaderState (s t band a b k : ℕ) : TblSt 16 A :=
  ⟨Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (fun _ => 0) 0 s) 1 t) 2 band) 3 k) 4 a) 5 b,[]⟩

def haloLookupFromHeaders (boundary : Bool) : Pr P₀ 117 Q A U :=
  .seq (initializeOriginHeaders haloLookupHeaders) (maskedHaloLookup boundary)

def haloLookupFromHeadersCost (V w s t band a b k : ℕ) : ℕ :=
  (104*V+137)+((s+t+band+k+a+b)*(4*V+10)+36*V+61)+maskedHaloLookupCost V w k

theorem haloLookupFromHeaders_exec {V w s t band a b k : ℕ} [NeZero s]
    (boundary : Bool) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hkS : k < s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (hbandSrc : (S.R 100).length = band) (hkSrc : (S.R 108).length = k)
    (haSrc : (S.R 101).length = a) (hbSrc : (S.R 103).length = b)
    (hVsrc : (S.R 115).length = V) (hwsrc : (S.R 94).length = w)
    (h109 : S.R 109 = []) (h106 : S.R 106 = [])
    (hblank : ∀ r : Fin 117, r.val < 31 → S.R r = [])
    (hsrc : S.R 92 = cstream A w (chirpLine s C)++tail) :
    let T := if boundary then haloBoundary s t band a b else haloInterior s t band a b
    let z := if (k : ZMod s) ∈ T then C (k : ZMod s) else 0
    ∃ v' m, v'.user = v.user ∧ m ≤ haloLookupFromHeadersCost V w s t band a b k ∧
      Exec body (haloLookupFromHeaders boundary) (mk v S) m
        (mk v' {S with R := Function.update S.R 110 (csyms A w z++S.R 110)}) := by
  dsimp only
  let initial : TblSt 16 A := ⟨fun _ => 0,[]⟩
  let st := haloLookupHeaderState (A := A) s t band a b k
  let value := fun r : Fin 117 => (S.R r).length
  have hsep : ∀ r ∈ haloLookupHeaders, ∀ x, originReg x ≠ r.1 := by
    intro r hr x he
    have hv : 31 ≤ r.1.val := by
      simp only [haloLookupHeaders,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hx := originReg_range x
    have hh := congrArg Fin.val he
    omega
  obtain ⟨v₂,S₂,m₂,hu₂,hm₂,he₂,hh₂,hf₂⟩ := initializeOriginHeaders_exec (body := body)
    haloLookupHeaders hsep V value v S (by intros; rfl) hVsrc h106 hblank
  have hstate : loadedOriginState value haloLookupHeaders initial = st := by
    simp [loadedOriginState,haloLookupHeaders,initial,st,haloLookupHeaderState,
      value,hsSrc,htSrc,hbandSrc,hkSrc,haSrc,hbSrc]
  rw [hstate] at hh₂
  have hoff₂ (r : Fin 117) (hr : 31 ≤ r.val) : S₂.R r = S.R r :=
    hf₂.2.2.2 r (fun x he => by have hx := originReg_range x; have hv := congrArg Fin.val he; omega)
  have hstV : ∀ r, st.val r < 2^V := by
    have htV : t < 2^V := by nlinarith only [hwide]
    intro r
    simp only [st,haloLookupHeaderState,Function.update_apply]
    split_ifs <;> omega
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := maskedHaloLookup_exec (body := body) (V := V) (w := w) (s := s) (t := t)
    (band := band) (a := a) (b := b) (k := k) boundary st
    (by simp [st,haloLookupHeaderState])
    (by simp [st,haloLookupHeaderState])
    (by simp [st,haloLookupHeaderState])
    (by simp [st,haloLookupHeaderState])
    (by simp [st,haloLookupHeaderState])
    (by simp [st,haloLookupHeaderState])
    rfl hst haS hbS hbandS hkS hwide hstV C tail v₂ S₂
    (by rw [hoff₂ 109 (by decide)]; exact h109)
    (by rw [hoff₂ 108 (by decide)]; exact hkSrc)
    (by rw [hoff₂ 94 (by decide)]; exact hwsrc)
    (by rw [hoff₂ 92 (by decide)]; exact hsrc) hh₂
  have hcost : loadOriginListCost V value haloLookupHeaders =
      (s+t+band+k+a+b)*(4*V+10)+36*V+61 := by
    simp [loadOriginListCost,haloLookupHeaders,value,hsSrc,htSrc,hbandSrc,hkSrc,haSrc,hbSrc]
    ring
  rw [hcost] at hm₂
  refine ⟨v₃,m₂+m₃,hu₃.trans hu₂,?_,(Exec.seq he₂ he₃).cast rfl ?_⟩
  · dsimp only [haloLookupFromHeadersCost]
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext hf₂.1 hf₂.2.1 hf₂.2.2.1 ?_
    funext r
    by_cases hr : r.val < 31
    · have hr110 : r ≠ 110 := by intro he; subst r; norm_num at hr
      simp [hr,hr110,hblank r hr]
    · have hv : 31 ≤ r.val := by omega
      by_cases hr110 : r = 110
      · subst r; simp [hoff₂ 110 (by decide)]
      · simp [hr,hr110,hoff₂ r hv]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
