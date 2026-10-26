module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloMembershipHost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMaskedIndexedWord
public import IntegerMultBounds.MathlibTM2.Mult.ChirpCyclicMath

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

def maskedHaloLookup (boundary : Bool) : Pr P₀ 117 Q A U :=
  .seq (haloMembershipHost boundary) (maskedIndexedWord 109 108 94 92 110 3 0 1 2 4 5)

def maskedHaloLookupCost (V w k : ℕ) : ℕ :=
  25*tblC V V+62*V+k*(12*w+9)+10*w+93

theorem maskedHaloLookup_exec {V w s t band a b k : ℕ} [NeZero s]
    (boundary : Bool) (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band) (hk : st.val 3 = k)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hacc : st.acc = [])
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hkS : k < s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hbound : ∀ r, st.val r < 2^V)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A) (h109 : S.R 109 = [])
    (hindex : (S.R 108).length = k) (hwidth : (S.R 94).length = w)
    (hsrc : S.R 92 = cstream A w (chirpLine s C)++tail)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    let T := if boundary then haloBoundary s t band a b else haloInterior s t band a b
    let z := if (k : ZMod s) ∈ T then C (k : ZMod s) else 0
    ∃ v' m, v'.user = v.user ∧ m ≤ maskedHaloLookupCost V w k ∧
      Exec body (maskedHaloLookup boundary) (mk v S) m
        (mk v' {S with R := (fun r => if r.val < 31 then [] else if r = 110 then
          csyms A w z++S.R 110 else S.R r)}) := by
  dsimp only
  let flag := haloMaskAt boundary s t band a b k
  obtain ⟨v₁,m₁,hu₁,_,hm₁,he₁⟩ := haloMembershipHost_exec (body := body) boundary st
    hs ht hband hk ha hb hacc (NeZero.pos s) hst haS hbS hbandS hwide hbound v S h109 hS
  let S₁ : Stacks 117 A := {S with R := (fun r => if r.val < 31 then [] else if r = 109 then
    (if flag then [tick] else []) else S.R r)}
  have hidx : k < (chirpLine s C).length := by simpa using hkS
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := maskedIndexedWord_exec (body := body)
    (mask := 109) (index := 108) (width := 94) (src := 92) (dst := 110) (skip := 3)
    (savedSkip := 0) (saved := 1) (tmp := 2) (work₁ := 4) (work₂ := 5) (by decide)
    flag w k (chirpLine s C) hidx tail v₁ S₁ (by simp [S₁])
    (by simpa [S₁] using hindex) (by simpa [S₁] using hwidth) (by simpa [S₁] using hsrc) (by
      intro r hr
      have hlo : r.val < 31 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp [S₁,hlo])
  have hflag := haloMaskAt_spec boundary hst band a b k hbS hkS
  have hword : (if flag then (chirpLine s C)[k] else 0) =
      (if (k : ZMod s) ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
        then C (k : ZMod s) else 0) := by
    simp only [flag,chirpLine,List.getElem_map,List.getElem_range,hflag]
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
  · dsimp only [maskedHaloLookupCost]
    omega
  · apply congrArg (mk v₂)
    refine Stacks.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · funext r
      by_cases hlo : r.val < 31
      · have h109' : r ≠ 109 := by intro he; subst r; norm_num at hlo
        have h110 : r ≠ 110 := by intro he; subst r; norm_num at hlo
        simp [S₁,hlo,h109',h110]
      by_cases h109' : r = 109
      · subst r; simp [h109]
      by_cases h110 : r = 110
      · subst r; simp [S₁,hword]
      simp [S₁,hlo,h109',h110]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
