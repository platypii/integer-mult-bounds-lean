module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeHaloRunHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryWindowCounters

/-! Compute recovery-window counters from the retained ordinary scalar headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def recoveryWindowFromHeaders (ambient : Bool) : Pr P 117 Q A U :=
  .seq (initializeOriginHeaders haloRunHeaders) (recoveryWindowCounters ambient)

def recoveryWindowFromHeadersCost (ambient : Bool) (W s t B a b : ℕ) : ℕ :=
  (104*W+137)+((s+t+B+a+b)*(4*W+10)+30*W+51)+recoveryWindowCountersCost ambient W s B a b

theorem recoveryWindowFromHeaders_exec {W s t B a b : ℕ} (ambient : Bool)
    (hst : s < t) (has : a ≤ s) (hbs : b ≤ s) (hwide : 8*(t+1)^2+2*B+8 < 2^W)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hs : (S.R 97).length = s) (ht : (S.R 98).length = t)
    (hB : (S.R 100).length = B) (ha : (S.R 101).length = a) (hb : (S.R 103).length = b)
    (hW : (S.R 115).length = W) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 31 → S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ recoveryWindowFromHeadersCost ambient W s t B a b ∧
      Exec body (recoveryWindowFromHeaders ambient) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 108
          (List.replicate (recoveryWindowLower ambient s B a) tick)) 106
            (List.replicate (recoveryWindowUpper ambient s B b) tick))}) := by
  let st := haloRunRawState A s t B a b
  obtain ⟨v₁,S₁,n₁,hu₁,hn₁,he₁,hh₁,hf₁⟩ := initializeHaloRunHeaders_exec (body := body)
    W s t B a b v S hs ht hB ha hb hW h106 hblank
  have hoff (r : Fin 117) (hr : 31 ≤ r.val) : S₁.R r = S.R r :=
    hf₁.2.2.2 r (fun x he => by have hx := originReg_range x; have hv := congrArg Fin.val he; omega)
  have hbound : ∀ r, st.val r < 2^W := by
    have htW : t < 2^W := by nlinarith only [hwide]
    intro r
    simp only [st,haloRunRawState,Function.update_apply]
    split_ifs <;> omega
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := recoveryWindowCounters_exec (body := body) (W := W) (s := s) (B := B) (a := a) (b := b) ambient st
    (by simp [st,haloRunRawState]) (by simp [st,haloRunRawState])
    (by simp [st,haloRunRawState]) (by simp [st,haloRunRawState]) has hbs
    (by nlinarith only [hwide,hst]) hbound rfl v₁ S₁
    (by simpa [hoff 106 (by decide)] using h106) (by simpa [hoff 108 (by decide)] using h108) hh₁
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,by dsimp [recoveryWindowFromHeadersCost]; omega,
    (Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext hf₁.1 hf₁.2.1 hf₁.2.2.1 ?_
  funext r
  by_cases hr : r.val < 31
  · have hr106 : r ≠ (106 : Fin 117) := by intro he; subst r; norm_num at hr
    have hr108 : r ≠ (108 : Fin 117) := by intro he; subst r; norm_num at hr
    simp [hr,hr106,hr108,hblank r hr]
  have hr31 : 31 ≤ r.val := by omega
  by_cases hr108 : r = 108
  · subst r; simp [hr]
  by_cases hr106 : r = 106
  · subst r; simp [hr,hr108]
  simp [hr,hr108,hr106,hoff r hr31]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
