module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalHaloClassController
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginRelease

/-! Run the existing halo origin/count controller and release its loaded table.
Binary and unary loaders can share this exact publication/restoration law. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def releasedHaloClass : Pr P 117 Q A U := .seq localHaloClassController releaseOriginBank

def releasedHaloClassCost (V s t band a b L : ℕ) : ℕ :=
  ((36*haloPhaseCount s t a b+16)*tblC V V+(haloLengthGroup s t band a b L).length*(8*V+6)+6)+(62*V+63)

theorem releasedHaloClass_exec {V s t band a b L : ℕ}
    (hs : 0 < s) (hst : s < t) (hband : band ≤ s) (hab : a ≤ b) (hb : b ≤ s)
    (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A) (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick)
      (haloClassRawState A s t band a b L)))
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ releasedHaloClassCost V s t band a b L ∧
      Exec body releasedHaloClass (mk v S) m
        (mk v' {S with R := fun k => if k.val < 31 then [] else if k = 109 then
          haloOriginPackets A V s t band a b L++S.R k else if k = 116 then
          List.replicate (haloLengthGroup s t band a b L).length tick else S.R k}) := by
  obtain ⟨v₁,S₁,m₁,st₁,hu₁,hm₁,he₁,hpackets,hcount,hh,hbound,hinp,hout,hleft,hframe⟩ :=
    localHaloClassController_exec (body := body) hs hst hband hab hb hL hLs hwide hA v S hS h104 h106 h116
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := releaseOriginBank_width_exec (body := body) V V le_rfl st₁.val v₁ S₁ hh
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext hinp hout hleft ?_
  funext k
  by_cases hk : k.val < 31
  · simp [hk]
  · have hoff : ∀ r, originReg r ≠ k := by
      intro r he; have hr := originReg_range r; rw [he] at hr; omega
    by_cases h109 : k = 109
    · subst k; simp [hpackets]
    by_cases h116' : k = 116
    · subst k; simp [hcount]
    · simp [hk,h109,h116',hframe k h109 h116' hoff]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
