module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConditionalHaloGroupPreparation
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedControlledHaloClass

/-! One runtime-selected class operation. The computed row count chooses the
actual numerical continuation or the verified empty exit; origins are reused
and the same final register/ambient-error contract covers both branches. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def conditionalHaloClass (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq conditionalHaloGroupPreparation (.cond (·.flag) (protectedControlledHaloClass hR hQ) (.act .done))

def conditionalHaloClassCost (p l L s t u target rhsExp a b : ℕ) : ℕ :=
  let q := executionPrecision p l target rhsExp
  let N := executionStagePrecision p l target rhsExp+1
  let P := 2^15*p
  let band := PhaseCellBand.width p u
  let B := (haloLengthGroup s t band a b L).length
  conditionalHaloGroupPreparationCost P N q l s t u band a b L+
    (if 0 < B then protectedControlledHaloClassCost p l B L s t u target rhsExp a b else 1)+1

theorem conditionalHaloClass_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (v : HS 144 Q A U) (S : Stacks 144 A) (borrowed E outputTail : List (Fin (A+4)))
    (hE : E.length = s*executionWidth p l target rhsExp) (hdst : S.R 132 = E++outputTail)
    (hmasters : ∀ r ∈ groupHeaderCopies, (S.R r.1).length =
      groupHeaderValue (2^15*p) (executionStagePrecision p l target rhsExp+1)
        (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) L r.1)
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hleft : ∀ k : Fin 144, k.val < 117 → S.L k = [])
    (hblank : ∀ k : Fin 144, k.val < 117 → k ≠ 93 → k ≠ 110 → S.R k = [])
    (hsrc : S.R 110 = cstream A (executionWidth p l target rhsExp) (chirpLine s C) ++ borrowed)
    (h129 : S.R 129 = []) (h133 : S.R 133 = [])
    (hwidth : (S.R 130).length = executionWidth p l target rhsExp)
    (hfresh : ∀ k ∈ [(131 : Fin 144),134,135,136,137,140], S.R k = []) :
    let B := (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length
    let lo := haloGroupOrigin s t (PhaseCellBand.width p u) a b L
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    ∃ v' S' n, ∃ ys : List (Fin (A+4)), v'.user = v.user ∧
      n ≤ conditionalHaloClassCost p l L s t u target rhsExp a b ∧
      Exec (embTab groupReg body) (conditionalHaloClass hR hQ) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ys.length = B*L*w ∧
      S'.R = publishedClassR S.R (scatterRows (L*w) E (ys++S.R 93)
        (haloScatterGaps s t (PhaseCellBand.width p u) a b L w)++outputTail) ∧
      ∀ n : Fin B, PhaseCellInterface.ErrorOn (publishedCellCore (lo n) L)
        (publishedCellRead q w (0 : ZMod s) (S'.R 132)) x (1/(2 : ℝ)^target) := by
  dsimp only
  let P := 2^15*p
  let N := executionStagePrecision p l target rhsExp+1
  let band := PhaseCellBand.width p u
  let B := (haloLengthGroup s t band a b L).length
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  have hw : w = 2*q+8 := by dsimp [q,w,executionWidth,executionPrecision]; omega
  obtain ⟨v₁,S₁,n₁,hu₁,hflag₁,hn₁,he₁,hi₁,ho₁,hl₁,hpost₁⟩ := conditionalHaloGroupPreparation_exec (body := body)
    P N q l s t u band a b L (by dsimp [P]; omega) (Nat.pos_of_ne_zero (NeZero.ne s)) hst hu
    hband has hbs hL hLs (by omega) C v S borrowed hmasters haMaster hbMaster hleft hblank (by simpa only [← hw] using hsrc) h133
  by_cases hB : 0 < (haloLengthGroup s t band a b L).length
  · have hpost : embStk groupReg S₁ = controlledHaloGroupInputBank P N q l t u band a b L C borrowed (S.R 93) S.inp S.out ∧
        ∀ k : Fin 144, 117 ≤ k.val → S₁.R k = S.R k := by
      simpa only [ite_eq_left hB] using hpost₁
    obtain ⟨hbank₁,hR₁⟩ := hpost
    have h93 : S₁.R 93 = S.R 93 := by
      have hh := congrArg (fun B : Stacks 117 A => B.R 93) hbank₁
      simpa [embStk,groupReg,controlledHaloGroupInputBank,haloOriginAndGatherControlsR,haloClassControlsR,
        haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank] using hh
    have h110 : S₁.R 110 = S.R 110 := by
      have hh := congrArg (fun B : Stacks 117 A => B.R 110) hbank₁
      have hr : S₁.R 110 = cstream A (2*q+8) (chirpLine s C)++borrowed := by
        simpa [embStk,groupReg,controlledHaloGroupInputBank,haloOriginAndGatherControlsR,haloClassControlsR,
          haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank] using hh
      exact hr.trans (by simpa only [← hw] using hsrc.symm)
    have h128 : (S₁.R 128).length = L := by
      rw [hR₁ 128 (by decide)]
      have hh := hmasters (128,102) (by simp [groupHeaderCopies])
      simpa [groupHeaderValue] using hh
    obtain ⟨v₂,S₂,n₂,ys,hu₂,hn₂,he₂,hi₂,ho₂,hl₂,hylen,hframe,herror⟩ :=
      protectedControlledHaloClass_spec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget hB hpad C hC x hx
        v₁ S₁ borrowed E outputTail hE (by rw [hR₁ 132 (by decide)]; exact hdst)
        (by simpa only [hi₁,ho₁,h93] using hbank₁) h128
        (by rw [hR₁ 129 (by decide)]; exact h129) (by rw [hR₁ 133 (by decide)]; exact h133)
        (by rw [hR₁ 130 (by decide)]; exact hwidth) (by
          intro k hk
          have hkhi : 117 ≤ k.val := by
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
            rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
          rw [hR₁ k hkhi]
          exact hfresh k hk)
    have hrestored : restoredGroupR S₁.R = S.R := restoredGroupR_frame S₁.R S.R h93 h110 hR₁ hblank
    have hcond : Exec (embTab groupReg body) (.cond (·.flag) (protectedControlledHaloClass hR hQ) (.act .done))
        (mk v₁ S₁) (n₂+1) (mk v₂ S₂) := by
      apply Exec.cond_true ?_ he₂
      change v₁.flag = true
      simpa only [hflag₁,decide_eq_true_eq] using hB
    refine ⟨v₂,S₂,n₁+(n₂+1),ys,hu₂.trans hu₁,?_,Exec.seq he₁ hcond,
      hi₂.trans hi₁,ho₂.trans ho₁,hl₂.trans hl₁,hylen,?_,herror⟩
    · dsimp only [conditionalHaloClassCost]
      dsimp only [P,N,q,w,band,B] at *
      rw [ite_eq_left hB]
      omega
    · simpa only [hrestored,h93] using hframe
  · have hBzero : (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length = 0 := by
      change (haloLengthGroup s t band a b L).length = 0
      omega
    have hgaps : haloScatterGaps s t band a b L w = [] := List.eq_nil_of_length_eq_zero (by
      rw [haloScatterGaps_length]
      exact hBzero)
    have hr : S₁.R = Function.update S.R 128 [] := by simpa only [ite_eq_right hB] using hpost₁
    have hcond : Exec (embTab groupReg body) (.cond (·.flag) (protectedControlledHaloClass hR hQ) (.act .done))
        (mk v₁ S₁) 2 (mk v₁ S₁) := by
      refine Exec.cond_false ?_ ?_
      · change v₁.flag = false
        simpa only [hflag₁,decide_eq_false_iff_not] using hB
      · simpa only [Action.run] using Exec.act (body := embTab groupReg body) .done (mk v₁ S₁)
    refine ⟨v₁,S₁,n₁+2,[],hu₁,?_,Exec.seq he₁ hcond,hi₁,ho₁,hl₁,?_,?_,?_⟩
    · dsimp only [conditionalHaloClassCost]
      rw [ite_eq_right hB]
      dsimp only [P,N,q,band] at *
      omega
    · simp [hBzero]
    · change S₁.R = publishedClassR S.R (scatterRows (L*w) E ([]++S.R 93)
        (haloScatterGaps s t band a b L w)++outputTail)
      rw [hgaps,scatterRows_nil,← hdst,publishedClassR_empty S.R h129 (hfresh 140 (by simp))]
      exact hr
    · intro n
      have hn := n.isLt
      omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
