module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloRunMaskCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWindowMask
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingSourceMaskHost

/-! Both coupling masks reuse the interval producer; the boundary case clips its complement. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def closedCouplingRunMask (boundary : Bool) : Pr P 117 Q A U :=
  .seq (closedHaloRunMask (pairSym A boundary boundary) (pairSym A (!boundary) (!boundary)))
    (if boundary then windowMask id (fun _ => pairSym A false false) else .act .done)

def closedCouplingRunMaskCost (s t band a b : ℕ) : ℕ :=
  closedHaloRunMaskCost s t band a b+windowMaskCost s a b

theorem closedCouplingRunMaskCost_le (s t band a b : ℕ) :
    closedCouplingRunMaskCost s t band a b ≤
      4000*(s+t+band+a+b+1)*(publicationGeometryWidth t band+4)^2 := by
  have hbase := closedHaloRunMaskCost_le_sharp s t band a b
  let H := s+t+band+a+b+1
  let W := publicationGeometryWidth t band
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hD : 16 ≤ (W+4)^2 := by nlinarith only [Nat.zero_le W,Nat.zero_le (W^2)]
  have hw : windowMaskCost s a b ≤ 14*H+14 := by dsimp [windowMaskCost,H]; omega
  have hm := Nat.mul_le_mul_left H hD
  change closedHaloRunMaskCost s t band a b ≤ 3600*H*(W+4)^2 at hbase
  change closedHaloRunMaskCost s t band a b+windowMaskCost s a b ≤ 4000*H*(W+4)^2
  nlinarith only [hbase,hw,hm,hH]

theorem closedCouplingRunMask_exec (boundary : Bool) {s t band a b : ℕ} [NeZero s]
    (hst : s < t) (has : a ≤ s) (hbs : b ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hs : (S.R 97).length = s) (ht : (S.R 98).length = t)
    (hband : (S.R 100).length = band) (ha : (S.R 101).length = a) (hb : (S.R 103).length = b)
    (h115 : S.R 115 = []) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 31 → S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ closedCouplingRunMaskCost s t band a b ∧
      Exec body (closedCouplingRunMask boundary) (mk v S) n
        (mk v' {S with R := Function.update S.R 109 (couplingSourceMaskSymbols boundary A s t band a b++S.R 109)}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := closedHaloRunMask_exec (body := body) hst has hbs hA
    (pairSym A boundary boundary) (pairSym A (!boundary) (!boundary)) v S
    hs ht hband ha hb h115 h106 h108 hblank
  let xs := (List.range s).map (fun k => if haloInteriorAt s t band a b k then
    pairSym A (!boundary) (!boundary) else pairSym A boundary boundary)
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 109 (xs++S.R 109)}
  cases boundary with
  | false =>
    have hm : xs = couplingSourceMaskSymbols false A s t band a b := by
      dsimp only [xs,couplingSourceMaskSymbols,haloMaskAt]
      apply List.map_congr_left
      intro k hk
      cases haloInteriorAt s t band a b k <;> rfl
    refine ⟨v₁,n₁+1,hu₁,?_,(Exec.seq he₁ (Exec.act .done (mk v₁ S₁))).cast rfl ?_⟩
    · dsimp only [closedCouplingRunMaskCost,windowMaskCost]; omega
    · simp [Action.run,S₁,hm]
  | true =>
    obtain ⟨v₂,hu₂,he₂⟩ := windowMask_exec (body := body) s a b has hbs id (fun _ => pairSym A false false)
      v₁ S₁ xs (S.R 109) (by simpa [S₁] using hs) (by simpa [S₁] using ha)
      (by simpa [S₁] using hb) (by simp [xs]) (by simp [S₁]) (by
        intro k hk
        have hk31 : k.val < 31 := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
        have hk109 : k ≠ (109 : Fin 117) := by intro he; subst k; norm_num at hk31
        simpa [S₁,hk109] using hblank k hk31)
    have hm : windowWord id (fun _ => pairSym A false false) a b xs = couplingSourceMaskSymbols true A s t band a b := by
      rw [show xs = (List.range s).map (fun k => if haloInteriorAt s t band a b k then
        pairSym A false false else pairSym A true true) by rfl,windowWord_map_range]
      apply List.map_congr_left
      intro k hk
      by_cases hw : a ≤ k ∧ k < b <;> cases hi : haloInteriorAt s t band a b k <;>
        simp [couplingSourceMaskSymbols,haloMaskAt,hw,hi]
    refine ⟨v₂,n₁+windowMaskCost s a b,hu₂.trans hu₁,by dsimp [closedCouplingRunMaskCost]; omega,
      (Exec.seq he₁ he₂).cast rfl ?_⟩
    simp [S₁,hm]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
