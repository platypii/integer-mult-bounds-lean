module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConditionalHaloClass

/-! One generated-key iteration body: decode its ordinary length header,
execute the runtime-selected class and preserve the remaining key suffix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def processHaloLengthKey (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq takeOuterLengthKey (conditionalHaloClass hR hQ)

theorem processHaloLengthKey_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp V a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (v : HS 144 Q A U) (S : Stacks 144 A) (borrowed E outputTail keyTail : List (Fin (A+4)))
    (hkey : L < 2^V) (hV : (S.R 125).length = V) (hkeys : S.R 126 = binSyms V L++keyTail)
    (hE : E.length = s*executionWidth p l target rhsExp) (hdst : S.R 132 = E++outputTail)
    (hmasters : ∀ r ∈ groupHeaderCopies, (S.R r.1).length =
      groupHeaderValue (2^15*p) (executionStagePrecision p l target rhsExp+1)
        (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) 0 r.1)
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
      n ≤ (6*L+19*V+14)+conditionalHaloClassCost p l L s t u target rhsExp a b ∧
      Exec (embTab groupReg body) (processHaloLengthKey hR hQ) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ys.length = B*L*w ∧
      S'.R = publishedClassR (Function.update S.R 126 keyTail) (scatterRows (L*w) E (ys++S.R 93)
        (haloScatterGaps s t (PhaseCellBand.width p u) a b L w)++outputTail) ∧
      ∀ n : Fin B, PhaseCellInterface.ErrorOn (publishedCellCore (lo n) L)
        (publishedCellRead q w (0 : ZMod s) (S'.R 132)) x (1/(2 : ℝ)^target) := by
  dsimp only
  have h128 : S.R 128 = [] := by
    have hh := hmasters (128,102) (by simp [groupHeaderCopies])
    apply List.eq_nil_of_length_eq_zero
    simpa [groupHeaderValue] using hh
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := takeOuterLengthKey_exec (body := embTab groupReg body)
    V L hkey keyTail v S hV hkeys (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      · exact h128
      all_goals exact hfresh _ (by simp))
  let S₁ : Stacks 144 A := { S with R := (Function.update (Function.update S.R 126 keyTail) 128 (List.replicate L tick)) }
  have hmasters₁ : ∀ r ∈ groupHeaderCopies, (S₁.R r.1).length =
      groupHeaderValue (2^15*p) (executionStagePrecision p l target rhsExp+1)
        (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) L r.1 := by
    intro r hr
    by_cases hr128 : r.1 = 128
    · simp [S₁,hr128,groupHeaderValue]
    have hr126 : r.1 ≠ 126 := by
      simp only [groupHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hv128 : r.1.val ≠ 128 := fun h => hr128 (Fin.ext h)
    simpa only [S₁,Function.update_of_ne hr128,Function.update_of_ne hr126,groupHeaderValue,
      ite_eq_right hv128] using hmasters r hr
  obtain ⟨v₂,S₂,n₂,ys,hu₂,hn₂,he₂,hi₂,ho₂,hl₂,hylen,hframe,herror⟩ :=
    conditionalHaloClass_spec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget hband has hbs hL hLs hpad C hC x hx
      v₁ S₁ borrowed E outputTail hE (by simpa [S₁] using hdst) hmasters₁ (by simpa [S₁] using haMaster) (by simpa [S₁] using hbMaster) hleft (by
        intro k hk hk93 hk110
        have hk126 : k ≠ 126 := by intro he; subst k; norm_num at hk
        have hk128 : k ≠ 128 := by intro he; subst k; norm_num at hk
        simpa [S₁,hk126,hk128] using hblank k hk hk93 hk110)
      (by simpa [S₁] using hsrc) (by simpa [S₁] using h129) (by simpa [S₁] using h133)
      (by simpa [S₁] using hwidth) (by
        intro k hk
        have hk126 : k ≠ 126 := by intro he; subst k; norm_num at hk
        have hk128 : k ≠ 128 := by intro he; subst k; norm_num at hk
        simpa [S₁,hk126,hk128] using hfresh k hk)
  have h93 : S₁.R 93 = S.R 93 := by simp [S₁]
  refine ⟨v₂,S₂,n₁+n₂,ys,hu₂.trans hu₁,by omega,Exec.seq he₁ he₂,hi₂,ho₂,hl₂,hylen,?_,herror⟩
  rw [h93] at hframe
  rw [hframe]
  funext k
  by_cases hk128 : k = 128 <;> simp [S₁,publishedClassR,Function.update_apply,hk128]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
