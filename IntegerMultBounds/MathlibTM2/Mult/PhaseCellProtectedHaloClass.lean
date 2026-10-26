module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClassFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedRawHaloGroup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinishHaloClass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloScatterCoreRead

/-! One complete nonempty clipped halo class: generated preparation, actual solve,
RHS retirement, ambient publication and per-class workspace release. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def protectedHaloClass (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq (protectedRawHaloGroup hR hQ) finishNaturalClass

theorem protectedHaloClass_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (has : a ≤ s) (hbs : b ≤ s)
    (hgroup : 0 < (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length) (hpad : L+L ≤ 2^l+1)
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
    ∃ v' S' n, ∃ ys : EncodedStream A w, v'.user = v.user ∧
      n ≤ protectedRawHaloGroupCost p l B L s t u target rhsExp a b+94*s*w+39 ∧
      Exec (embTab groupReg body) (protectedHaloClass hR hQ) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ys.val.length = B*L*w ∧
      S'.R = publishedClassR S.R (scatterRows (L*w) E (ys++S.R 93)
        (haloScatterGaps s t (PhaseCellBand.width p u) a b L w)++outputTail) ∧
      ∀ n : Fin B, PhaseCellInterface.ErrorOn (publishedCellCore (lo n) L)
        (publishedCellRead q w (0 : ZMod s) (S'.R 132)) x (1/(2 : ℝ)^target) := by
  dsimp only
  let band := PhaseCellBand.width p u
  let B := (haloLengthGroup s t band a b L).length
  let lo := haloGroupOrigin s t band a b L
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let raw := cstream A w (chirpLine s C)
  have hE' : E.length = s*w := hE
  let rhs := cstream A w ((List.range B).flatMap (cellSourceRows L lo (fun _ => C)))
  obtain ⟨v₁,S₁,n₁,hu₁,hn₁,he₁,hi₁,ho₁,hl₁,hr₁,hclean₁,hB₁,hoff₁,hctrl₁,hpoint₁,herror₁,ys,hylen,hys⟩ :=
    protectedRawHaloGroup_spec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget has hbs hgroup hpad C hC x hx
      v S borrowed hmasters haMaster hbMaster hleft hblank hsrc h129 h133 hwidth (by
        intro k hk
        apply hfresh k
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
        rcases hk with rfl | rfl | rfl <;> simp)
  have h128 : (S₁.R 128).length = L := by
    rw [hoff₁ 128 (by decide) (by decide) (by decide)]
    have hh := hmasters (128,102) (by simp [groupHeaderCopies])
    simpa [groupHeaderValue] using hh
  have hfresh₁ : ∀ k ∈ [(88 : Fin 144),89,90,92,94,131,134,135,136,137], S₁.R k = [] := by
    intro k hk
    by_cases hlo : k.val < 117
    · apply hclean₁ k hlo
      · intro he; subst k; norm_num at hk
      · intro he; subst k; norm_num at hk
    · rw [hoff₁ k (by omega) (by intro he; subst k; norm_num at hk)
        (by intro he; subst k; norm_num at hk)]
      apply hfresh k
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals omega
  have hrhs : rhs.length = B*L*w := by simp [rhs,cellSourceRows,Nat.mul_assoc]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := finishHaloClass_exec (body := embTab groupReg body)
    hst band a b L w (by dsimp [w,executionWidth]; omega) hgroup rhs (raw++borrowed)
    E ys (S.R 93) outputTail hE (by simpa only [Nat.mul_assoc] using hylen) hrhs v₁ S₁ h128
    (by rw [hoff₁ 130 (by decide) (by decide) (by decide)]; exact hwidth)
    (by simp [hB₁,band]) hr₁
    (by simpa only [hfresh 140 (by simp),List.append_nil] using hctrl₁)
    (by rw [hoff₁ 132 (by decide) (by decide) (by decide)]; exact hdst) hys hfresh₁
  let published := scatterRows (L*w) E (ys++S.R 93) (haloScatterGaps s t band a b L w)++outputTail
  let S₂ : Stacks 144 A := { S₁ with R := finishedClassR S₁.R (raw++borrowed) (S.R 93) published }
  have hframe : S₂.R = publishedClassR S.R published := by
    funext k
    by_cases hk128 : k = 128
    · subst k; simp [S₂,finishedClassR,publishedClassR]
    by_cases hk129 : k = 129
    · subst k; simp [S₂,finishedClassR,publishedClassR]
    by_cases hk132 : k = 132
    · subst k; simp [S₂,finishedClassR,publishedClassR]
    by_cases hk140 : k = 140
    · subst k; simp [S₂,finishedClassR,publishedClassR]
    by_cases hk93 : k = 93
    · subst k; simp [S₂,finishedClassR,publishedClassR]
    by_cases hk110 : k = 110
    · subst k; simpa [S₂,finishedClassR,publishedClassR] using hsrc.symm
    simp only [S₂,finishedClassR,publishedClassR,Function.update_of_ne hk128,
      Function.update_of_ne hk129,Function.update_of_ne hk132,Function.update_of_ne hk140,
      Function.update_of_ne hk93,Function.update_of_ne hk110]
    by_cases hlo : k.val < 117
    · rw [hclean₁ k hlo hk93 hk110,hblank k hlo hk93 hk110]
    · exact hoff₁ k (by omega) hk129 hk140
  have hn₂' : n₂ ≤ 94*s*executionWidth p l target rhsExp+39 := hn₂
  have hylen' : ys.val.length = B*(L*w) := by simpa only [Nat.mul_assoc] using hylen
  refine ⟨v₂,S₂,n₁+n₂,ys,hu₂.trans hu₁,by omega,Exec.seq he₁ he₂,hi₁,ho₁,hl₁,hylen,hframe,?_⟩
  intro n
  have hf := haloScatterGaps_fits s t band a b L w E hE'.ge
  have hpub : S₂.R 132 = scatterRows (L*w) (E++outputTail) (ys++S.R 93)
      (haloScatterGaps s t band a b L w) := by
    rw [scatterRows_append (L*w) (haloScatterGaps s t band a b L w) E (ys++S.R 93) outputTail hf]
    simp [S₂,finishedClassR,published]
  rw [hpub]
  apply haloScatterRows_errorOn t band a b L q w (E++outputTail) (ys++S.R 93)
    (by simp only [List.length_append]; omega)
    (by simp only [List.length_append]; change B*(L*w) ≤ _; omega)
    x (1/(2 : ℝ)^target) ?_ n
  intro m i
  simpa only [hys] using hpoint₁ m i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
