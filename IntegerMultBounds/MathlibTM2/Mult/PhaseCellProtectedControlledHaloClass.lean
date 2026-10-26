module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClassFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedControlledHaloGroupInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedHaloBatchSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinishHaloClass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloScatterCoreRead

/-! Complete the nonempty runtime branch from its controlled bank, reusing the
computed origins and gather controls through solve, publication and release. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def protectedControlledHaloClass (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq protectedControlledHaloGroupInput (.seq (protectedBatchSolve hR hQ) finishNaturalClass)

def protectedControlledHaloClassCost (p l B L s t u target rhsExp a b : ℕ) : ℕ :=
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  (48*s*w+27)+(rawNaturalGatherCost q s+2*(a+b)+5)+(4*B+4)+sizedClosedBatchBound p l B L s t u target rhsExp+94*s*w+39

theorem protectedControlledHaloClass_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hgroup : 0 < (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length) (hpad : L+L ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (v : HS 144 Q A U) (S : Stacks 144 A) (borrowed E outputTail : List (Fin (A+4)))
    (hE : E.length = s*executionWidth p l target rhsExp) (hdst : S.R 132 = E++outputTail)
    (hbank : embStk groupReg S = controlledHaloGroupInputBank (2^15*p)
      (executionStagePrecision p l target rhsExp+1) (executionPrecision p l target rhsExp)
      l t u (PhaseCellBand.width p u) a b L C borrowed (S.R 93) S.inp S.out)
    (h128 : (S.R 128).length = L)
    (h129 : S.R 129 = []) (h133 : S.R 133 = [])
    (hwidth : (S.R 130).length = executionWidth p l target rhsExp)
    (hfresh : ∀ k ∈ [(131 : Fin 144),134,135,136,137,140], S.R k = []) :
    let B := (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length
    let lo := haloGroupOrigin s t (PhaseCellBand.width p u) a b L
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    ∃ v' S' n, ∃ ys : BoundedEncodedStream A w q (interiorOutputExponent p l target rhsExp), v'.user = v.user ∧
      n ≤ protectedControlledHaloClassCost p l B L s t u target rhsExp a b ∧
      Exec (embTab groupReg body) (protectedControlledHaloClass hR hQ) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ys.val.length = B*L*w ∧
      S'.R = publishedClassR (restoredGroupR S.R) (scatterRows (L*w) E (ys++S.R 93)
        (haloScatterGaps s t (PhaseCellBand.width p u) a b L w)++outputTail) ∧
      ∀ n : Fin B, PhaseCellInterface.ErrorOn (publishedCellCore (lo n) L)
        (publishedCellRead q w (0 : ZMod s) (S'.R 132)) x (1/(2 : ℝ)^target) := by
  dsimp only
  let P := 2^15*p
  let N := executionStagePrecision p l target rhsExp+1
  let band := PhaseCellBand.width p u
  let B := (haloLengthGroup s t band a b L).length
  let lo := haloGroupOrigin s t band a b L
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let raw := cstream A w (chirpLine s C)
  let rhs := cstream A w ((List.range B).flatMap (cellSourceRows L lo (fun _ => C)))
  have hE' : E.length = s*w := hE
  have hw : w = 2*q+8 := by dsimp [q,w,executionWidth,executionPrecision]; omega
  have hsrc : S.R 110 = raw++borrowed := by
    have hh := congrArg (fun B : Stacks 117 A => B.R 110) hbank
    simpa [embStk,groupReg,controlledHaloGroupInputBank,haloOriginAndGatherControlsR,haloClassControlsR,
      haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank,raw,hw] using hh
  obtain ⟨v₁,S₁,n₁,hu₁,hn₁,he₁,hbank₁,hL₁,hR₁,hctrl₁⟩ := protectedControlledHaloGroupInput_exec (body := body)
    P N q l s t u band a b L hst hgroup C v S borrowed (S.R 93) S.inp S.out hbank h128
    (by simpa only [← hw] using hwidth) (by
      intro k hk
      apply hfresh k
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
      rcases hk with rfl | rfl | rfl <;> simp)
  rw [← hw] at hbank₁ hctrl₁ hn₁
  have hi₁ : S₁.inp = S.inp := congrArg (fun B : Stacks 117 A => B.inp) hbank₁
  have ho₁ : S₁.out = S.out := congrArg (fun B : Stacks 117 A => B.out) hbank₁
  have hl₁ : S₁.L = S.L := by
    funext k
    by_cases hk : k.val < 117
    · let i : Fin 117 := ⟨k.val,hk⟩
      have hi : groupReg i = k := Fin.ext rfl
      have hh₁ := congrArg (fun B : Stacks 117 A => B.L i) hbank₁
      have hh := congrArg (fun B : Stacks 117 A => B.L i) hbank
      have hz₁ : S₁.L k = [] := by simpa [embStk,Function.comp_apply,hi,batchInputBank] using hh₁
      have hz : S.L k = [] := by
        simpa [embStk,Function.comp_apply,hi,controlledHaloGroupInputBank,haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank] using hh
      rw [hz₁,hz]
    · exact hL₁ k (by omega)
  obtain ⟨v₂,S₂,n₂,hu₂,hn₂,he₂,hi₂,ho₂,hl₂,hr₂,hclean₂,hB₂,hR₂,hpoint₂,herror₂,ys,hylen,hys⟩ :=
    protectedHaloBatchSolve_spec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget hgroup hpad C hC x hx
      v₁ S₁ borrowed (S.R 93) (by simpa only [hi₁,ho₁] using hbank₁)
      (by rw [hR₁ 129 (by decide) (by decide)]; exact h129)
      (by rw [hR₁ 133 (by decide) (by decide)]; exact h133)
  have h128₂ : (S₂.R 128).length = L := by
    rw [hR₂ 128 (by decide) (by decide),hR₁ 128 (by decide) (by decide)]
    exact h128
  have hfresh₂ : ∀ k ∈ [(88 : Fin 144),89,90,92,94,131,134,135,136,137], S₂.R k = [] := by
    intro k hk
    by_cases hlo : k.val < 117
    · apply hclean₂ k hlo
      · intro he; subst k; norm_num at hk
      · intro he; subst k; norm_num at hk
    · have hk129 : k ≠ 129 := by intro he; subst k; norm_num at hk
      have hk140 : k ≠ 140 := by intro he; subst k; norm_num at hk
      rw [hR₂ k (by omega) hk129,hR₁ k (by omega) hk140]
      apply hfresh k
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals omega
  have hrhs : rhs.length = B*L*w := by simp [rhs,cellSourceRows,Nat.mul_assoc]
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := finishHaloClass_exec (body := embTab groupReg body)
    hst band a b L w (by dsimp [w,executionWidth]; omega) hgroup rhs (raw++borrowed)
    E ys (S.R 93) outputTail hE (by simpa only [Nat.mul_assoc] using hylen) hrhs v₂ S₂ h128₂
    (by rw [hR₂ 130 (by decide) (by decide),hR₁ 130 (by decide) (by decide)]; exact hwidth)
    (by simp [hB₂,band]) hr₂
    (by rw [hR₂ 140 (by decide) (by decide)]; simpa only [hfresh 140 (by simp),List.append_nil] using hctrl₁)
    (by rw [hR₂ 132 (by decide) (by decide),hR₁ 132 (by decide) (by decide)]; exact hdst) hys hfresh₂
  let published := scatterRows (L*w) E (ys++S.R 93) (haloScatterGaps s t band a b L w)++outputTail
  let S₃ : Stacks 144 A := { S₂ with R := finishedClassR S₂.R (raw++borrowed) (S.R 93) published }
  have hframe : S₃.R = publishedClassR (restoredGroupR S.R) published := by
    funext k
    by_cases hk128 : k = 128
    · subst k; simp [S₃,finishedClassR,publishedClassR]
    by_cases hk129 : k = 129
    · subst k; simp [S₃,finishedClassR,publishedClassR]
    by_cases hk132 : k = 132
    · subst k; simp [S₃,finishedClassR,publishedClassR]
    by_cases hk140 : k = 140
    · subst k; simp [S₃,finishedClassR,publishedClassR]
    by_cases hk93 : k = 93
    · subst k; simp [S₃,finishedClassR,publishedClassR,restoredGroupR]
    by_cases hk110 : k = 110
    · subst k; simpa [S₃,finishedClassR,publishedClassR,restoredGroupR] using hsrc.symm
    simp only [S₃,finishedClassR,publishedClassR,Function.update_of_ne hk128,
      Function.update_of_ne hk129,Function.update_of_ne hk132,Function.update_of_ne hk140,
      Function.update_of_ne hk93,Function.update_of_ne hk110]
    by_cases hlo : k.val < 117
    · simp [restoredGroupR,hlo,hk93,hk110,hclean₂ k hlo hk93 hk110]
    · simpa [restoredGroupR,hlo] using (hR₂ k (by omega) hk129).trans (hR₁ k (by omega) hk140)
  have hylen' : ys.val.length = B*(L*w) := by simpa only [Nat.mul_assoc] using hylen
  refine ⟨v₃,S₃,n₁+(n₂+n₃),ys,hu₃.trans (hu₂.trans hu₁),?_,Exec.seq he₁ (Exec.seq he₂ he₃),
    hi₂.trans hi₁,ho₂.trans ho₁,hl₂.trans hl₁,hylen,hframe,?_⟩
  · dsimp only [protectedControlledHaloClassCost]
    dsimp only [P,N,q,w,band,B] at *
    omega
  · intro n
    have hf := haloScatterGaps_fits s t band a b L w E hE'.ge
    have hpub : S₃.R 132 = scatterRows (L*w) (E++outputTail) (ys++S.R 93)
        (haloScatterGaps s t band a b L w) := by
      rw [scatterRows_append (L*w) (haloScatterGaps s t band a b L w) E (ys++S.R 93) outputTail hf]
      simp [S₃,finishedClassR,published]
    rw [hpub]
    apply haloScatterRows_errorOn t band a b L q w (E++outputTail) (ys++S.R 93)
      (by simp only [List.length_append]; omega)
      (by simp only [List.length_append]; change B*(L*w) ≤ _; omega)
      x (1/(2 : ℝ)^target) ?_ n
    intro m i
    simpa only [hys] using hpoint₂ m i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
