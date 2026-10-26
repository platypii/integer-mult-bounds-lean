module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOuterHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedBatchSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedGroupInput

/-! An actual raw group solve inside a private 117-register bank. Retained outer
parameters and remaining keys survive the numerical call; its generated batch
count is saved outside the bank for publication and payload retirement. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def protectedRawGroup (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq installGroupHeaders (.seq protectedGroupInput
    (protectedBatchSolve hR hQ))

def protectedRawGroupCost (p l B L s t u target rhsExp : ℕ) : ℕ :=
  let q := executionPrecision p l target rhsExp
  let N := executionStagePrecision p l target rhsExp+1
  let P := 2^15*p
  let band := PhaseCellBand.width p u
  installGroupHeadersCost P N q l s t u band L +
    generateOriginAndGatherControlsCost P q s t u band L +
    (48*s*(executionWidth p l target rhsExp)+27) + rawNaturalGatherCost q s +
    (4*B+4)+sizedClosedBatchBound p l B L s t u target rhsExp

theorem protectedRawGroup_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hgroup : 0 < (naturalLengthGroup s t (PhaseCellBand.width p u) L).length) (hpad : L+L ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (interiorSet s t (PhaseCellBand.width p u)) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (v : HS 144 Q A U) (S : Stacks 144 A) (borrowed : List (Fin (A+4)))
    (hmasters : ∀ r ∈ groupHeaderCopies, (S.R r.1).length =
      groupHeaderValue (2^15*p) (executionStagePrecision p l target rhsExp+1)
        (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) L r.1)
    (hleft : ∀ k : Fin 144, k.val < 117 → S.L k = [])
    (hblank : ∀ k : Fin 144, k.val < 117 → k ≠ 93 → k ≠ 110 → S.R k = [])
    (hsrc : S.R 110 = cstream A (executionWidth p l target rhsExp) (chirpLine s C) ++ borrowed)
    (h129 : S.R 129 = []) (h133 : S.R 133 = [])
    (hwidth : (S.R 130).length = executionWidth p l target rhsExp)
    (hfresh : ∀ k ∈ [(131 : Fin 144),134,135], S.R k = []) :
    let B := (naturalLengthGroup s t (PhaseCellBand.width p u) L).length
    let lo := naturalGroupOrigin s t (PhaseCellBand.width p u) L
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let rhs := cstream A w ((List.range B).flatMap (cellSourceRows L lo (fun _ => C)))
    ∃ v' S' n, v'.user = v.user ∧ n ≤ protectedRawGroupCost p l B L s t u target rhsExp ∧
      Exec (embTab groupReg body) (protectedRawGroup hR hQ) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧
      S'.L = S.L ∧
      S'.R 110 = rhs ++ (cstream A w (chirpLine s C) ++ borrowed) ∧
      (∀ k : Fin 144, k.val < 117 → k ≠ 93 → k ≠ 110 → S'.R k = []) ∧
      S'.R 129 = List.replicate B tick ∧
      (∀ k : Fin 144, 117 ≤ k.val → k ≠ 129 → k ≠ 140 → S'.R k = S.R k) ∧
      S'.R 140 = gatherControls A (naturalScatterGaps s t (PhaseCellBand.width p u) L w)++S.R 140 ∧
      (∀ n : Fin B, ∀ i : Fin L, |(value q (decodeWord (((S'.R 93).drop ((n.val*L+i.val)*w)).take w))).re -
        x (lo n+(i.val : ZMod s))| ≤ 1/(2 : ℝ)^target) ∧
      (∀ n : Fin B, PhaseCellInterface.ErrorOn (publishedCellCore (lo n) L)
        (publishedBatchRead q w n.val L (lo n) (S'.R 93)) x (1/(2 : ℝ)^target)) ∧
      ∃ ys : List (Fin (A+4)), ys.length = B*L*w ∧ S'.R 93 = ys ++ S.R 93 := by
  dsimp only
  let P := 2^15*p
  let N := executionStagePrecision p l target rhsExp+1
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  let B := (naturalLengthGroup s t band L).length
  let lo := naturalGroupOrigin s t band L
  let raw := cstream A w (chirpLine s C)
  let rhs := cstream A w ((List.range B).flatMap (cellSourceRows L lo (fun _ => C)))
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hg := naturalGroup_solver_geometry hst band L (⟨0,hgroup⟩ : Fin B)
  have hLs : L ≤ s := by have hh := hg.2.1; omega
  have hband : band ≤ s := by
    have hh := hg.2.1
    rw [naturalGroupOrigin_val] at hh
    unfold naturalStart at hh
    omega
  have hP : 13 ≤ P := by dsimp [P]; omega
  have hw : w = 2*q+8 := by dsimp [q,w,executionWidth,executionPrecision]; omega
  obtain ⟨v₁, hu₁, he₁⟩ := installGroupHeaders_exec (body := embTab groupReg body)
    P N q l s t u band L v S hmasters h133
  let S₁ : Stacks 144 A := { S with R := copiedGroupR P N q l s t u band L S.R }
  have hbank₁ := copiedGroup_project P N q l s t u band L S raw borrowed hleft hblank hsrc
  have h128 : (S₁.R 128).length = L := by
    dsimp only [S₁]
    rw [copiedGroupR_off P N q l s t u band L S.R 128 (by decide)]
    have hh := hmasters (128,102) (by simp [groupHeaderCopies])
    simpa [groupHeaderValue] using hh
  obtain ⟨v₂,S₂,np,hup,hnp,he₂,hbank₂,hleft₂,hoff₂,hctrl₂⟩ := protectedGroupInput_exec (body := body)
    P N q l s t u band L hP hs hst hu hgroup hband hg.1 hLs (by omega) C v₁ S₁
    borrowed (S.R 93) S.inp S.out (by simpa only [← hw] using hbank₁) h128
    (by dsimp only [S₁]; rw [copiedGroupR_off P N q l s t u band L S.R 130 (by decide)]; simpa only [← hw] using hwidth)
    (by
      intro k hk
      have hkhi : 117 ≤ k.val := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl <;> decide
      dsimp only [S₁]
      rw [copiedGroupR_off P N q l s t u band L S.R k hkhi]
      exact hfresh k hk)
  rw [← hw] at hbank₂ hctrl₂ hnp
  have hS₂left (k : Fin 144) (hk : 117 ≤ k.val) : S₂.L k = S.L k := hleft₂ k hk
  have hS₂off (k : Fin 144) (hk : 117 ≤ k.val) (hk140 : k ≠ 140) : S₂.R k = S.R k :=
    (hoff₂ k hk hk140).trans (copiedGroupR_off P N q l s t u band L S.R k hk)
  have hi₂ : S₂.inp = S.inp := congrArg (fun B : Stacks 117 A => B.inp) hbank₂
  have ho₂ : S₂.out = S.out := congrArg (fun B : Stacks 117 A => B.out) hbank₂
  have hL₂ : S₂.L = S.L := by
    funext k
    by_cases hk : k.val < 117
    · let i : Fin 117 := ⟨k.val,hk⟩
      have he : groupReg i = k := Fin.ext rfl
      have hh := congrArg (fun B : Stacks 117 A => B.L i) hbank₂
      have hz : S₂.L k = [] := by simpa [embStk,Function.comp_apply,he,batchInputBank] using hh
      rw [hz,hleft k hk]
    · exact hS₂left k (by omega)
  obtain ⟨v₃,S₃,ns,hu₃,hns,he₃,hi₃,ho₃,hl₃,hr₃,hclean₃,hB₃,hoff₃,hpoints,herrors,hprefix⟩ :=
    protectedBatchSolve_spec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget hgroup hpad C hC x hx
      v₂ S₂ borrowed (S.R 93) (by simpa only [hi₂,ho₂] using hbank₂)
      (by rw [hS₂off 129 (by decide) (by decide)]; exact h129)
      (by rw [hS₂off 133 (by decide) (by decide)]; exact h133)
  refine ⟨v₃,S₃,installGroupHeadersCost P N q l s t u band L+(np+ns),
    hu₃.trans (hup.trans hu₁),?_,Exec.seq he₁ (Exec.seq he₂ he₃),hi₃.trans hi₂,ho₃.trans ho₂,
    hl₃.trans hL₂,hr₃,hclean₃,hB₃,?_,?_,hpoints,herrors,hprefix⟩
  · dsimp only [protectedRawGroupCost]
    dsimp only [P,N,q,band,B,w] at *
    omega
  · intro k hk hk129 hk140
    exact (hoff₃ k hk hk129).trans (hS₂off k hk hk140)
  · rw [hoff₃ 140 (by decide) (by decide)]
    simpa only [S₁,copiedGroupR_off P N q l s t u band L S.R 140 (by decide),band,w] using hctrl₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
