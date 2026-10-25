module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOuterHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedNaturalGroup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawNaturalGroupInput

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
  .seq installGroupHeaders (.seq (embProg groupReg id rawNaturalGroupPrepare)
    (.seq (ucopy 116 129 133) (embProg groupReg id (closedBatch hR hQ))))

def protectedRawGroupCost (p l B L s t u target rhsExp : ℕ) : ℕ :=
  let q := executionPrecision p l target rhsExp
  let N := executionStagePrecision p l target rhsExp+1
  let P := 2^15*p
  let band := PhaseCellBand.width p u
  installGroupHeadersCost P N q l s t u band L +
    generateOriginAndGatherControlsCost P q s t u band L + rawNaturalGatherCost q s +
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
    (h129 : S.R 129 = []) (h133 : S.R 133 = []) :
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
      (∀ k : Fin 144, 117 ≤ k.val → k ≠ 129 → S'.R k = S.R k) ∧
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
  obtain ⟨vp, np, hup, hnp, hep⟩ := rawNaturalGroupInputBank_exec (body := body)
    P N q l s t u band L hP hs hst hu hgroup hband hg.1 hLs (by omega) C
    (embDn groupReg v₁) borrowed (S.R 93) S.inp S.out
  rw [← hw] at hep
  have hbody : ∀ f, embTab groupReg body (id f) = embProg groupReg id (body f) := fun _ => rfl
  obtain ⟨v₂, S₂, he₂, hv₂, hu₂, hbank₂, hoff₂⟩ := exec_emb groupReg_injective hbody hep v₁ rfl S₁ hbank₁
  have hS₂off (k : Fin 144) (hk : 117 ≤ k.val) : S₂.L k = S.L k ∧ S₂.R k = S.R k := by
    obtain ⟨hl, hr⟩ := hoff₂ k (groupReg_off k hk)
    exact ⟨hl, hr.trans (copiedGroupR_off P N q l s t u band L S.R k hk)⟩
  have h116 : (S₂.R 116).length = B := by
    have hh := congrArg (fun S : Stacks 117 A => (S.R 116).length) hbank₂
    simpa [embStk, groupReg, batchInputBank, B] using hh
  obtain ⟨v₃, hu₃, he₃⟩ := ucopy_exec (body := embTab groupReg body)
    (a := 116) (b := 129) (t := 133) (by decide) (by decide) (by decide) v₂ S₂
    (by rw [(hS₂off 133 (by decide)).2]; exact h133)
  let S₃ : Stacks 144 A := { S₂ with R := Function.update S₂.R 129 (List.replicate B tick) }
  have he₃' : Exec (embTab groupReg body) (ucopy 116 129 133) (mk v₂ S₂) (4*B+4) (mk v₃ S₃) := by
    simpa [S₃, h116, (hS₂off 129 (by decide)).2, h129] using he₃
  have hbank₃ : embStk groupReg S₃ = batchInputBank P N q l s t u band L B
      (fun n => (lo n).val) rhs (raw++borrowed) (S.R 93) S.inp S.out := by
    rw [groupProject_updateR S₂ 129 (List.replicate B tick) (by decide)]
    exact hbank₂
  obtain ⟨vs, Ss, ns, hus, hns, hes, his, hos, hls, hrs, hcleans, hpoints, herrors, hprefix⟩ :=
    closedNaturalGroup_spec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget hgroup hpad
      C hC x hx (embDn groupReg v₃) (S.R 93) (raw++borrowed) S.inp S.out
  obtain ⟨v₄, S₄, he₄, hv₄, hu₄, hbank₄, hoff₄⟩ := exec_emb groupReg_injective hbody hes v₃ rfl S₃ hbank₃
  have hfinalR (i : Fin 117) : S₄.R (groupReg i) = Ss.R i := congrArg (fun S : Stacks 117 A => S.R i) hbank₄
  have hfinalL (i : Fin 117) : S₄.L (groupReg i) = Ss.L i := congrArg (fun S : Stacks 117 A => S.L i) hbank₄
  have h93 : S₄.R 93 = Ss.R 93 := by simpa [groupReg] using hfinalR 93
  have h110 : S₄.R 110 = Ss.R 110 := by simpa [groupReg] using hfinalR 110
  refine ⟨v₄, S₄, installGroupHeadersCost P N q l s t u band L+(np+((4*B+4)+ns)),
    hu₄.trans (hus.trans (hu₃.trans (hu₂.trans (hup.trans hu₁)))), ?_,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃' he₄)), ?_, ?_, ?_, h110.trans hrs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [protectedRawGroupCost]
    dsimp only [P,N,q,band,B] at *
    omega
  · exact (congrArg (fun S : Stacks 117 A => S.inp) hbank₄).trans his
  · exact (congrArg (fun S : Stacks 117 A => S.out) hbank₄).trans hos
  · funext k
    by_cases hk : k.val < 117
    · let i : Fin 117 := ⟨k.val,hk⟩
      have he : groupReg i = k := Fin.ext rfl
      rw [← he, hfinalL i, hls i, hleft (groupReg i) i.isLt]
    · exact (hoff₄ k (groupReg_off k (by omega))).1.trans (hS₂off k (by omega)).1
  · intro k hk hk93 hk110
    let i : Fin 117 := ⟨k.val,hk⟩
    have he : groupReg i = k := Fin.ext rfl
    rw [← he, hfinalR i]
    exact hcleans i (fun h => hk93 (he.symm.trans (congrArg groupReg h)))
      (fun h => hk110 (he.symm.trans (congrArg groupReg h)))
  · have hh := (hoff₄ 129 (groupReg_off 129 (by decide))).2
    simpa [S₃] using hh
  · intro k hk hk129
    have hr := (hoff₄ k (groupReg_off k hk)).2
    exact hr.trans (by simpa [S₃,hk129] using (hS₂off k hk).2)
  · intro n i
    rw [h93]
    exact hpoints n i
  · intro n
    rw [h93]
    exact herrors n
  · obtain ⟨ys, hylen, hy⟩ := hprefix
    exact ⟨ys, hylen, h93.trans hy⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
