module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRunNaturalLengthKeys
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseKeyRuntime

/-! A fixed program initializes and executes the natural length schedule, then
releases its widths. Only the ambient output changes; the raw input, native
stacks, master headers and every borrowed suffix are restored exactly. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def solveNaturalInterior (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq initializeLengthKeys (.seq (runLengthKeys hR hQ) releaseKeyRuntime)

def solveNaturalInteriorCost (p l s t u target rhsExp : ℕ) : ℕ :=
  let band := PhaseCellBand.width p u
  let P := 2^15*p
  let N := executionStagePrecision p l target rhsExp+1
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let V := weightWorkspaceWidth P q w t u
  initializeLengthKeysCost P N q l s t u band +
    (lengthKeyLoopCost p l s t u target rhsExp V (naturalPositiveLengthKeys s t band)+1) +
    (2*(V+w)+5)

theorem solveNaturalInterior_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l s t p u target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (interiorSet s t (PhaseCellBand.width p u)) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (v : HS 144 Q A U) (S : Stacks 144 A) (borrowed E outputTail : List (Fin (A+4)))
    (hE : E.length = s*executionWidth p l target rhsExp) (hdst : S.R 132 = E++outputTail)
    (h127 : S.R 127 = []) (h138 : S.R 138 = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l target rhsExp) (chirpLine s C)++borrowed) S) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    ∃ v' n, ∃ E' : List (Fin (A+4)), v'.user = v.user ∧
      n ≤ solveNaturalInteriorCost p l s t u target rhsExp ∧ E'.length = s*w ∧
      Exec (embTab groupReg body) (solveNaturalInterior hR hQ) (mk v S) n
        (mk v' { S with R := Function.update S.R 132 (E'++outputTail) }) ∧
      PhaseCellInterface.ErrorOn (interiorSet s t (PhaseCellBand.width p u))
        (publishedCellRead q w (0 : ZMod s) (E'++outputTail)) x (1/(2 : ℝ)^target) := by
  dsimp only
  let P := 2^15*p
  let N := executionStagePrecision p l target rhsExp+1
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  let V := weightWorkspaceWidth P q w t u
  let K := (naturalPositiveLengthKeys s t band).length
  let keys := naturalPositiveLengthPackets A V s t band
  have hw : 2*q+8 = w := by dsimp [q,w,executionPrecision,executionWidth]; omega
  have hP : 13 ≤ P := by dsimp [P]; omega
  have hs : 0 < s := NeZero.pos s
  have h125 : S.R 125 = [] := List.eq_nil_of_length_eq_zero hready.keyWidth
  have h130 : S.R 130 = [] := List.eq_nil_of_length_eq_zero hready.wordWidth
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := initializeLengthKeys_exec (body := body)
    P N q l s t u band hP hs hst hu hband (by omega) v S
    hready.masters hready.left hready.blank (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      · exact h125
      · exact h127
      · exact h130
      · exact hready.headerTemp
      · exact h138)
  simp only [hw] at he₁
  let S₁ : Stacks 144 A := { S with R := initializedKeyRuntimeR S.R V w K keys }
  have hready₁ : LengthKeyReady P N q l s t u band V w
      (cstream A w (chirpLine s C)++borrowed) S₁ := hready.initialized
  have hwide : s < 2^V := by
    obtain ⟨hb,_⟩ := weightWorkspaceWidth_control (q := q) (w := w) hP hs hst hu hband
    dsimp only [V]
    nlinarith only [hb,hst,hs]
  obtain ⟨v₂,S₂,n₂,E',hu₂,hn₂,he₂,hi₂,ho₂,hl₂,hlen,hr₂,herror⟩ :=
    runNaturalLengthKeys_spec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget hband
      hwide hpad C hC x hx v₁ S₁ borrowed E outputTail (S.R 126) hE
      (by simpa [S₁,initializedKeyRuntimeR] using hdst)
      (by simp [S₁,initializedKeyRuntimeR,keys,band])
      (by simp [S₁,initializedKeyRuntimeR,K,band]) hready₁
  obtain ⟨v₃,hu₃,he₃⟩ := releaseKeyRuntime_exec (body := embTab groupReg body) V w v₂ S₂
    (by rw [hr₂]; simp [keyLoopR,S₁,initializedKeyRuntimeR])
    (by rw [hr₂]; simp [keyLoopR,S₁,initializedKeyRuntimeR])
  have hfinal : { S₂ with R := releasedKeyRuntimeR S₂.R } =
      { S with R := Function.update S.R 132 (E'++outputTail) } := by
    refine Stacks.ext ?_ ?_ ?_ ?_
    · exact hi₂
    · exact ho₂
    · exact hl₂
    · change releasedKeyRuntimeR S₂.R = _
      rw [hr₂]
      exact released_keyLoop_initialized S.R V w K keys (E'++outputTail) h125 h127 h130
  refine ⟨v₃,n₁+(n₂+(2*(V+w)+5)),E',hu₃.trans (hu₂.trans hu₁),?_,hlen,?_,?_⟩
  · dsimp only [solveNaturalInteriorCost]
    dsimp only [P,N,q,w,band,V] at *
    omega
  · exact Exec.seq he₁ (Exec.seq he₂ (he₃.cast rfl (congrArg (mk v₃) hfinal)))
  · have h132 : S₂.R 132 = E'++outputTail := by simp [hr₂,keyLoopR]
    simpa only [h132] using herror

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
