module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryUnscaleReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBoundaryRealUnfold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryPublicationReady

/-! The actual solved bank supplies the inverse-fold and real-publication controls. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def solvedBoundaryUnfold : Pr P 224 Q A U :=
  .seq preparedBoundaryUnfold boundaryRealProjection

def solvedBoundaryUnfoldCost (R : Regs 224 A) (N w : ℕ) : ℕ :=
  (2*([189,191,198,204].map (fun k => (R k).length)).sum+9)+
    generatedBoundaryUnfoldCost N w+(N*(12*w+9)+12)

theorem solvedBoundaryUnfold_exec {s : ℕ} [NeZero s] (hA : 4 ≤ A) (q : ℕ)
    (B : Finset (ZMod s)) (solution : List GaussianInt) (hlen : solution.length = B.card)
    (v : HS 224 Q A U) (S : Stacks 224 A) (hready : BoundaryUnscaleReady q S)
    (hcount : (S.R 116).length = B.card)
    (hsource : S.R 217 = cstream A (2*q+8) solution) :
    let retired : List (Fin 224) := [189,191,198,204]
    let S₀ : Stacks 224 A := {S with R := fun i => if i ∈ retired then [] else S.R i}
    ∃ v' m, v'.user = v.user ∧ m ≤ solvedBoundaryUnfoldCost S.R B.card (2*q+8) ∧
      Exec body solvedBoundaryUnfold (mk v S) m
        (mk v' {S₀ with R := (Function.update (Function.update S₀.R 217 []) 204
          (cstream A (2*q+8) ((bOrder s B).map (boundarySolutionField B solution))))}) := by
  dsimp only
  let w := 2*q+8
  let retired : List (Fin 224) := [189,191,198,204]
  let S₀ : Stacks 224 A := {S with R := fun i => if i ∈ retired then [] else S.R i}
  have hw : (S.R 160).length = w := hready.ready.wn
  have hclean : ∀ k ∈ ([184,223,208,211,201,215] : List (Fin 224)), S.R k = [] := by
    intro k hk
    apply hready.clean k
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
    tauto
  obtain ⟨v₁,m₁,hv₁,hm₁,he₁⟩ := preparedBoundaryUnfold_exec w solution v S
    hready.left hready.mul (by rw [hlen]; exact hcount) hsource hw hclean
  let S₁ : Stacks 224 A := {S₀ with R := (Function.update (Function.update S₀.R 217 []) 204
    (cstream A w (unfoldList solution)))}
  obtain ⟨v₂,m₂,hv₂,hm₂,he₂⟩ := boundaryRealProjection_exec (body := body) hA w
    (unfoldList solution) [] v₁ S₁
    (by simpa [S₁,S₀,retired,length_unfoldList,hlen] using hcount)
    (by simpa [S₁,S₀,retired] using hw) (by simp [S₁])
    (by simpa [S₁,S₀,retired] using hready.clean 184 (by simp))
    (by simp [S₁])
    (by simpa [S₁,S₀,retired] using hready.clean 223 (by simp))
  refine ⟨v₂,m₁+m₂,hv₂.trans hv₁,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
  · have hm₁' : m₁ ≤ (2*(retired.map (fun k => (S.R k).length)).sum+9)+
        generatedBoundaryUnfoldCost B.card w := by simpa only [hlen] using hm₁
    have hm₂' : m₂ ≤ B.card*(12*w+9)+12 := by
      simpa only [length_unfoldList,hlen] using hm₂
    exact Nat.add_le_add hm₁' hm₂'
  · apply congrArg (mk v₂)
    rw [boundary_unfold_field B solution hlen]
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h204 : i = 204 <;> by_cases h217 : i = 217 <;>
      simp [S₁,S₀,retired,w,h204,h217]

/-- Inverse folding leaves precisely the workspace required by generated publication. -/
theorem solvedBoundaryUnfold_publicationReady {A q s N V : ℕ} (S : Stacks 224 A)
    (h : BoundaryUnscaleReady q S) (hs : (S.R 121).length = s)
    (hV : (S.R 115).length = V) (hN : S.R 116 = List.replicate N tick)
    (output : List (Fin (A+4))) :
    let retired : List (Fin 224) := [189,191,198,204]
    let S₀ : Stacks 224 A := {S with R := fun i => if i ∈ retired then [] else S.R i}
    BoundaryPublicationReady {S₀ with R := (Function.update (Function.update S₀.R 217 []) 204 output)}
      s N V (2*q+8) := by
  dsimp only
  let retired : List (Fin 224) := [189,191,198,204]
  let S₀ : Stacks 224 A := {S with R := fun i => if i ∈ retired then [] else S.R i}
  let F : Stacks 224 A := {S₀ with R := (Function.update (Function.update S₀.R 217 []) 204 output)}
  have hmul : ∀ i : Fin 64, F.R (boundaryFactorMulReg i) = [] := by
    intro i
    have hi := i.isLt
    have hoff (k : Fin 224) (hk : 64 ≤ k.val) : boundaryFactorMulReg i ≠ k := by
      intro he
      have hv := congrArg (fun j : Fin 224 => j.val) he
      change i.val = k.val at hv
      omega
    simpa [F,S₀,retired,hoff 189 (by decide),hoff 191 (by decide),hoff 198 (by decide),
      hoff 204 (by decide),hoff 217 (by decide)] using h.mul i
  refine ⟨h.left,hmul,?_,?_,?_,?_,?_⟩
  · simpa [S₀,retired] using hs
  · have hw : (S.R 160).length = 2*q+8 := h.ready.wn
    simpa [S₀,retired] using hw
  · simpa [S₀,retired] using hV
  · simpa [S₀,retired] using hN
  · intro i hi
    have hm : i ∈ ([0,1,2,3,4,5,6,7,8,9] : List (Fin 224)) ∨
        i ∈ ([184,217,223,201,208,211,215,220,206] : List (Fin 224)) := List.mem_append.mp hi
    rcases hm with hm | hm
    · have hlt : i.val < 64 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact hmul ⟨i.val,hlt⟩
    · by_cases hi217 : i = 217
      · subst i; simp
      · have hclean : S.R i = [] := by
          apply h.clean i
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hm ⊢
          tauto
        have hoff : i ≠ 189 ∧ i ≠ 191 ∧ i ≠ 198 ∧ i ≠ 204 := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
          rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        simpa [S₀,retired,hi217,hoff.1,hoff.2.1,hoff.2.2.1,hoff.2.2.2] using hclean

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
