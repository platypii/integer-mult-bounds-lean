module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCorePublication

/-! Place the checked local solver beside core headers and publish its actual
output. The supplied premise is an execution of that concrete solver program. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  ScalarPlacement

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U} {body' : P → Pr P 256 Q A U}

def packedHaloPublicationReg : Fin 248 → Fin 256 := Fin.castLE (by decide)

def packedCorePublication : Pr P 256 Q A U :=
  preparedPackedSlice 249 250 130 132 248 251 252 253 254 104 105

noncomputable def packedHaloPublicationUsing (freshGeometry : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 256 Q A U :=
  .seq (embProg packedHaloPublicationReg id (packedHaloSolveUsing freshGeometry hR hQ)) packedCorePublication

noncomputable def packedHaloPublication (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 256 Q A U :=
  packedHaloPublicationUsing true hR hQ

theorem packedHaloPublicationUsing_exec (freshGeometry : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (hbody : ∀ f, body' f = embProg packedHaloPublicationReg id (body f))
    {s : ℕ} [NeZero s] (q w width k radius : ℕ)
    (D : ZMod s → GaussianInt) (x : ZMod s → ℝ) (ε : ℝ)
    (hleft : radius ≤ coreStart width k)
    (hright : coreStart width k+coreLength s width k+radius ≤ s)
    (tail : List (Fin (A+4))) (v : HS 256 Q A U) (S : Stacks 256 A)
    (v₁ : HS 248 Q A U) (F₁ : Stacks 248 A) (m : ℕ)
    (hu₁ : v₁.user = v.user)
    (he₁ : Exec body (packedHaloSolveUsing freshGeometry hR hQ)
      (mk (embDn packedHaloPublicationReg v) (embStk packedHaloPublicationReg S)) m (mk v₁ F₁))
    (hwidth : (F₁.R 130).length = w) (h104 : F₁.R 104 = []) (h105 : F₁.R 105 = [])
    (hsrc : F₁.R 132 = cstream A w
      (packedInterval (coreStart width k-radius) (coreLength s width k+2*radius) D)++tail)
    (herror : PhaseCellInterface.ErrorOn
      (haloVertices s (coreStart width k-radius) (coreStart width k+coreLength s width k+radius))
      (fun i => (packedIntervalRead q w (coreStart width k-radius) (F₁.R 132) i).re) x ε)
    (hoffset : (S.R 249).length = radius) (hrows : (S.R 250).length = coreLength s width k)
    (hfresh : ∀ i ∈ ([251,252,253,254] : List (Fin 256)), S.R i = []) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ m+preparedPackedSliceCost radius (coreLength s width k) w ∧
      Exec body' (packedHaloPublicationUsing freshGeometry hR hQ) (mk v S) n (mk v' F) ∧
      F.R 248 = cstream A w (ownedCoreWords width k D)++S.R 248 ∧ embStk packedHaloPublicationReg F = F₁ ∧
      PhaseCellInterface.ErrorOn (ownedCore s width k)
        (fun i => (packedIntervalRead q w (coreStart width k) (F.R 248) i).re) x ε ∧
      ∀ i : Fin 256, 248 ≤ i.val → i ≠ 248 → F.R i = S.R i := by
  have hinj : Function.Injective packedHaloPublicationReg := by
    intro i j hij; exact Fin.ext (congrArg (fun k : Fin 256 => k.val) hij)
  obtain ⟨v₂,F₂,he₂,hv₂,hu₂,hview,hframe⟩ := exec_emb hinj hbody he₁ v rfl S rfl
  have hread (i : Fin 248) : F₂.R (packedHaloPublicationReg i) = F₁.R i :=
    congrArg (fun G : Stacks 248 A => G.R i) hview
  have hreg132 : packedHaloPublicationReg 132 = 132 := by decide
  have hread132 : F₂.R 132 = F₁.R 132 := by
    simpa only [hreg132] using hread 132
  have hnew (i : Fin 256) (hi : 248 ≤ i.val) : F₂.R i = S.R i := by
    apply (hframe i _).2
    intro j hij
    have hj := j.isLt
    have hh := congrArg Fin.val hij
    change j.val = i.val at hh
    omega
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃,haccuracy⟩ := preparedCorePublication_exec (body := body')
    249 250 130 132 248 251 252 253 254 104 105 (by decide) q w width k radius D x ε hleft hright
    tail v₂ F₂ (by rw [hnew 249 (by decide)]; exact hoffset)
    (by rw [hnew 250 (by decide)]; exact hrows) ((congrArg List.length (hread 130)).trans hwidth)
    ((hread 132).trans hsrc) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hnew 251 (by decide)]; exact hfresh 251 (by decide)
      · rw [hnew 252 (by decide)]; exact hfresh 252 (by decide)
      · rw [hnew 253 (by decide)]; exact hfresh 253 (by decide)
      · rw [hnew 254 (by decide)]; exact hfresh 254 (by decide)
      · exact (hread 104).trans h104
      · exact (hread 105).trans h105)
    (by simpa only [hread132] using herror)
  let F : Stacks 256 A := {F₂ with R := (Function.update F₂.R 248
    (cstream A w (ownedCoreWords width k D)++F₂.R 248))}
  refine ⟨v₃,F,m+n₃,hu₃.trans (hu₂.trans hu₁),Nat.add_le_add_left hn₃ _,Exec.seq he₂ he₃,?_,?_,?_,?_⟩
  · simp [F,hnew 248 (by decide)]
  · have he : embStk packedHaloPublicationReg F = embStk packedHaloPublicationReg F₂ := by
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      have hoff : packedHaloPublicationReg i ≠ 248 := by
        intro hi
        have hh := congrArg Fin.val hi
        change i.val = 248 at hh
        have hi' := i.isLt
        omega
      simp only [F,embStk,Function.comp_apply,Function.update_of_ne hoff]
    exact he.trans hview
  · simpa [F] using haccuracy
  · intro i hi hn
    simpa only [F,Function.update_of_ne hn] using hnew i hi

theorem packedHaloPublication_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (hbody : ∀ f, body' f = embProg packedHaloPublicationReg id (body f))
    {s : ℕ} [NeZero s] (q w width k radius : ℕ)
    (D : ZMod s → GaussianInt) (x : ZMod s → ℝ) (ε : ℝ)
    (hleft : radius ≤ coreStart width k)
    (hright : coreStart width k+coreLength s width k+radius ≤ s)
    (tail : List (Fin (A+4))) (v : HS 256 Q A U) (S : Stacks 256 A)
    (v₁ : HS 248 Q A U) (F₁ : Stacks 248 A) (m : ℕ)
    (hu₁ : v₁.user = v.user)
    (he₁ : Exec body (packedHaloSolve hR hQ)
      (mk (embDn packedHaloPublicationReg v) (embStk packedHaloPublicationReg S)) m (mk v₁ F₁))
    (hwidth : (F₁.R 130).length = w) (h104 : F₁.R 104 = []) (h105 : F₁.R 105 = [])
    (hsrc : F₁.R 132 = cstream A w
      (packedInterval (coreStart width k-radius) (coreLength s width k+2*radius) D)++tail)
    (herror : PhaseCellInterface.ErrorOn
      (haloVertices s (coreStart width k-radius) (coreStart width k+coreLength s width k+radius))
      (fun i => (packedIntervalRead q w (coreStart width k-radius) (F₁.R 132) i).re) x ε)
    (hoffset : (S.R 249).length = radius) (hrows : (S.R 250).length = coreLength s width k)
    (hfresh : ∀ i ∈ ([251,252,253,254] : List (Fin 256)), S.R i = []) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ m+preparedPackedSliceCost radius (coreLength s width k) w ∧
      Exec body' (packedHaloPublication hR hQ) (mk v S) n (mk v' F) ∧
      F.R 248 = cstream A w (ownedCoreWords width k D)++S.R 248 ∧ embStk packedHaloPublicationReg F = F₁ ∧
      PhaseCellInterface.ErrorOn (ownedCore s width k)
        (fun i => (packedIntervalRead q w (coreStart width k) (F.R 248) i).re) x ε ∧
      ∀ i : Fin 256, 248 ≤ i.val → i ≠ 248 → F.R i = S.R i := by
  exact packedHaloPublicationUsing_exec (body := body) (body' := body') true
    hR hQ hbody q w width k radius D x ε hleft hright tail v S v₁ F₁ m hu₁ he₁
    hwidth h104 h105 hsrc herror hoffset hrows hfresh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
