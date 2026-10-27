module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilySolveHaloInteriorBounded
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeInteriorOutput

/-! Initialize a pass from its actual RHS and solve using the retained weight
family. The owned result is prepended to the caller's ambient suffix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 151 Q A U}

theorem weightFamilyLegacyBank_update_output {A : ℕ} (S : Stacks 151 A) (xs : List (Fin (A+4))) :
    weightFamilyLegacyBank {S with R := Function.update S.R 132 xs} =
      {weightFamilyLegacyBank S with R := Function.update (weightFamilyLegacyBank S).R 132 xs} := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  simp [weightFamilyLegacyBank,embStk,weightFamilyCoreReg,cachedGroupLegacyReg,Function.update_apply,Fin.ext_iff]

noncomputable def familyInitializedInterior (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 151 Q A U :=
  .seq (embProg weightFamilyLegacyReg Empty.elim (initializeInteriorOutput (P₀ := Empty))) (familySolveHaloInterior hR hQ)

def familyInitializedInteriorCost (A p l s t u target rhsExp a b : ℕ) : ℕ :=
  initializeInteriorOutputCost (executionPrecision p l target rhsExp) s+
    familySolveHaloInteriorCost A p l s t u target rhsExp a b

theorem familyInitializedInterior_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l s t p u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (v : HS 151 Q A U) (S : Stacks 151 A) (borrowed familyTail : List (Fin (A+4)))
    (h127 : S.R 127 = []) (h138 : S.R 138 = [])
    (ha : (S.R 141).length = a) (hb : (S.R 142).length = b)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l target rhsExp) (chirpLine s C)++borrowed) (weightFamilyLegacyBank S))
    (hfamily : S.R 148 = weightKeyFamily (haloWeightKeyPages A (executionWidth p l target rhsExp)
      (executionPrecision p l target rhsExp) (2^15*p) s t u (PhaseCellBand.width p u) a b
      (haloLengthKeys s t (PhaseCellBand.width p u) a b))++familyTail)
    (hcache : ∀ i ∈ ([(144 : Fin 151),145,146,147,149] : List (Fin 151)), S.R i = [])
    (h150 : S.R 150 = []) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    ∃ v' n, ∃ D : ZMod s → GaussianInt, v'.user = v.user ∧
      n ≤ familyInitializedInteriorCost A p l s t u target rhsExp a b ∧ (cstream A w (chirpLine s D)).length = s*w ∧
      Exec body (familyInitializedInterior hR hQ) (mk v S) n
        (mk v' {S with R := Function.update S.R 132 (cstream A w (chirpLine s D)++S.R 132)}) ∧
      (∀ k, ‖value q (D k)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
        (fun k => (value q (D k)).re) x (1/(2 : ℝ)^target) := by
  dsimp only
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let raw := cstream A w (chirpLine s C)
  let T : Stacks 151 A := {S with R := Function.update S.R 132 (raw++S.R 132)}
  have hw : 2*q+8 = w := by dsimp [q,w,executionPrecision,executionWidth]; omega
  obtain ⟨vi,n₁,hui,hn₁,hei⟩ := initializeInteriorOutput_exec
    (body := fun p : Empty => nomatch p) q s raw borrowed (embDn weightFamilyLegacyReg v) (weightFamilyLegacyBank S)
    (by simpa [groupHeaderValue,q] using hready.masters (119,112) (by simp [groupHeaderCopies]))
    (by simpa [groupHeaderValue] using hready.masters (121,97) (by simp [groupHeaderCopies]))
    hready.source (by simp [raw,hw]) (hready.blank 94 (by decide) (by decide) (by decide))
    (hready.fresh 131 (by simp)) (hready.fresh 134 (by simp)) (hready.fresh 135 (by simp))
  obtain ⟨v₁,hv₁,hu₁,he₁⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    weightFamilyLegacyReg_injective (fun p => nomatch p) hei v rfl S rfl
  have he₁' : Exec body (embProg weightFamilyLegacyReg Empty.elim (initializeInteriorOutput (P₀ := Empty)))
      (mk v S) n₁ (mk v₁ T) := by
    refine he₁.cast rfl ?_
    apply congrArg (mk v₁)
    have hbase : embOvr weightFamilyLegacyReg (weightFamilyLegacyBank S).get S = S := embOvr_stk S
    rw [embOvr_updR weightFamilyLegacyReg_injective,hbase]
    rfl
  have hC' : ∀ k, ‖value q (C k)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp := by
    intro k
    exact (hC k).trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (rhsExponent_le_interiorOutputExponent p l target rhsExp))
  obtain ⟨v₂,n₂,D,hu₂,hn₂,hlen,he₂,hnorm,herror⟩ := familySolveHaloInterior_bounded_spec (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hband has hbs hpad C hC x hx v₁ T borrowed (S.R 132) familyTail C hC' rfl
    (by simpa [T] using h127) (by simpa [T] using h138) (by simpa [T] using ha) (by simpa [T] using hb)
    (by rw [show weightFamilyLegacyBank T = _ from weightFamilyLegacyBank_update_output S _]; exact hready.update_output _)
    (by simpa [T] using hfamily) (by
      intro i hi
      have hi132 : i ≠ 132 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
      simpa [T,hi132] using hcache i hi) (by simpa [T] using h150)
  refine ⟨v₂,n₁+n₂,D,hu₂.trans (hu₁.trans hui),Nat.add_le_add hn₁ hn₂,hlen,
    (Exec.seq he₁' he₂).cast rfl ?_,hnorm,herror⟩
  apply congrArg (mk v₂)
  simp [T,Function.update_idem]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
