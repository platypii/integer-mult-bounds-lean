module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilySolveHaloInterior

/-! Execute numerical family setup followed by a complete interior pass. The
family is generated from caller masters and remains retained for reuse. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 151 Q A U}

theorem weightFamilyLegacyBank_update_high {A : ℕ} (S : Stacks 151 A) (i : Fin 151)
    (hi : 144 ≤ i.val) (xs : List (Fin (A+4))) :
    weightFamilyLegacyBank {S with R := Function.update S.R i xs} = weightFamilyLegacyBank S := by
  refine Stacks.ext rfl rfl rfl ?_
  funext j
  change Function.update S.R i xs (weightFamilyLegacyReg j) = S.R (weightFamilyLegacyReg j)
  exact Function.update_of_ne (weightFamilyLegacyReg_off i hi j) _ _

noncomputable def generatedFamilyHaloInterior (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 151 Q A U :=
  .seq prepareHaloWeightFamily (familySolveHaloInterior hR hQ)

theorem generatedFamilyHaloInterior_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (v : HS 151 Q A U) (S : Stacks 151 A) (borrowed E outputTail : List (Fin (A+4)))
    (hE : E.length = s*executionWidth p l target rhsExp) (hdst : S.R 132 = E++outputTail)
    (h127 : S.R 127 = []) (h138 : S.R 138 = [])
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l target rhsExp) (chirpLine s C)++borrowed) (weightFamilyLegacyBank S))
    (hcache : ∀ i ∈ ([(144 : Fin 151),145,146,147,149] : List (Fin 151)), S.R i = [])
    (h150 : S.R 150 = []) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    ∃ v' n, ∃ E' : List (Fin (A+4)), v'.user = v.user ∧
      n ≤ prepareHaloWeightFamilyCost A (2^15*p) (executionStagePrecision p l target rhsExp+1)
        q l s t u (PhaseCellBand.width p u) a b+familySolveHaloInteriorCost A p l s t u target rhsExp a b ∧ E'.length = s*w ∧
      Exec body (generatedFamilyHaloInterior hR hQ) (mk v S) n
        (mk v' { S with R := (Function.update (Function.update S.R 148
          (weightKeyFamily (haloWeightKeyPages A w q (2^15*p) s t u (PhaseCellBand.width p u) a b
            (haloLengthKeys s t (PhaseCellBand.width p u) a b))++S.R 148)) 132 (E'++outputTail)) }) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
        (publishedCellRead q w (0 : ZMod s) (E'++outputTail)) x (1/(2 : ℝ)^target) ∧
      (EncodedRange A w q (interiorOutputExponent p l target rhsExp) E →
        EncodedRange A w q (interiorOutputExponent p l target rhsExp) E') := by
  dsimp only
  let P := 2^15*p
  let N := executionStagePrecision p l target rhsExp+1
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  let pages := haloWeightKeyPages A w q P s t u band a b (haloLengthKeys s t band a b)
  have hw : 2*q+8 = w := by dsimp [q,w,executionPrecision,executionWidth]; omega
  have hP : 13 ≤ P := by dsimp [P]; omega
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := prepareHaloWeightFamily_exec (body := body)
    P N q l s t u band a b hP hst hu (PhaseCellBand.width_pos p u) hband has hbs (by omega)
    v S (cstream A w (chirpLine s C)++borrowed) hready haMaster hbMaster h127 h138 h150 hcache
  simp only [hw] at he₁
  let T : Stacks 151 A := {S with R := Function.update S.R 148 (weightKeyFamily pages++S.R 148)}
  have ht : weightFamilyLegacyBank T = weightFamilyLegacyBank S := weightFamilyLegacyBank_update_high S 148 (by decide) _
  obtain ⟨v₂,n₂,E',hu₂,hn₂,hlen,he₂,herror,hbound⟩ := familySolveHaloInterior_spec (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hband has hbs hpad C hC x hx v₁ T borrowed E outputTail (S.R 148)
    hE (by simpa [T] using hdst) (by simpa [T] using h127) (by simpa [T] using h138)
    (by simpa [T] using haMaster) (by simpa [T] using hbMaster) (by rw [ht]; exact hready)
    (by simp [T,pages,P,q,w,band]) (by
      intro i hi
      have hi148 : i ≠ 148 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
      simpa [T,hi148] using hcache i hi) (by simpa [T] using h150)
  exact ⟨v₂,n₁+n₂,E',hu₂.trans hu₁,by dsimp only [P,N,q,band] at hn₁ ⊢; omega,hlen,Exec.seq he₁ he₂,herror,hbound⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
