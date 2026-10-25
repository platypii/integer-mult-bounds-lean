module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCanonicalCellRuntime
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightedGeneratorSetup

/-! The complete numerical setup starts with unary controls and a raw RHS.
Its generated state is exactly the construction bank accepted by cell execution. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def unaryCellBank {A : ℕ} (P M q l s t u band L lo : ℕ)
    (rhs borrowed outTail : List (Fin (A + 4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 117 A where
  inp := inp
  out := out
  L := fun _ => []
  R := fun k => if k.val = 101 then List.replicate M tick else
    if k.val = 102 then List.replicate L tick else if k.val = 103 then List.replicate L tick else
    if k.val = 97 then List.replicate s tick else if k.val = 98 then List.replicate t tick else
    if k.val = 99 then List.replicate u tick else if k.val = 100 then List.replicate band tick else
    if k.val = 109 then List.replicate l tick else if k.val = 111 then List.replicate lo tick else
    if k.val = 112 then List.replicate q tick else if k.val = 114 then List.replicate P tick else
    if k.val = 110 then rhs ++ borrowed else if k.val = 93 then outTail else []

theorem unaryCellBank_base_eq {A : ℕ} (P M q l s t u band L lo : ℕ)
    (outs factors rhs borrowed outTail : List (Fin (A + 4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (hweights : weightPage A (2 * q + 8) q P s t u lo L = outs ++ factors) :
    unaryGeometryBase (runtimeWeightBank
      (unaryCellBank P M q l s t u band L lo rhs borrowed outTail inp out) P s t u q L lo) P q M =
      cellConstructionBank P M q l L (integerSetupWidth P q (M + 1) 0)
        outs factors rhs borrowed outTail inp out := by
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases hk : k.val ∈ [93, 94, 97, 98, 99, 100, 101, 102, 103, 109, 110, 111, 112, 114, 115]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
        simp [unaryGeometryBase, setupWidthBank, runtimeWeightBank, unaryCellBank,
          cellConstructionBank, geometryHeaderPorts, Function.update_apply, Fin.ext_iff, h,
          hweights, List.append_assoc]
    · have hn (n : ℕ) (h : n ∈ [93, 94, 97, 98, 99, 100, 101, 102, 103, 109, 110, 111, 112, 114, 115]) :
          k.val ≠ n := fun he => hk (he ▸ h)
      simp [unaryGeometryBase, setupWidthBank, runtimeWeightBank, unaryCellBank,
        cellConstructionBank, geometryHeaderPorts, Function.update_apply, Fin.ext_iff,
        hn 93 (by decide), hn 94 (by decide), hn 97 (by decide), hn 98 (by decide), hn 99 (by decide),
        hn 100 (by decide), hn 101 (by decide), hn 102 (by decide), hn 103 (by decide),
        hn 109 (by decide), hn 110 (by decide), hn 111 (by decide), hn 112 (by decide),
        hn 114 (by decide), hn 115 (by decide)]

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

/-- Unary numerical setup produces the precise construction state consumed by
runtime execution. The output/factor lists specify generated data, not inputs. -/
theorem unaryCellBank_setup_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (P M q l s t u band L lo : ℕ) (hP : 13 ≤ P) (hqMax : q ≤ 2 * (M + 1))
    (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hL : 0 < L) (hLs : L ≤ s) (hlo : lo < s)
    (outs factors rhs borrowed outTail : List (Fin (A + 4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) (v : HS 117 Q A U)
    (hweights : weightPage A (2 * q + 8) q P s t u lo L = outs ++ factors) :
    let S := cellConstructionBank P M q l L (integerSetupWidth P q (M + 1) 0)
      outs factors rhs borrowed outTail inp out
    ∃ v' m, v'.user = v.user ∧ m ≤ weightedGeneratorSetupCost P M q s t u band L lo ∧
      Exec body (weightedGeneratorSetup hQ)
        (mk v (unaryCellBank P M q l s t u band L lo rhs borrowed outTail inp out)) m
        (mk v' (packedGeneratorBank (constructedFactorBank S P s t u band L
          (integerSetupWidth P q (M + 1) 0)) P s t u band L q
          (integerSetupWidth P q (M + 1) 0) (M + 1))) := by
  let B := unaryCellBank P M q l s t u band L lo rhs borrowed outTail inp out
  have hlow (k : Fin 117) (hk : k.val < 93) : B.R k = [] := by
    have hn (n : ℕ) (h : 93 ≤ n) : k.val ≠ n := by omega
    simp [B, unaryCellBank, hn 101 (by decide), hn 102 (by decide), hn 103 (by decide),
      hn 97 (by decide), hn 98 (by decide), hn 99 (by decide), hn 100 (by decide), hn 109 (by decide),
      hn 111 (by decide), hn 112 (by decide), hn 114 (by decide), hn 110 (by decide), hn 93 (by decide)]
  have hc : CClean mul B := by
    intro i
    refine ⟨rfl, hlow (mul i) ?_⟩
    have hi := i.isLt
    dsimp [mul]
    omega
  have hb : ∀ r, B.R (cr r) = [] := by
    intro r
    obtain ⟨hlo, hhi, h93, _⟩ := cr_range r
    have hn (n : ℕ) (h : 97 ≤ n) : (cr r).val ≠ n := by omega
    simp [B, unaryCellBank, hn 101 (by decide), hn 102 (by decide), hn 103 (by decide),
      hn 97 (by decide), hn 98 (by decide), hn 99 (by decide), hn 100 (by decide), hn 109 (by decide),
      hn 111 (by decide), hn 112 (by decide), hn 114 (by decide), hn 110 (by decide), h93]
  obtain ⟨v', m, hu', hm, he⟩ := weightedGeneratorSetup_exec (body := body) (band := band) hQ hA
    hP hqMax hs hst hu hL hLs hlo v B
    (by simp [B, unaryCellBank]) (by simp [B, unaryCellBank]) (by simp [B, unaryCellBank])
    (by simp [B, unaryCellBank]) (by simp [B, unaryCellBank]) (by simp [B, unaryCellBank])
    (by simp [B, unaryCellBank]) (by simp [B, unaryCellBank]) (by simp [B, unaryCellBank])
    (by simp [B, unaryCellBank]) hc hb (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [B, unaryCellBank])
  refine ⟨v', m, hu', hm, he.cast rfl ?_⟩
  unfold weightedGeneratorBank
  rw [show unaryGeometryBase (runtimeWeightBank B P s t u q L lo) P q M =
    cellConstructionBank P M q l L (integerSetupWidth P q (M + 1) 0)
      outs factors rhs borrowed outTail inp out from
    unaryCellBank_base_eq P M q l s t u band L lo outs factors rhs borrowed outTail inp out hweights]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
