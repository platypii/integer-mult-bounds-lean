module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeHaloLengthKeys
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloReady

/-! Reuse the existing executed key initializer in the packed caller bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def initializePackedHaloKeys : Pr P 168 Q A U :=
  embProg packedHeaderReg Empty.elim (initializeHaloLengthKeys (P₀ := Empty))

theorem initializePackedHaloKeys_exec (precision stage q l s t u band a b : ℕ)
    (hP : 13 ≤ precision) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hband : band ≤ s) (hab : a ≤ b) (hb : b ≤ s) (hA : 4 ≤ A)
    (v : HS 168 Q A U) (S : Stacks 168 A) (input E outputTail : List (Fin (A+4)))
    (hnative : embStk packedCellCoreReg S = releasedCellBank [] input (S.R 93) S.inp S.out)
    (hmasters : ∀ r ∈ groupHeaderCopies, (S.R (packedHeaderReg r.1)).length =
      groupHeaderValue precision stage q l s t u band 0 r.1)
    (ha : (S.R 141).length = a) (hb' : (S.R 142).length = b)
    (hmeta : CouplingIntervalMetadata (weightWorkspaceWidth precision q (2*q+8) t u) s t band a b a (b-a) S)
    (h157 : (S.R 157).length ≤ weightWorkspaceWidth precision q (2*q+8) t u)
    (houtput : S.R 132 = E++outputTail) (hE : E.length = (b-a)*(2*q+8))
    (hfresh : ∀ k ∈ [(125 : Fin 168),127,130,133,138,129,131,134,135,136,140,153,166], S.R k = []) :
    let V := weightWorkspaceWidth precision q (2*q+8) t u
    let keys := haloPositiveLengthPackets A V s t band a b
    let K := (haloLengthKeys s t band a b).length
    let F := {S with R := initializedKeyRuntimeR S.R V (2*q+8) K keys}
    ∃ v' m, v'.user = v.user ∧ m ≤ initializeHaloLengthKeysCost precision stage q l s t u band a b ∧
      Exec body initializePackedHaloKeys (mk v S) m (mk v' F) ∧
      PackedHaloReady precision stage q l s t u band a b V (2*q+8) input E outputTail F := by
  dsimp only
  let V := weightWorkspaceWidth precision q (2*q+8) t u
  let keys := haloPositiveLengthPackets A V s t band a b
  let K := (haloLengthKeys s t band a b).length
  let T := embStk packedHeaderReg S
  have hleft : ∀ k : Fin 144, k.val < 117 → T.L k = [] := by
    intro k hk
    let i : Fin 117 := ⟨k.val,hk⟩
    simpa [T,embStk,packedHeaderReg,packedCellCoreReg,releasedCellBank,i] using
      congrArg (fun B : Stacks 117 A => B.L i) hnative
  have hblank : ∀ k : Fin 144, k.val < 117 → k ≠ 93 → k ≠ 110 → T.R k = [] := by
    intro k hk h93 h110
    let i : Fin 117 := ⟨k.val,hk⟩
    have h93' : k.val ≠ 93 := fun he => h93 (Fin.ext he)
    have h110' : k.val ≠ 110 := fun he => h110 (Fin.ext he)
    simpa [T,embStk,packedHeaderReg,packedCellCoreReg,releasedCellBank,i,h93',h110'] using
      congrArg (fun B : Stacks 117 A => B.R i) hnative
  obtain ⟨v₁,m,hu₁,hm,he⟩ := initializeHaloLengthKeys_exec (body := fun p : Empty => nomatch p)
    precision stage q l s t u band a b hP hs hst hu hband (hab.trans hb) hb hA
    (embDn packedHeaderReg v) T hmasters ha hb' hleft hblank
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> exact hfresh _ (by simp [packedHeaderReg]))
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    packedHeaderReg_injective (fun p => nomatch p) he v rfl S rfl
  let F : Stacks 168 A := {S with R := initializedKeyRuntimeR S.R V (2*q+8) K keys}
  have hfinal : embOvr packedHeaderReg
      ({T with R := initializedKeyRuntimeR T.R V (2*q+8) K keys} : Stacks 144 A).get S = F := by
    let T₁ : Stacks 144 A := {T with R := Function.update T.R 125 (List.replicate V tick)}
    let T₂ : Stacks 144 A := {T₁ with R := Function.update T₁.R 126 (keys++T.R 126)}
    let T₃ : Stacks 144 A := {T₂ with R := Function.update T₂.R 127 (List.replicate K tick)}
    change embOvr packedHeaderReg ({T₃ with R := Function.update T₃.R 130 (List.replicate (2*q+8) tick)} : Stacks 144 A).get S = F
    rw [embOvr_updR packedHeaderReg_injective T₃ S 130,
      embOvr_updR packedHeaderReg_injective T₂ S 127,
      embOvr_updR packedHeaderReg_injective T₁ S 126,
      embOvr_updR packedHeaderReg_injective T S 125,embOvr_stk]
    rfl
  refine ⟨v₂,m,hu₂.trans hu₁,hm,he₂.cast rfl (congrArg (mk v₂) hfinal),?_⟩
  have hoff (k : Fin 168) (h125 : k ≠ 125) (h126 : k ≠ 126) (h127 : k ≠ 127) (h130 : k ≠ 130) :
      F.R k = S.R k := by simp [F,initializedKeyRuntimeR,h125,h126,h127,h130]
  constructor
  · have hp : embStk packedCellCoreReg F = embStk packedCellCoreReg S := by
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      apply hoff
      all_goals intro he
      all_goals have hv := congrArg (fun j : Fin 168 => j.val) he
      all_goals have hk := k.isLt
      all_goals simp only [packedCellCoreReg] at hv
      all_goals omega
    change embStk packedCellCoreReg F = releasedCellBank [] input (F.R 93) F.inp F.out
    rw [hp]
    simpa [F,initializedKeyRuntimeR] using hnative
  · intro r hr _
    have hn : packedHeaderReg r.1 ≠ 125 ∧ packedHeaderReg r.1 ≠ 126 ∧
        packedHeaderReg r.1 ≠ 127 ∧ packedHeaderReg r.1 ≠ 130 := by
      simp only [groupHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hoff _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2]; exact hmasters r hr
  · constructor
    · rw [hoff 163 (by decide) (by decide) (by decide) (by decide)]; exact hmeta.width
    · intro k hk
      have hn : k ≠ 125 ∧ k ≠ 126 ∧ k ≠ 127 ∧ k ≠ 130 := by
        simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [hoff k hn.1 hn.2.1 hn.2.2.1 hn.2.2.2]; exact hmeta.encoded k hk
  · simp [F,initializedKeyRuntimeR]
  · rw [hoff 128 (by decide) (by decide) (by decide) (by decide)]
    have hh := hmasters (128,102) (by decide)
    have hz : (S.R 128).length = 0 := by simpa [groupHeaderValue,packedHeaderReg] using hh
    omega
  · rw [hoff 157 (by decide) (by decide) (by decide) (by decide)]; exact h157
  · simp [F,initializedKeyRuntimeR]
  · rw [hoff 132 (by decide) (by decide) (by decide) (by decide)]; exact houtput
  · exact hE
  · intro k hk
    have hn : k ≠ 125 ∧ k ≠ 126 ∧ k ≠ 127 ∧ k ≠ 130 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hoff k hn.1 hn.2.1 hn.2.2.1 hn.2.2.2]
    exact hfresh k (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
      rcases hk with h | h | h | h | h | h | h | h | h <;> simp_all)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
