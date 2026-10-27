module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageRetireBandTable
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Preserve the complex result, retire its generated table suffix and clear all owned setup pages. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def sharedPageOwnedRegs : List (Fin 240) :=
  [109,115,116,239]++(List.finRange 240).filter (fun i => 154 ≤ i.val ∧ i.val < 224)

@[simp] theorem sharedPageOwnedRegs_mem (i : Fin 240) :
    i ∈ sharedPageOwnedRegs ↔ i = 109 ∨ i = 115 ∨ i = 116 ∨ i = 239 ∨ 154 ≤ i.val ∧ i.val < 224 := by
  simp [sharedPageOwnedRegs]

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 240 Q A U}

def sharedPageRelease : Pr P 240 Q A U :=
  .seq (unaryProduct 121 160 231 232 233)
    (.seq (transfer 231 132 237 233) (.seq sharedPageRetireBandTable
      (.seq (moveR 237 132 id) (.seq (uclear 231) (clearWords sharedPageOwnedRegs)))))

def sharedPageReleaseCost (s N W w : ℕ) (S : Stacks 240 A) : ℕ :=
  retirePackedBandTableCost N W w+12*s*w+9*s+12+
    2*(sharedPageOwnedRegs.map fun i => (S.R i).length).sum+2*sharedPageOwnedRegs.length+1

theorem sharedPageRelease_exec {s rows : ℕ} [NeZero s] (B : Finset (ZMod s)) (W w : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (result tail : List (Fin (A+4))) (hresult : result.length = rows*w)
    (v : HS 240 Q A U) (S : Stacks 240 A)
    (hs : (S.R 121).length = rows) (hW : (S.R 190).length = W)
    (hN : (S.R 116).length = B.card) (hw : (S.R 160).length = w)
    (hsource : S.R 132 = result++(bandTableWords A w B W columns 0++tail))
    (hfresh : ∀ i ∈ ([152,151,131,134,135,136,137,138,231,232,233,237] : List (Fin 240)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ sharedPageReleaseCost rows B.card W w S ∧
      Exec body sharedPageRelease (mk v S) n
        (mk v' {S with R := fun i => if i ∈ sharedPageOwnedRegs then [] else
          (Function.update S.R 132 (result++tail)) i}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := 121) (b := 160) (dst := 231) (t₁ := 232) (t₂ := 233) (by decide) v S
    (hfresh _ (by simp)) (hfresh _ (by simp))
  let S₁ : Stacks 240 A := {S with R := Function.update S.R 231 (List.replicate (rows*w) tick)}
  have he₁' : Exec body (unaryProduct 121 160 231 232 233) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hs,hw,hfresh 231 (by simp),List.append_nil] using he₁
  have hn₁' : n₁ ≤ rows*(4*w+9)+4 := by simpa only [hs,hw] using hn₁
  obtain ⟨v₂,hu₂,he₂⟩ := transfer_exec (body := body) (count := 231) (src := 132) (dst := 237) (tmp := 233)
    (by decide) v₁ S₁ result (bandTableWords A w B W columns 0++tail)
    (by simpa [S₁] using hsource) (by simp [S₁,hresult]) (by simpa [S₁] using hfresh 233 (by simp))
  let S₂ : Stacks 240 A := {S₁ with R := (Function.update (Function.update S₁.R 132
    (bandTableWords A w B W columns 0++tail)) 237 result.reverse)}
  have he₂' : Exec body (transfer 231 132 237 233) (mk v₁ S₁) (4*result.length+4) (mk v₂ S₂) := by
    simpa only [S₂,Function.update_of_ne (by decide : (237 : Fin 240) ≠ 231),S₁,hfresh 237 (by simp),List.append_nil] using he₂
  have hz : ∀ i ∈ ([152,151,131,134,135,136,137,138] : List (Fin 240)), S₂.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [S₂,S₁] using hfresh _ (by simp)
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := sharedPageRetireBandTable_exec (body := body) B W w columns hlen tail v₂ S₂
    (by simpa [S₂,S₁] using hW) (by simpa [S₂,S₁] using hN) (by simpa [S₂,S₁] using hw) (by rfl) hz
  let S₃ : Stacks 240 A := {S₂ with R := Function.update S₂.R 132 tail}
  obtain ⟨v₄,hu₄,he₄⟩ := moveR_exec body 237 132 (by decide) id v₃ S₃
  let S₄ : Stacks 240 A := {S₃ with R := Function.update (Function.update S₃.R 237 []) 132 (result++tail)}
  have he₄' : Exec body (moveR 237 132 id) (mk v₃ S₃) (2*result.length+2) (mk v₄ S₄) := by
    simpa [S₄,S₃,S₂,movedR] using he₄
  obtain ⟨v₅,hu₅,he₅⟩ := uclear_exec body 231 v₄ S₄
  let S₅ : Stacks 240 A := {S₄ with R := Function.update S₄.R 231 []}
  have he₅' : Exec body (uclear 231) (mk v₄ S₄) (2*(rows*w)+2) (mk v₅ S₅) := by
    simpa [S₅,S₄,S₃,S₂,S₁] using he₅
  have hbase : S₅ = {S with R := Function.update S.R 132 (result++tail)} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi231 : i = 231 <;> by_cases hi237 : i = 237 <;> by_cases hi132 : i = 132 <;>
      simp [S₅,S₄,S₃,S₂,S₁,hi231,hi237,hi132,hfresh 231 (by simp),hfresh 237 (by simp)]
  obtain ⟨v₆,hu₆,he₆⟩ := clearWords_exec (body := body) sharedPageOwnedRegs (by decide) v₅ S₅
  have hsum : (sharedPageOwnedRegs.map fun i => (S₅.R i).length).sum =
      (sharedPageOwnedRegs.map fun i => (S.R i).length).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    have hi132 : i ≠ 132 := by
      intro he
      subst i
      simp at hi
    rw [hbase]
    exact congrArg List.length (Function.update_of_ne hi132 _ _)
  refine ⟨v₆,n₁+((4*result.length+4)+(n₃+((2*result.length+2)+((2*(rows*w)+2)+
    (2*(sharedPageOwnedRegs.map fun i => (S.R i).length).sum+2*sharedPageOwnedRegs.length+1))))),
    hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄' (Exec.seq he₅' he₆))))).cast (by rw [hsum]) ?_⟩
  · rw [hresult]
    dsimp only [sharedPageReleaseCost]
    nlinarith only [hn₁',hn₃]
  · apply congrArg (mk v₆)
    rw [hbase]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
