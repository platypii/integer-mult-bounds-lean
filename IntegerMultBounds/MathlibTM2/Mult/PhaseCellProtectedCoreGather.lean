module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellQueuedCoreGather
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWordWidth

/-! Gather directly into the solver queues while protecting its native bank.
Geometry and the temporary word-width header live outside the solver workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 272 Q A U}

def protectedCoreGatherPerm : Equiv.Perm (Fin 272) :=
  (Equiv.swap 108 256).trans ((Equiv.swap 109 257).trans ((Equiv.swap 116 261).trans
    ((Equiv.swap 91 262).trans ((Equiv.swap 145 264).trans ((Equiv.swap 150 265).trans
      ((Equiv.swap 152 266).trans ((Equiv.swap 94 267).trans (Equiv.swap 154 268))))))))

def protectedCoreGatherReg (i : Fin 168) : Fin 272 :=
  protectedCoreGatherPerm (Fin.castLE (by decide) i)

theorem protectedCoreGatherReg_injective : Function.Injective protectedCoreGatherReg :=
  protectedCoreGatherPerm.injective.comp (by
    intro i j he
    exact Fin.ext (congrArg (fun k : Fin 272 => k.val) he))

def protectedCoreGather : Pr P 272 Q A U :=
  .seq (generateWordWidth 119 267 104)
    (.seq (queuedCoreGather protectedCoreGatherReg) (uclear 267))

def protectedCoreGatherCost (V q s width radius L : ℕ) : ℕ :=
  (8*q+9)+queuedCoreGatherCost V s width radius L (2*q+8)+(2*(2*q+8)+2)

theorem protectedCoreGather_spec {V q s width radius L : ℕ}
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V) (hLfit : L < 2^V)
    (hwV : 2*q+8 < 2^V) (hvol : s*(2*q+8) < 2^V) (hA : 4 ≤ A) (hVpos : 0 < V)
    (hgroup : 0 < (coreGatherIndices s width radius L).length)
    (v : HS 272 Q A U) (M : Stacks 272 A)
    (h163 : (M.R 163).length = V) (hq : (M.R 119).length = q)
    (hs : M.R 264 = binSyms V s) (hw : M.R 265 = binSyms V width)
    (hr : M.R 266 = binSyms V radius) (hL : M.R 165 = binSyms V L) (hz : M.R 268 = [])
    (hblank : ∀ i : Fin 168, i.val < 31 → M.R (protectedCoreGatherReg i) = [])
    (hclean : ∀ i ∈ [(88 : Fin 168),89,90,92,93,95,96,97,98,99,100,101,102,103,104,105,106,115],
      M.R (protectedCoreGatherReg i) = [])
    (h261 : M.R 261 = []) (h262 : M.R 262 = []) (h267 : M.R 267 = [])
    (C : ZMod s → GaussianInt) (hsource : M.R 110 = cstream A (2*q+8) (chirpLine s C)) :
    ∃ v' n, v'.user = v.user ∧ n ≤ protectedCoreGatherCost V q s width radius L ∧
      Exec body protectedCoreGather (mk v M) n
        (mk v' {M with R := (Function.update (Function.update (Function.update M.R
          256 ((coreGatherIndices s width radius L).flatMap
            (fun k => cstream A (2*q+8) (packedInterval (coreStart width k-radius) L C))++M.R 256))
          257 ((coreGatherIndices s width radius L).flatMap
            (fun k => binSyms V (coreStart width k-radius))++M.R 257))
          261 (List.replicate (coreGatherIndices s width radius L).length tick))}) := by
  have hreg94 : protectedCoreGatherReg 94 = 267 := by decide
  have hreg104 : protectedCoreGatherReg 104 = 104 := by decide
  have h104 : M.R 104 = [] := by simpa only [hreg104] using hclean 104 (by simp)
  obtain ⟨v₀,hu₀,he₀⟩ := generateWordWidth_exec (body := body)
    (precision := 119) (width := 267) (tmp := 104) (by decide) q v M hq h267 h104
  let M₀ : Stacks 272 A := {M with R := Function.update M.R 267 (List.replicate (2*q+8) tick)}
  let S := embStk protectedCoreGatherReg M₀
  have hread (i : Fin 168) (hi : i ≠ 94) : S.R i = M.R (protectedCoreGatherReg i) := by
    have hn : protectedCoreGatherReg i ≠ 267 := by
      intro he
      exact hi (protectedCoreGatherReg_injective (he.trans hreg94.symm))
    simp only [S,embStk,Function.comp_apply,M₀,Function.update_of_ne hn]
  have hcleanS : ∀ i ∈ [(88 : Fin 168),89,90,92,93,95,96,97,98,99,100,101,102,103,104,105,106,115], S.R i = [] := by
    intro i hi
    rw [hread i (by intro he; subst i; norm_num at hi)]
    exact hclean i hi
  have hreg108 : protectedCoreGatherReg 108 = 256 := by decide
  have hreg109 : protectedCoreGatherReg 109 = 257 := by decide
  have hreg116 : protectedCoreGatherReg 116 = 261 := by decide
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := queuedCoreGather_spec (body := body)
    protectedCoreGatherReg protectedCoreGatherReg_injective hwidth hwide hLfit hwV hvol hA hVpos hgroup
    v₀ M₀ S rfl
    (by rw [hread 163 (by decide),show protectedCoreGatherReg 163 = 163 by decide]; exact h163)
    (hcleanS 115 (by simp)) (hcleanS 103 (by simp)) (hcleanS 105 (by simp))
    (by rw [hread 145 (by decide),show protectedCoreGatherReg 145 = 264 by decide]; exact hs)
    (by rw [hread 150 (by decide),show protectedCoreGatherReg 150 = 265 by decide]; exact hw)
    (by rw [hread 152 (by decide),show protectedCoreGatherReg 152 = 266 by decide]; exact hr)
    (by rw [hread 165 (by decide),show protectedCoreGatherReg 165 = 165 by decide]; exact hL)
    (by rw [hread 154 (by decide),show protectedCoreGatherReg 154 = 268 by decide]; exact hz)
    (by intro i hi; rw [hread i (by intro he; subst i; norm_num at hi)]; exact hblank i hi)
    (hcleanS 104 (by simp)) (hcleanS 106 (by simp))
    (by rw [hread 116 (by decide),hreg116]; exact h261) C
    (by rw [hread 110 (by decide),show protectedCoreGatherReg 110 = 110 by decide]; exact hsource)
    (by simp only [S,embStk,Function.comp_apply,hreg94,M₀,Function.update_self,List.length_replicate])
    (by rw [hread 91 (by decide),show protectedCoreGatherReg 91 = 262 by decide]; exact h262)
    (by intro i hi; exact hcleanS i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto))
    (by intro i hi; exact hcleanS i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto))
  let batch := (coreGatherIndices s width radius L).flatMap
    (fun k => cstream A (2*q+8) (packedInterval (coreStart width k-radius) L C))
  let origins := (coreGatherIndices s width radius L).flatMap
    (fun k => binSyms (A := A) V (coreStart width k-radius))
  let count := List.replicate (coreGatherIndices s width radius L).length (tick : Fin (A+4))
  let M₁ : Stacks 272 A := {M₀ with R := (Function.update (Function.update (Function.update M₀.R
    256 (batch++M₀.R 256)) 257 (origins++M₀.R 257)) 261 count)}
  have he₁' : Exec body (queuedCoreGather protectedCoreGatherReg) (mk v₀ M₀) n₁ (mk v₁ M₁) := by
    simpa only [hreg108,hreg109,hreg116] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := uclear_exec body 267 v₁ M₁
  have hlen : (M₁.R 267).length = 2*q+8 := by simp [M₁,M₀]
  refine ⟨v₂,(8*q+9)+(n₁+(2*(2*q+8)+2)),hu₂.trans (hu₁.trans hu₀),?_,
    (Exec.seq he₀ (Exec.seq he₁' he₂)).cast (by rw [hlen]) ?_⟩
  · unfold protectedCoreGatherCost
    omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h256 : i = 256 <;> by_cases h257 : i = 257 <;>
      by_cases h261i : i = 261 <;> by_cases h267i : i = 267 <;>
      simp [M₁,M₀,h256,h257,h261i,h267i,h267,batch,origins,count]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
