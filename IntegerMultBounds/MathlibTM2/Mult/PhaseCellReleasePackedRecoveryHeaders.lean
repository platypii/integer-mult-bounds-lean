module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryInteriorPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloReady
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Release recovery's private runtime headers at their proved sizes, without
touching the retained numerical bank or the published local solution. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

def packedRecoveryHeaderPorts : List (Fin 248) := [242,243,244,247]

def releasePackedRecoveryHeaders : Pr P 248 Q A U := clearWords packedRecoveryHeaderPorts

def releasedPackedRecoveryHeaders {A : ℕ} (S : Stacks 248 A) : Stacks 248 A :=
  {S with R := fun k => if k ∈ packedRecoveryHeaderPorts then [] else S.R k}

theorem releasedPackedRecoveryHeaders_low {A : ℕ} (S : Stacks 248 A)
    (k : Fin 248) (hk : k.val < 242) :
    (releasedPackedRecoveryHeaders S).R k = S.R k := by
  have hn : k ∉ packedRecoveryHeaderPorts := by
    simp only [packedRecoveryHeaderPorts,List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff]
    omega
  simp only [releasedPackedRecoveryHeaders,if_neg hn]

theorem releasedPackedRecoveryHeaders_prefix {A : ℕ} (S : Stacks 248 A) :
    embStk (Fin.castLE (by decide : 242 ≤ 248)) (releasedPackedRecoveryHeaders S) =
      embStk (Fin.castLE (by decide : 242 ≤ 248)) S := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  exact releasedPackedRecoveryHeaders_low S _ i.isLt

theorem releasePackedRecoveryHeaders_exec
    {precision stage q l s t u band a b V w : ℕ}
    {input E outputTail : List (Fin (A+4))}
    (v : HS 248 Q A U) (S : Stacks 248 A)
    (h : PackedHaloReady precision stage q l s t u band a b V w input E outputTail
      (embStk packedRecoveryInteriorReg S)) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 2*(2*V+s+w)+9 ∧
      Exec body releasePackedRecoveryHeaders (mk v S) n
        (mk v' (releasedPackedRecoveryHeaders S)) := by
  have h242 : (S.R 242).length = V := h.keyWidth
  have h243 : (S.R 243).length ≤ s := h.unaryLengthBound
  have h244 : (S.R 244).length = w := h.wordWidth
  have h247 : (S.R 247).length ≤ V := h.binaryLengthBound
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) packedRecoveryHeaderPorts (by decide) v S
  refine ⟨v',_,hu,?_,he⟩
  simp only [packedRecoveryHeaderPorts,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    List.length_cons,List.length_nil,h242,h244]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
