module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceHaloHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryRetainedPorts

/-! The ordered-origin step on the generated-core ABI. Native scratch is borrowed
and restored; queued halo payloads and publication buffers are untouched. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node ScalarPlacement

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 272 Q A U}

def advanceQueuedHaloHeaders : Pr P 272 Q A U :=
  advanceHaloHeaders 163 257 155 104 105 141 142 261 269 270 271 106

def advancedQueuedHaloHeaders (V x y : ℕ) (tail cs : List (Fin (A+4)))
    (S : Stacks 272 A) : Stacks 272 A :=
  {S with R := (Function.update
    (Function.update (Function.update (Function.update
      (Function.update S.R 141 (List.replicate (y-x) tick++S.R 141))
      142 (List.replicate (y-x) tick++S.R 142)) 155 (binSyms V y)) 257 tail) 261 cs)}

theorem advanceQueuedHaloHeaders_exec {V x y : ℕ} (hxy : x ≤ y) (hy : y < 2^V)
    (tail cs : List (Fin (A+4))) (v : HS 272 Q A U) (S : Stacks 272 A)
    (hwidth : (S.R 163).length = V) (hword : S.R 155 = binSyms V x)
    (hsrc : S.R 257 = binSyms V y++tail) (hcount : S.R 261 = tick::cs)
    (hnative : PackedHaloNativeClean (embStk (Fin.castLE (by decide : 168 ≤ 272)) S))
    (hfresh : ∀ k ∈ ([269,270,271] : List (Fin 272)), S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ advanceHaloHeadersCost V (y-x) ∧
      Exec body advanceQueuedHaloHeaders (mk v S) n
        (mk v' (advancedQueuedHaloHeaders V x y tail cs S)) := by
  apply advanceHaloHeaders_exec (by decide) hxy hy tail cs v S hwidth hword hsrc hcount
  intro k hk
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact hnative 104 (by decide) (by decide)
  · exact hnative 105 (by decide) (by decide)
  · exact hfresh 269 (by decide)
  · exact hfresh 270 (by decide)
  · exact hfresh 271 (by decide)

/-- All registers outside the five owned header/cursor slots retain both sides. -/
theorem advancedQueuedHaloHeaders_frame (V x y : ℕ) (tail cs : List (Fin (A+4)))
    (S : Stacks 272 A) (k : Fin 272)
    (h141 : k ≠ 141) (h142 : k ≠ 142) (h155 : k ≠ 155) (h257 : k ≠ 257) (h261 : k ≠ 261) :
    (advancedQueuedHaloHeaders V x y tail cs S).L k = S.L k ∧
      (advancedQueuedHaloHeaders V x y tail cs S).R k = S.R k := by
  exact ⟨rfl,by simp only [advancedQueuedHaloHeaders,Function.update_of_ne h141,
    Function.update_of_ne h142,Function.update_of_ne h155,Function.update_of_ne h257,
    Function.update_of_ne h261]⟩

theorem advancedQueuedHaloHeaders_masters {precision q w s t u band V x y L : ℕ}
    (hxy : x ≤ y) (tail cs : List (Fin (A+4))) (S : Stacks 272 A)
    (h : CouplingMasterHeaders precision q w s t u band x (x+L)
      (embStk (Fin.castLE (by decide : 168 ≤ 272)) S)) :
    CouplingMasterHeaders precision q w s t u band y (y+L)
      (embStk (Fin.castLE (by decide : 168 ≤ 272))
        (advancedQueuedHaloHeaders V x y tail cs S)) := by
  constructor
  · simpa [advancedQueuedHaloHeaders,embStk,Function.comp_apply] using h.precision
  · simpa [advancedQueuedHaloHeaders,embStk,Function.comp_apply] using h.fraction
  · simpa [advancedQueuedHaloHeaders,embStk,Function.comp_apply] using h.axis
  · simpa [advancedQueuedHaloHeaders,embStk,Function.comp_apply] using h.period
  · simpa [advancedQueuedHaloHeaders,embStk,Function.comp_apply] using h.parameter
  · simpa [advancedQueuedHaloHeaders,embStk,Function.comp_apply] using h.bandwidth
  · have hx : (S.R 141).length = x := h.lower
    simp only [embStk,Function.comp_apply,advancedQueuedHaloHeaders]
    simp [hx,Nat.sub_add_cancel hxy]
  · have hx : (S.R 142).length = x+L := h.upper
    simp only [embStk,Function.comp_apply,advancedQueuedHaloHeaders]
    simp only [show (Fin.castLE (by decide : 168 ≤ 272) (142 : Fin 168)) = 142 by decide,
      Function.update_of_ne (by decide : (142 : Fin 272) ≠ 261),
      Function.update_of_ne (by decide : (142 : Fin 272) ≠ 257),
      Function.update_of_ne (by decide : (142 : Fin 272) ≠ 155),Function.update_self,
      List.length_append,List.length_replicate,hx]
    omega
  · simpa [advancedQueuedHaloHeaders,embStk,Function.comp_apply] using h.width

theorem advancedQueuedHaloHeaders_native {V x y : ℕ} (tail cs : List (Fin (A+4)))
    (S : Stacks 272 A)
    (h : PackedHaloNativeClean (embStk (Fin.castLE (by decide : 168 ≤ 272)) S)) :
    PackedHaloNativeClean (embStk (Fin.castLE (by decide : 168 ≤ 272))
      (advancedQueuedHaloHeaders V x y tail cs S)) := by
  intro i hi93 hi110
  let k : Fin 272 := ⟨i.val,by have hi := i.isLt; omega⟩
  have hk : k.val < 117 := i.isLt
  have hn (n : Fin 272) (hn : 117 ≤ n.val) : k ≠ n := by
    intro he
    have hv := congrArg (fun j : Fin 272 => j.val) he
    omega
  change (advancedQueuedHaloHeaders V x y tail cs S).R k = []
  rw [(advancedQueuedHaloHeaders_frame V x y tail cs S k
    (hn 141 (by decide)) (hn 142 (by decide)) (hn 155 (by decide))
    (hn 257 (by decide)) (hn 261 (by decide))).2]
  exact h i hi93 hi110

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
