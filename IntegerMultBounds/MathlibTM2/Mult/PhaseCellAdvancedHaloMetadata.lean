module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRefreshHaloEndpoints
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceQueuedHaloHeaders

/-! The complete geometry invariant after advancing an ordered halo's headers
and translating its endpoint bank. Ambient dimensions and the local length are
retained; only coordinate-dependent words change. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node

variable {A V s t band x y L : ℕ}

def advancedHaloMetadata (tail cs : List (Fin (A+4))) (S : Stacks 272 A) : Stacks 272 A :=
  translatedHaloEndpoints V y L band (advancedQueuedHaloHeaders V x y tail cs S)

theorem advancedHaloMetadata_geometry (tail cs : List (Fin (A+4))) (S : Stacks 272 A)
    (h : CouplingIntervalMetadata V s t band x (x+L) x L
      (embStk (Fin.castLE (by decide : 168 ≤ 272)) S)) :
    CouplingIntervalMetadata V s t band y (y+L) y L
      (embStk (Fin.castLE (by decide : 168 ≤ 272))
        (advancedHaloMetadata (V := V) (x := x) (y := y) (L := L) (band := band) tail cs S)) := by
  constructor
  · simpa [advancedHaloMetadata,translatedHaloEndpoints,writeRight,
      advancedQueuedHaloHeaders,embStk,Function.comp_apply] using h.width
  · intro k hk
    have hold := h.encoded k hk
    simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | (simp [advancedHaloMetadata,translatedHaloEndpoints,writeRight,
          advancedQueuedHaloHeaders,embStk,Function.comp_apply,couplingIntervalValue]; done)
      | simpa [advancedHaloMetadata,translatedHaloEndpoints,writeRight,
          advancedQueuedHaloHeaders,embStk,Function.comp_apply,couplingIntervalValue] using hold


variable {Q : ℕ} {P U : Type} {body : P → Pr P 272 Q A U}

def advanceHaloMetadata : Pr P 272 Q A U :=
  .seq advanceQueuedHaloHeaders refreshHaloEndpoints

theorem advanceHaloMetadata_exec (hxy : x ≤ y) (hfit : y+(L+2*band) < 2^V)
    (tail cs : List (Fin (A+4))) (v : HS 272 Q A U) (S : Stacks 272 A)
    (h : CouplingIntervalMetadata V s t band x (x+L) x L
      (embStk (Fin.castLE (by decide : 168 ≤ 272)) S))
    (hsrc : S.R 257 = binSyms V y++tail) (hcount : S.R 261 = tick::cs)
    (hnative : PackedHaloNativeClean (embStk (Fin.castLE (by decide : 168 ≤ 272)) S))
    (hfresh : ∀ k ∈ ([269,270,271] : List (Fin 272)), S.R k = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ advanceHaloHeadersCost V (y-x)+(42*V+43) ∧
      Exec body advanceHaloMetadata (mk v S) n
        (mk v' (advancedHaloMetadata (V := V) (x := x) (y := y) (L := L) (band := band) tail cs S)) ∧
      CouplingIntervalMetadata V s t band y (y+L) y L
        (embStk (Fin.castLE (by decide : 168 ≤ 272))
          (advancedHaloMetadata (V := V) (x := x) (y := y) (L := L) (band := band) tail cs S)) := by
  have h155 : S.R 155 = binSyms V x := by
    simpa [embStk,Function.comp_apply,couplingIntervalValue] using
      h.encoded 155 (by simp [couplingIntervalPorts])
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := advanceQueuedHaloHeaders_exec (body := body) hxy (by omega)
    tail cs v S h.width h155 hsrc hcount hnative hfresh
  let H := advancedQueuedHaloHeaders V x y tail cs S
  have hencoded (k : Fin 168) (hk : k ∈ couplingIntervalPorts) :
      S.R (Fin.castLE (by decide : 168 ≤ 272) k) =
        binSyms V (couplingIntervalValue s t band x (x+L) x L k) := h.encoded k hk
  obtain ⟨v₂,hu₂,he₂⟩ := refreshHaloEndpoints_exec (body := body) hxy hfit v₁ H
    (by simp [H,advancedQueuedHaloHeaders])
    (by simpa [H,advancedQueuedHaloHeaders,couplingIntervalValue] using hencoded 149 (by simp [couplingIntervalPorts]))
    (by simpa [H,advancedQueuedHaloHeaders,couplingIntervalValue] using hencoded 151 (by simp [couplingIntervalPorts]))
    (by simpa [H,advancedQueuedHaloHeaders,couplingIntervalValue] using hencoded 156 (by simp [couplingIntervalPorts]))
    (by simpa [H,advancedQueuedHaloHeaders,couplingIntervalValue] using hencoded 164 (by simp [couplingIntervalPorts]))
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · have hn104 : S.R 104 = [] := hnative 104 (by decide) (by decide)
        simpa [H,advancedQueuedHaloHeaders] using hn104
      · simpa [H,advancedQueuedHaloHeaders] using hfresh 269 (by decide)
      · simpa [H,advancedQueuedHaloHeaders] using hfresh 270 (by decide)
      · simpa [H,advancedQueuedHaloHeaders] using hfresh 271 (by decide))
  exact ⟨v₂,n₁+(42*V+43),hu₂.trans hu₁,Nat.add_le_add_right hn₁ _,
    Exec.seq he₁ he₂,advancedHaloMetadata_geometry tail cs S h⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
