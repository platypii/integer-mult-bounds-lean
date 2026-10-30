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



def advancedHaloMetadataPorts : List (Fin 272) := [141,142,149,151,155,156,164,257,261]

/-- Every spectator stack is preserved by the complete metadata step. -/
theorem advancedHaloMetadata_frame (tail cs : List (Fin (A+4))) (S : Stacks 272 A)
    (k : Fin 272) (hk : k ∉ advancedHaloMetadataPorts) :
    (advancedHaloMetadata (V := V) (x := x) (y := y) (L := L) (band := band) tail cs S).R k = S.R k := by
  have hn (i : Fin 272) (hi : i ∈ advancedHaloMetadataPorts) : k ≠ i := by
    intro he
    subst k
    exact hk hi
  unfold advancedHaloMetadata translatedHaloEndpoints
  rw [writeRight_R_off]
  · exact (advancedQueuedHaloHeaders_frame V x y tail cs S k
      (hn 141 (by decide)) (hn 142 (by decide)) (hn 155 (by decide))
      (hn 257 (by decide)) (hn 261 (by decide))).2
  · intro w hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> exact (hn _ (by dsimp; decide)).symm

theorem advancedHaloMetadata_native (tail cs : List (Fin (A+4))) (S : Stacks 272 A)
    (h : PackedHaloNativeClean (embStk (Fin.castLE (by decide : 168 ≤ 272)) S)) :
    PackedHaloNativeClean (embStk (Fin.castLE (by decide : 168 ≤ 272))
      (advancedHaloMetadata (V := V) (x := x) (y := y) (L := L) (band := band) tail cs S)) := by
  intro i hi93 hi110
  let k : Fin 272 := ⟨i.val,by have hi := i.isLt; omega⟩
  have hk : k ∉ advancedHaloMetadataPorts := by
    have hi := i.isLt
    simp only [advancedHaloMetadataPorts,List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at *
    dsimp [k]
    omega
  change (advancedHaloMetadata (V := V) (x := x) (y := y) (L := L) (band := band) tail cs S).R k = []
  rw [advancedHaloMetadata_frame tail cs S k hk]
  exact h i hi93 hi110

theorem advancedHaloMetadata_headers {precision stage q l s t u w : ℕ}
    (hxy : x ≤ y) (tail cs : List (Fin (A+4))) (S : Stacks 272 A)
    (h : PackedHaloRetainedHeaders precision stage q l s t u band x (x+L) V w
      (embStk (Fin.castLE (by decide : 168 ≤ 272)) S)) :
    PackedHaloRetainedHeaders precision stage q l s t u band y (y+L) V w
      (embStk (Fin.castLE (by decide : 168 ≤ 272))
        (advancedHaloMetadata (V := V) (x := x) (y := y) (L := L) (band := band) tail cs S)) := by
  have hlength : (x+L)-x = L := by omega
  have hgeometry : CouplingIntervalMetadata V s t band x (x+L) x L
      (embStk (Fin.castLE (by decide : 168 ≤ 272)) S) := by
    simpa only [hlength] using h.geometry
  constructor
  · apply (advancedQueuedHaloHeaders_masters (V := V) hxy tail cs S h.masters).of_frame
    intro k hk
    simp only [ScalarPlacement.couplingMasterPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [advancedHaloMetadata,translatedHaloEndpoints,writeRight,embStk,Function.comp_apply]
  · have hyLength : (y+L)-y = L := by omega
    simpa only [hyLength] using advancedHaloMetadata_geometry tail cs S hgeometry
  · have hh : (S.R 118).length = stage := h.stage
    change ((advancedHaloMetadata (V := V) (x := x) (y := y) (L := L) (band := band) tail cs S).R 118).length = stage
    rw [advancedHaloMetadata_frame tail cs S 118 (by decide)]
    exact hh
  · have hh : (S.R 120).length = l := h.level
    change ((advancedHaloMetadata (V := V) (x := x) (y := y) (L := L) (band := band) tail cs S).R 120).length = l
    rw [advancedHaloMetadata_frame tail cs S 120 (by decide)]
    exact hh

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


/-- Reusable header/scratch contract of the executed next-origin operation. -/
theorem advanceHaloMetadata_spec {precision stage q l s t u w : ℕ}
    (hxy : x ≤ y) (hfit : y+(L+2*band) < 2^V)
    (tail cs : List (Fin (A+4))) (v : HS 272 Q A U) (S : Stacks 272 A)
    (h : PackedHaloRetainedHeaders precision stage q l s t u band x (x+L) V w
      (embStk (Fin.castLE (by decide : 168 ≤ 272)) S))
    (hsrc : S.R 257 = binSyms V y++tail) (hcount : S.R 261 = tick::cs)
    (hnative : PackedHaloNativeClean (embStk (Fin.castLE (by decide : 168 ≤ 272)) S))
    (hfresh : ∀ k ∈ ([269,270,271] : List (Fin 272)), S.R k = []) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ advanceHaloHeadersCost V (y-x)+(42*V+43) ∧
      Exec body advanceHaloMetadata (mk v S) n (mk v' F) ∧
      PackedHaloRetainedHeaders precision stage q l s t u band y (y+L) V w
        (embStk (Fin.castLE (by decide : 168 ≤ 272)) F) ∧
      PackedHaloNativeClean (embStk (Fin.castLE (by decide : 168 ≤ 272)) F) ∧
      (∀ k ∈ ([269,270,271] : List (Fin 272)), F.R k = []) ∧
      F = advancedHaloMetadata (V := V) (x := x) (y := y) (L := L) (band := band) tail cs S := by
  have hlength : (x+L)-x = L := by omega
  have hgeometry : CouplingIntervalMetadata V s t band x (x+L) x L
      (embStk (Fin.castLE (by decide : 168 ≤ 272)) S) := by
    simpa only [hlength] using h.geometry
  obtain ⟨v',n,hu,hn,he,_⟩ := advanceHaloMetadata_exec (body := body)
    hxy hfit tail cs v S hgeometry hsrc hcount hnative hfresh
  refine ⟨v',_,n,hu,hn,he,advancedHaloMetadata_headers hxy tail cs S h,
    advancedHaloMetadata_native tail cs S hnative,?_,rfl⟩
  intro k hk
  have hoff : k ∉ advancedHaloMetadataPorts := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl <;> decide
  exact (advancedHaloMetadata_frame tail cs S k hoff).trans (hfresh k hk)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
