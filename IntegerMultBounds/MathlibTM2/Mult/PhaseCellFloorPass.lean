module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFloorWord
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicSlice

/-! # Execute floor encoding of an owned word stream

The existing structural word-pass executor supplies the loop. Every counter
and work register restores; only the owned source stream changes width.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem floorSlicePass_exec {src dst skip width rest tmp : Fin T}
    (hreg : [src, dst, skip, width, rest, tmp].Nodup)
    (W a w e : ℕ) (hW : 1 ≤ W) (hwidth : W = a + w + e)
    (xs : List GaussianInt) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A W xs) (hdst : S.R dst = [])
    (hg : FloorSliceReady skip width rest tmp a w e S.R) :
    ∃ v', v'.user = v.user ∧
      Exec body (topPass src dst (floorSliceWord src dst skip width rest tmp)) (mk v S)
        (xs.length * (4 * W + 2 * w + 14) + 4)
        (mk v' { S with R := (Function.update S.R src
          (cstream A w (xs.map (fun z => (⟨z.re / (2 : ℤ) ^ a, z.im / (2 : ℤ) ^ a⟩ : GaussianInt))))) }) := by
  have hreg' := hreg
  regs_ne hreg'
  have hspec : TopWordSpec body (floorSliceWord src dst skip width rest tmp) src dst
      (FloorSliceReady skip width rest tmp a w e) W (fun xs => (xs.drop a).take w) (4 * W + 13) := by
    simpa only [hwidth] using floorSliceWord_spec (body := body) hreg a w e
  have hmap : (xs.map (csyms A W)).map (fun ys => (ys.drop a).take w) =
      (xs.map (fun z => (⟨z.re / (2 : ℤ) ^ a, z.im / (2 : ℤ) ^ a⟩ : GaussianInt))).map (csyms A w) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro z _
    exact csyms_floor_div_slice A W a w (by omega) z
  obtain ⟨v', hu, he⟩ := topPass_exec body ‹src ≠ dst› (floorSliceReady_frame hreg a w e) hW hspec
    (xs.map (csyms A W)) v S
    (by intro ys hy; obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy; simp [csyms])
    (by simpa only [cstream, List.flatMap_def] using hsrc) hdst hg
  rw [hmap] at he
  refine ⟨v', hu, he.cast ?_ rfl⟩
  simp only [List.length_map]
  change 1 + (xs.length * (4 * W + 13 + 1) + 1) +
    (2 * (cstream A w (xs.map (fun z => (⟨z.re / (2 : ℤ) ^ a, z.im / (2 : ℤ) ^ a⟩ : GaussianInt)))).length + 2) = _
  simp only [length_cstream, List.length_map]
  ring

/-- The actual dyadic floor words are emitted exactly, including negative numerators. -/
theorem dyadicPass_exec {src dst skip width rest tmp : Fin T}
    (hreg : [src, dst, skip, width, rest, tmp].Nodup)
    (W w q r : ℕ) (hW : 1 ≤ W) (hqr : q ≤ r) (hwidth : r - q + w ≤ W)
    (zs : List ℤ) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A W (zs.map (fun z => (⟨z, 0⟩ : GaussianInt)))) (hdst : S.R dst = [])
    (hg : FloorSliceReady skip width rest tmp (r - q) w (W - (r - q + w)) S.R) :
    ∃ v', v'.user = v.user ∧
      Exec body (topPass src dst (floorSliceWord src dst skip width rest tmp)) (mk v S)
        (zs.length * (4 * W + 2 * w + 14) + 4)
        (mk v' { S with R := Function.update S.R src (cstream A w (zs.map (dyadicWord q r))) }) := by
  have hsum : W = (r - q) + w + (W - (r - q + w)) := by omega
  obtain ⟨v', hu, he⟩ := floorSlicePass_exec (body := body) hreg W (r - q) w (W - (r - q + w)) hW hsum
    (zs.map (fun z => (⟨z, 0⟩ : GaussianInt))) v S hsrc hdst hg
  have hmap : (zs.map (fun z => (⟨z, 0⟩ : GaussianInt))).map
      (fun z => (⟨z.re / (2 : ℤ) ^ (r - q), z.im / (2 : ℤ) ^ (r - q)⟩ : GaussianInt)) =
        zs.map (dyadicWord q r) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro z _
    simp [dyadicWord_ediv hqr]
  exact ⟨v', hu, by simpa only [List.length_map, hmap] using he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
