module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFloorPass

/-! Common-width packets enter a key-specific numerical bank by exact low-bit
cropping. This changes representation width, not fixed-point scale. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Consume each common-width packet and retain its exact numerical-width
encoding. The caller supplies a blank zero counter and retained width counters;
all work and controls restore, and only the source changes. No unsignedness
assumption is needed, since signed encodings agree on their low bits. -/
theorem narrowPackets_exec {src dst zero width rest tmp : Fin T}
    (hreg : [src,dst,zero,width,rest,tmp].Nodup)
    (W w : ℕ) (hW : 1 ≤ W) (hw : w ≤ W)
    (xs : List GaussianInt) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A W xs) (hdst : S.R dst = [])
    (hzero : S.R zero = []) (hwidth : (S.R width).length = w)
    (hrest : (S.R rest).length = W-w) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (topPass src dst (floorSliceWord src dst zero width rest tmp))
        (mk v S) (xs.length*(4*W+2*w+14)+4)
        (mk v' {S with R := Function.update S.R src (cstream A w xs)}) := by
  obtain ⟨v',hu,he⟩ := floorSlicePass_exec (body := body) hreg W 0 w (W-w)
    hW (by omega) xs v S hsrc hdst
    ⟨by simp [hzero],hwidth,hrest,htmp⟩
  refine ⟨v',hu,?_⟩
  simpa using he

/-- Return numerical results to the common external width by sign extension.
The signed-fit hypothesis belongs to the numerical result, and is not a claim
that arbitrary padded bit strings represent bounded numbers. -/
theorem widenPackets_exec {src dst width extra tmp : Fin T}
    (hreg : [src,dst,width,extra,tmp].Nodup)
    (w W : ℕ) (hw : 1 ≤ w) (hwidth : w ≤ W)
    (xs : List GaussianInt) (hfit : ∀ z ∈ xs, TopFitsZ w z)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A w xs) (hdst : S.R dst = [])
    (hg : topWidenG width extra tmp w W S.R) :
    ∃ v', v'.user = v.user ∧
      Exec body (topPass src dst (topWidenWord src dst width extra tmp))
        (mk v S) (xs.length*(6*W+10)+4)
        (mk v' {S with R := Function.update S.R src (cstream A W xs)}) := by
  have hreg' := hreg
  regs_ne hreg'
  have hframe : TopWordFrame src dst (topWidenG width extra tmp (A := A) w W) := by
    intro R ys zs ⟨h₁,h₂,h₃⟩
    refine ⟨?_,?_,?_⟩ <;> simp_all [ne_comm]
  have hmap : (xs.map (csyms A w)).map (topWidenF w W) = xs.map (csyms A W) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro z hz
    exact topWidenF_coeffSyms hw hwidth z (hfit z hz)
  obtain ⟨v',hu,he⟩ := topPass_exec body ‹src ≠ dst› hframe hw
    (topWidenWord_spec body hreg hw (w' := W)) (xs.map (csyms A w)) v S
    (by intro ys hy; obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hy; simp [csyms])
    (by simpa only [cstream,List.flatMap_def] using hsrc) hdst hg
  rw [hmap] at he
  refine ⟨v',hu,he.cast ?_ rfl⟩
  simp only [List.length_map]
  change 1 + (xs.length*((4*w+4)+((4*(W-w)+4)+1)+1)+1) +
    (2*(cstream A W xs).length+2) = _
  rw [length_cstream]
  have hsum : w+(W-w)=W := Nat.add_sub_of_le hwidth
  nlinarith only [congrArg (fun k => xs.length*k) hsum]

/-- The complete narrowing pass is linear in the common packet volume, with
an explicit per-word control allowance. -/
theorem narrowPackets_cost_le (N W w : ℕ) (hw : w ≤ W) :
    N*(4*W+2*w+14)+4 ≤ N*(6*W+14)+4 := by
  exact Nat.add_le_add_right (Nat.mul_le_mul_left N (by omega)) 4

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
