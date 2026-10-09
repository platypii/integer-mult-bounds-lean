import IntegerMultBounds.Machine.BinaryDescriptorStackAt

/-! Three changed numeric node descriptors are saved on a separate generic
binary frame stack. The full tape-bank frame is retained by both directions. -/
namespace IntegerMultBounds.Machine.CompactChildHeadersStack
noncomputable section
open BinaryDescriptorStack SharedPlacementAlphabet
variable {a t : ℕ}

def next (p : ℤ) (xs : List Bool) := p+1+xs.length

def frames (f : ℤ → Fin (a+4)) (p : ℤ) (data : Fin 3 → List Bool) :=
  frame (frame (frame f p (data 0)) (next p (data 0)) (data 1))
    (next (next p (data 0)) (data 1)) (data 2)
def top (p : ℤ) (data : Fin 3 → List Bool) := next (next (next p (data 0)) (data 1)) (data 2)
def cost (data : Fin 3 → List Bool) := 2*((data 0).length+(data 1).length+(data 2).length)+23

variable (focus : Fin 3 → Fin t) (hf : Function.Injective focus) (stack : Fin t)
  (hs : ∀ i, focus i ≠ stack)

def saveProgram : Program t 24 a :=
  seq (seq (BinaryDescriptorStackAt.pushProgram (focus 0) stack (hs 0))
    (BinaryDescriptorStackAt.pushProgram (focus 1) stack (hs 1)))
    (BinaryDescriptorStackAt.pushProgram (focus 2) stack (hs 2))
def restoreProgram : Program t 24 a :=
  seq (seq (BinaryDescriptorStackAt.popProgram stack (focus 2) (hs 2).symm)
    (BinaryDescriptorStackAt.popProgram stack (focus 1) (hs 1).symm))
    (BinaryDescriptorStackAt.popProgram stack (focus 0) (hs 0).symm)

omit hf in
theorem save (v : Tapes t a) (data : Fin 3 → List Bool)
    (hd : ∀ i, v.tape (focus i) = descriptor (data i)) (hh : ∀ i, v.head (focus i) = 1) :
    HoareTime (saveProgram (a := a) focus stack hs) (fun w => w=v)
      (fun w => w=setTape v stack (frames (v.tape stack) (v.head stack) data) (top (v.head stack) data))
      (cost data) := by
  let v1 := setTape v stack (frame (v.tape stack) (v.head stack) (data 0)) (next (v.head stack) (data 0))
  let v2 := setTape v1 stack (frame (v1.tape stack) (v1.head stack) (data 1)) (next (v1.head stack) (data 1))
  have h0 := BinaryDescriptorStackAt.push_hoare (focus 0) stack (hs 0) v (data 0) (hd 0) (hh 0)
  have h1 := BinaryDescriptorStackAt.push_hoare (focus 1) stack (hs 1) v1 (data 1)
    (by simpa [v1,setTape,hs] using hd 1) (by simpa [v1,setTape,hs] using hh 1)
  have h2 := BinaryDescriptorStackAt.push_hoare (focus 2) stack (hs 2) v2 (data 2)
    (by simpa [v2,v1,setTape,hs] using hd 2) (by simpa [v2,v1,setTape,hs] using hh 2)
  have h := (h0.seq h1).seq h2
  apply h.consequence (fun _ h => h) _ (by simp [cost]; omega)
  intro w hw
  simpa [v2,v1,frames,top,next,setTape,Function.update_idem] using hw

private theorem frames_above (f : ℤ → Fin (a+4)) (p : ℤ) (xs ys : List Bool) (z : ℤ)
    (hz : next (next p xs) ys ≤ z) : frame (frame f p xs) (next p xs) ys z = f z := by
  rw [frame_outside _ _ _ _ (Or.inr (by simpa [next] using hz))]
  rw [frame_outside _ _ _ _ (Or.inr (by simp [next] at hz ⊢; omega))]

include hf in
/-- Restoration accepts a changed caller after its three destinations have
been erased, and restores their exact saved words while consuming the frames. -/
theorem restore (v : Tapes t a) (f : ℤ → Fin (a+4)) (p : ℤ) (data : Fin 3 → List Bool)
    (ht : v.tape stack = frames f p data) (hp : v.head stack = top p data)
    (hd : ∀ i, v.tape (focus i) = fun _ => blank) (hh : ∀ i, v.head (focus i) = 0)
    (hblank : ∀ z, p ≤ z → f z = blank) :
    HoareTime (restoreProgram (a := a) focus stack hs) (fun w => w=v)
      (fun w => w=setTape (setTape (setTape (setTape v stack f p)
        (focus 2) (descriptor (data 2)) 1) (focus 1) (descriptor (data 1)) 1)
        (focus 0) (descriptor (data 0)) 1) (cost data) := by
  have hd01 : focus 0 ≠ focus 1 := fun h => by have := hf h; exact (by decide : (0 : Fin 3) ≠ 1) this
  have hd02 : focus 0 ≠ focus 2 := fun h => by have := hf h; exact (by decide : (0 : Fin 3) ≠ 2) this
  have hd12 : focus 1 ≠ focus 2 := fun h => by have := hf h; exact (by decide : (1 : Fin 3) ≠ 2) this
  let p1 := next p (data 0)
  let p2 := next p1 (data 1)
  let f1 := frame f p (data 0)
  let f2 := frame f1 p1 (data 1)
  let v1 := setTape (setTape v stack f2 p2) (focus 2) (descriptor (data 2)) 1
  let v2 := setTape (setTape v1 stack f1 p1) (focus 1) (descriptor (data 1)) 1
  have h2 := BinaryDescriptorStackAt.pop_hoare stack (focus 2) (hs 2).symm v f2 p2 (data 2)
    ht hp (hd 2) (hh 2) (by
      intro z hz _
      change frame (frame f p (data 0)) (next p (data 0)) (data 1) z = blank
      rw [frames_above f p (data 0) (data 1) z hz]
      apply hblank z
      simp [p2,p1,next] at hz
      omega)
  have h1 := BinaryDescriptorStackAt.pop_hoare stack (focus 1) (hs 1).symm v1 f1 p1 (data 1)
    (by simp [v1,setTape,(hs 2).symm,f2]) (by simp [v1,setTape,(hs 2).symm,p2,next])
    (by simp [v1,setTape,hs,hd12,hd]) (by simp [v1,setTape,hs,hd12,hh]) (by
      intro z hz _
      change frame f p (data 0) z = blank
      rw [frame_outside _ _ _ _ (Or.inr hz)]
      apply hblank z
      simp [p1,next] at hz
      omega)
  have h0 := BinaryDescriptorStackAt.pop_hoare stack (focus 0) (hs 0).symm v2 f p (data 0)
    (by simp [v2,setTape,(hs 1).symm,f1]) (by simp [v2,setTape,(hs 1).symm,p1,next])
    (by simp [v2,v1,setTape,hs,hd01,hd02,hd]) (by simp [v2,v1,setTape,hs,hd01,hd02,hh])
    (by intro z hz _; exact hblank z hz)
  have h := (h2.seq h1).seq h0
  apply h.consequence (fun _ h => h) _ (by simp [cost]; omega)
  intro w hw
  simp only [v2,v1] at hw
  simpa [setTape,Function.update_comm (hs 1),Function.update_comm (hs 2),
    Function.update_comm hd12,Function.update_idem] using hw

end
end IntegerMultBounds.Machine.CompactChildHeadersStack
