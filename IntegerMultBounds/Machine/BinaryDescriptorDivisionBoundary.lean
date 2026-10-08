import IntegerMultBounds.Machine.BinaryDescriptorDivisionRaw
import IntegerMultBounds.Machine.DescriptorStackControl

/-! Physical marked-input preparation and marker restoration for division.
Every scan, head move, marker erasure/write, and program join is charged. -/
namespace IntegerMultBounds.Machine.BinaryDescriptorDivisionBoundary
open BinaryDescriptorDivisionRaw (bank)
open BinaryDescriptorStack (descriptor)
variable {a : ℕ}

def frontAction (w0 w1 : Fin (a+4) → Fin (a+4)) (m0 m1 : Move)
    (sy : Fin 6 → Fin (a+4)) (i : Fin 6) : Fin (a+4) × Move :=
  if i = 0 then (w0 (sy i),m0) else if i = 1 then (w1 (sy i),m1) else (sy i,Move.stay)

def front (w0 w1 : Fin (a+4) → Fin (a+4)) (m0 m1 : Move) : Program 6 2 a :=
  DescriptorStackControl.once (by decide) (frontAction w0 w1 m0 m1)

private theorem front_hoare (w0 w1 : Fin (a+4) → Fin (a+4)) (m0 m1 : Move)
    (f0 f1 f2 f3 f4 f5 : ℤ → Fin (a+4)) (p0 p1 p2 p3 p4 p5 : ℤ) :
    HoareTime (front w0 w1 m0 m1) (fun v => v = bank f0 f1 f2 f3 f4 f5 p0 p1 p2 p3 p4 p5)
      (fun v => v = bank (Function.update f0 p0 (w0 (f0 p0))) (Function.update f1 p1 (w1 (f1 p1)))
        f2 f3 f4 f5 (p0+m0.offset) (p1+m1.offset) p2 p3 p4 p5) 1 := by
  apply (DescriptorStackControl.once_hoare (by decide) _ (bank f0 f1 f2 f3 f4 f5 p0 p1 p2 p3 p4 p5)).consequence
    (fun _ h => h) _ le_rfl
  rintro v rfl
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> simp [bank,frontAction,Move.offset]
  · funext i z; fin_cases i <;> simp [bank,frontAction,Function.update_apply] <;> intro h <;> subst z <;> rfl

private theorem mark_raw (xs : List Bool) :
    Function.update (BinaryQuotientNormalize.raw (a := a) xs 1) 0 separator = descriptor xs := by
  have he : Function.update (fun _ : ℤ => (blank : Fin (a+4))) 0 separator = BinaryDescriptorStack.empty := by
    funext z; simp [BinaryDescriptorStack.empty,Function.update_apply]
  rw [BinaryQuotientNormalize.raw,← putWord_update_before _ _ _ _ _ (by omega),he]
  rfl

private theorem erase_marker (xs : List Bool) :
    Function.update (descriptor (a := a) xs) 0 blank = BinaryQuotientNormalize.raw xs 1 := by
  rw [← mark_raw,Function.update_idem]
  apply Function.update_eq_self_iff.mpr
  rw [BinaryQuotientNormalize.raw,putWord_outside _ _ _ _ (Or.inl (by omega))]

def input (ys ds : List Bool) : Tapes 6 a :=
  bank (descriptor ys) (descriptor ds) (fun _ => blank) (fun _ => blank) (fun _ => blank) (fun _ => blank) 1 1 0 0 0 0

def prepare : Program 6 7 a :=
  seq (seq (seq (front id id Move.left Move.left) (front (fun _ => blank) (fun _ => blank) Move.right Move.right))
    (DescriptorStackControl.seek 0 blank Move.right)) (front id id Move.left Move.stay)

theorem prepare_hoare (ys ds : List Bool) :
    HoareTime (prepare (a := a)) (fun v => v = input ys ds)
      (fun v => v = BinaryDescriptorDivisionRaw.input ys ds) (ys.length+6) := by
  let ry := BinaryQuotientNormalize.raw (a := a) ys 1
  let rd := BinaryQuotientNormalize.raw (a := a) ds 1
  have h1 := front_hoare (a := a) id id Move.left Move.left (descriptor ys) (descriptor ds)
    (fun _ => blank) (fun _ => blank) (fun _ => blank) (fun _ => blank) 1 1 0 0 0 0
  simp only [id_eq,Function.update_eq_self,Move.offset] at h1
  have h2 := front_hoare (a := a) (fun _ => (blank : Fin (a+4))) (fun _ => blank) Move.right Move.right
    (descriptor ys) (descriptor ds) (fun _ => blank) (fun _ => blank) (fun _ => blank) (fun _ => blank) 0 0 0 0 0 0
  rw [erase_marker,erase_marker] at h2
  simp only [Move.offset,zero_add] at h2
  have hs := DescriptorStackControl.seek_hoare (bank ry rd (fun _ => blank) (fun _ => blank) (fun _ => blank) (fun _ => blank) 1 1 0 0 0 0)
    0 blank Move.right ys.length (by
      intro j hj
      have hm := ReturnOrigin.putWord_mem (fun _ => (blank : Fin (a+4))) 1 (ys.map bitSymbol) (1+j) (by simp; omega)
      obtain ⟨b,_,he⟩ := List.mem_map.mp hm
      change ry (1+j*Move.right.offset) ≠ blank
      simp only [Move.offset,mul_one,ry,BinaryQuotientNormalize.raw]
      rw [← he]
      cases b <;> simp [bitSymbol,blank,Fin.ext_iff])
    (by
      change ry (1+ys.length*Move.right.offset) = blank
      simp only [Move.offset,mul_one,ry,BinaryQuotientNormalize.raw]
      exact putWord_outside _ _ _ _ (Or.inr (by simp)))
  have hpos : DescriptorStackControl.positioned
      (bank ry rd (fun _ => blank) (fun _ => blank) (fun _ => blank) (fun _ => blank) 1 1 0 0 0 0) 0
      ((bank ry rd (fun _ => blank) (fun _ => blank) (fun _ => blank) (fun _ => blank) 1 1 0 0 0 0).head 0+ys.length*Move.right.offset) =
      bank ry rd (fun _ => blank) (fun _ => blank) (fun _ => blank) (fun _ => blank) (1+ys.length) 1 0 0 0 0 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [bank,Move.offset]
  rw [hpos] at hs
  have h3 := front_hoare (a := a) id id Move.left Move.stay ry rd (fun _ => blank) (fun _ => blank) (fun _ => blank) (fun _ => blank) (1+ys.length) 1 0 0 0 0
  simp only [id_eq,Function.update_eq_self,Move.offset,add_zero] at h3
  have hcoord : (1 : ℤ)+ys.length+(-1) = ys.length := by omega
  rw [hcoord] at h3
  exact (((h1.seq h2).seq hs).seq h3).consequence (fun _ h => h) (fun _ h => h) (by omega)

def finish : Program 6 4 a :=
  seq (front id id Move.stay Move.left) (front (fun _ => separator) (fun _ => separator) Move.right Move.right)

def output (ys ds zs : List Bool) : Tapes 6 a :=
  bank (descriptor ys) (descriptor ds)
    (BinaryDivide.blankWord (-(ys.length : ℤ)) (BinaryDivide.remainder ds ys))
    (fun _ => blank) (fun _ => blank) (descriptor zs) 1 1 (-(ys.length : ℤ)) 0 0 1

theorem finish_hoare (ys ds zs : List Bool) :
    HoareTime (finish (a := a)) (fun v => v = BinaryDescriptorDivisionRaw.output ys ds zs)
      (fun v => v = output ys ds zs) 3 := by
  let ry := BinaryQuotientNormalize.raw (a := a) ys 1
  let rd := BinaryQuotientNormalize.raw (a := a) ds 1
  let rem := BinaryDivide.blankWord (a := a) (-(ys.length : ℤ)) (BinaryDivide.remainder ds ys)
  have h1 := front_hoare (a := a) id id Move.stay Move.left ry rd rem (fun _ => blank) (fun _ => blank) (descriptor zs) 0 1 (-(ys.length : ℤ)) 0 0 1
  simp only [id_eq,Function.update_eq_self,Move.offset,add_zero] at h1
  have h2 := front_hoare (a := a) (fun _ => (separator : Fin (a+4))) (fun _ => separator) Move.right Move.right
    ry rd rem (fun _ => blank) (fun _ => blank) (descriptor zs) 0 0 (-(ys.length : ℤ)) 0 0 1
  change HoareTime _ _ (fun v => v = bank
    (Function.update (BinaryQuotientNormalize.raw ys 1) 0 separator)
    (Function.update (BinaryQuotientNormalize.raw ds 1) 0 separator) rem (fun _ => blank) (fun _ => blank) (descriptor zs) 1 1 (-(ys.length : ℤ)) 0 0 1) 1 at h2
  rw [mark_raw,mark_raw] at h2
  exact h1.seq h2

end IntegerMultBounds.Machine.BinaryDescriptorDivisionBoundary
