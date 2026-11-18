module

public import IntegerMultBounds.MathlibTM2.Cover.LabelEntry
public import IntegerMultBounds.MathlibTM2.Cover.LabelTransport
public import IntegerMultBounds.Machine.RecursiveScalarIndex

/-! The descriptor-wide triangular pass on the bit encoding of the interchange supplier. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelBits
noncomputable section

open IntegerMultBounds.Machine IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.M8.RevMachine
open Shared50ModularControl (prime prime_prime)
open RecursiveInterchangeLayout (Descriptor volume)
open ActualAffineScaling (modulus)
open LabelEntry (Cell position)
open Shared50RecursiveNodeSemantics (encoded)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open IntegerMultBounds.Swap.Modular (reduce)
variable {v : Descriptor} {m w B : ℕ}
local instance : NeZero (modulus w) := ⟨(ActualAffineScaling.modulus_pos w).ne'⟩

def coords (g : Matrix (Fin m) (Fin m) (ZMod (modulus w))) := M8.AtomOps.refine (Route.cols g)

/-- Every physical symbol has an outer prefix, a matrix label and a payload position. -/
theorem covers (hv : v.beforeH = B*prime^((m*m)*w)) (i : Fin (volume prime v)) :
    ∃ (z : Cell v B) (g : Matrix (Fin m) (Fin m) (ZMod (modulus w))), position z hv (coords g) = i := by
  obtain ⟨a, rfl⟩ := RecursiveScalarIndex.scaling_surjective i
  let N := (modulus w)^(m*m)
  have hN : N = prime^((m*m)*w) := by simp only [N, modulus, ← pow_mul, Nat.mul_comm w]
  have he : v.beforeH = B*N := hv.trans (congrArg (B*·) hN.symm)
  obtain ⟨⟨b, n⟩, hn⟩ := (finProdFinEquiv : Fin B × Fin N ≃ _).surjective (Fin.cast he a.before)
  let x := FlatCoordinateLayout.coordinates n
  let g : Matrix (Fin m) (Fin m) (ZMod (modulus w)) := fun i j => x (finProdFinEquiv (j,i))
  have hg : coords g = x := by
    funext j
    obtain ⟨⟨j,i⟩,rfl⟩ := finProdFinEquiv.surjective j
    exact M8.AtomOps.refine_at (Route.cols g) j i
  refine ⟨⟨a.beforeRows,a.row,b,a.h,a.middle,a.d,a.after⟩, g, ?_⟩
  rw [hg]
  unfold position
  congr 1
  cases a
  congr 1
  apply Fin.ext
  have h := congrArg Fin.val hn
  simp only [finProdFinEquiv_apply_val, Fin.val_cast] at h
  change b.val*prime^((m*m)*w)+(FlatCoordinateLayout.rank x).val = _
  rw [← hN, show FlatCoordinateLayout.rank x = n from FlatCoordinateLayout.rank_coordinates n]
  simpa only [Nat.mul_comm, Nat.add_comm] using h

private theorem encode_inj : Function.Injective (SparseRoleCircuit.encode (a := 0)) := by
  intro x y h
  fin_cases x <;> fin_cases y <;> first | rfl | contradiction

theorem pass_runs {T : ℕ} (hk : 2 ≤ m*m) (E : Matrix (Fin m) (Fin m) ℚ)
    (hs : ∀ op ∈ LabelAddress.pass E, FlatCoordinateSchedule.Supported op)
    (hE : IntegerMultBounds.Swap.Shear.LowerTriangular E) (hu : IsUnit (reduce (modulus w) E))
    (hv : v.beforeH = B*prime^(m*(w*m))) (hw : 0 < w) (hb : 0 < B) (hp : v.Positive)
    (io : Fin T) (roles : Tapes T prime) (x : Fin (volume prime v) → ZMod 2)
    (hh : roles.head io = 0) (hx : roles.tape io = sourceWord x) :
    let ops := LabelProgram.pass hk E hs
    let d := M8.Stage2Machine.Straight.words (LabelSchedule.base v w)
    ∃ y : Fin (volume prime v) → ZMod 2,
      GraphContract.Runs (LabelProgram.program io ops) (LabelCall.bank roles v d)
        (LabelCall.bank (SharedPlacementAlphabet.setTape roles io (sourceWord y) 0) v d)
        (LabelProgram.coefficient ops * volume prime v) ∧
      LabelPermutation.Transport v B w (fun g => g * (reduce (modulus w) E).transpose) (ext x) (ext y) := by
  have he : m*(w*m) = (m*m)*w := by ring
  have hv' := hv
  rw [he] at hv'
  obtain ⟨out, hr, h⟩ := LabelEntry.pass_runs hk E hs hE hu hv' hw hb hp io roles (encoded x) hh hx
  obtain ⟨u, hu'⟩ := ((reduce (modulus w) E).isUnit_transpose.mpr hu)
  have hall (i : Fin (volume prime v)) : ∃ bit, SparseRoleCircuit.encode bit = out i := by
    obtain ⟨z, g, rfl⟩ := covers hv' i
    let f := g * (↑u⁻¹ : Matrix (Fin m) (Fin m) (ZMod (modulus w)))
    have hf : f * (reduce (modulus w) E).transpose = g := by
      rw [← hu']; simp [f, Matrix.mul_assoc]
    have hentry := h z f
    dsimp only at hentry
    rw [hf] at hentry
    exact ⟨_, hentry.symm⟩
  choose y hy using hall
  have hout : encoded y = out := funext hy
  refine ⟨y, ?_, ?_⟩
  · rwa [← hout] at hr
  · intro g a ha row hrow b hb' hval hh' mid hm d hd after haf
    change Matrix (Fin m) (Fin m) (ZMod (modulus w)) at g
    let z : Cell v B := ⟨⟨a,ha⟩, ⟨row,hrow⟩, ⟨b,hb'⟩, ⟨hval,hh'⟩, ⟨mid,hm⟩, ⟨d,hd⟩, ⟨after,haf⟩⟩
    have key := h z g
    rw [← hout] at key
    have bit := encode_inj key
    have idx (g : Matrix (Fin m) (Fin m) (ZMod (modulus w))) :
        (position z hv' (coords g)).val = RecursiveInterchangeLayout.index prime v a row
          (b*prime^(m*(w*m))+(LabelAddress.address g).val) hval mid d after := by
      rw [position, RecursiveInterchangeScaling.index_val, he]; rfl
    have readAt (a : Fin (volume prime v) → ZMod 2) (g : Matrix (Fin m) (Fin m) (ZMod (modulus w))) :=
      (congrArg (ext a) (idx g).symm).trans (ext_apply a _)
    exact (readAt y _).trans (bit.trans (readAt x g).symm)

end
end IntegerMultBounds.MathlibTM2.Cover.LabelBits
