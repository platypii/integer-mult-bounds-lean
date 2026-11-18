module

public import IntegerMultBounds.MathlibTM2.Cover.LabelColumns
public import IntegerMultBounds.MathlibTM2.Cover.LabelProgram
public import IntegerMultBounds.MathlibTM2.Cover.LabelShift

/-! Packed coordinate semantics of the scalar instruction machine. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelEntry
noncomputable section

open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime prime_prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveInterchangeScaling (Address index)
open RecursiveViewedAction (Action)
open FlatCoordinateLayout (rank)
open ActualAffineScaling (modulus)
open IntegerMultBounds.Swap.Modular (ratMod)
open LabelProgram (Step)
variable {v : Descriptor} {k w B : ℕ}
local instance : NeZero (modulus w) := ⟨(ActualAffineScaling.modulus_pos w).ne'⟩

/-- One caller address, with the label digits supplied separately. -/
structure Cell (v : Descriptor) (B : ℕ) where
  a : Fin v.beforeRows
  row : Fin v.rows
  b : Fin B
  h : Fin (modulus v.width)
  mid : Fin v.between
  d : Fin (modulus v.width)
  after : Fin v.afterD

def position (z : Cell v B) (hv : v.beforeH = B*prime^(k*w)) (x : Fin k → ZMod (modulus w)) :
    Fin (volume prime v) :=
  index ⟨z.a,z.row,⟨z.b.val*prime^(k*w)+(rank x).val, by
    rw [hv]
    apply LabelShift.pack_lt z.b.isLt
    simpa only [modulus, ← pow_mul, Nat.mul_comm w k] using (rank x).isLt⟩,z.h,z.mid,z.d,z.after⟩

private def dest {u : Descriptor} (act : Action 1) (z : Address u) : Address u :=
  match act with
  | .shift _ r _ => RecursiveInterchangeShift.shiftAddress r z
  | .scale _ r _ target => RecursiveInterchangeScaling.scaleAddress r z target

private theorem dest_entry {u : Descriptor} (act : Action 1) (a : Fin (volume prime u) → Fin 4) (z : Address u) :
    RecursiveViewedAction.transform act (fun _ => a) 0 (index (dest act z)) = a (index z) := by
  cases act with
  | shift wire r hr =>
    fin_cases wire
    exact RecursiveInterchangeShift.array_entry r a z
  | scale wire r hr target =>
    fin_cases wire
    exact RecursiveInterchangeScaling.array_entry hr a target z

private theorem dest_fields {u : Descriptor} (act : Action 1) (z : Address u)
    (s t : Fin k) (hst : s < t) (x : Fin k → ZMod (modulus u.width))
    (hh : z.h.val = (x s).val) (hd : z.d.val = (x t).val) :
    let op : Step k := ⟨⟨(s,t),hst⟩, act⟩
    let y := OrderedAffine.execute (OrderedAffine.mapOp (ratMod (modulus u.width)) op.rational) x
    (dest act z).h.val = (y s).val ∧ (dest act z).d.val = (y t).val ∧
      Function.update (Function.update x s (y s)) t (y t) = y := by
  cases act with
  | shift wire r hr =>
    simp only [Step.rational, OrderedAffine.mapOp, OrderedAffine.execute, Function.update_self,
      Function.update_of_ne hst.ne, Function.update_eq_self, dest]
    refine ⟨hh, ?_, trivial⟩
    rw [RecursiveInterchangeShift.shiftAddress_d r hr, hd, hh, ZMod.natCast_zmod_val, ZMod.val_add]
  | scale wire r hr target =>
    cases target <;>
      simp [Step.rational, OrderedAffine.mapOp, OrderedAffine.execute, Function.update_of_ne hst.ne,
        Function.update_of_ne hst.ne', Function.update_eq_self, dest, RecursiveInterchangeScaling.scaleAddress,
        FlatAffineScalingArray.coordinate, hh, hd]

private theorem dest_shape {u : Descriptor} (act : Action 1) (z : Address u) :
    dest act z = {z with h := (dest act z).h, d := (dest act z).d} := by
  cases act with
  | shift => rfl
  | scale _ _ _ target => cases target <;> rfl

private theorem label_radix (q w k s t lp a gap b ls : ℕ) :
    LabelView.label (q^w) 1 k s t lp a gap b ls = LabelView.label q w k s t lp a gap b ls := by
  simp only [LabelView.label, Nat.one_mul, pow_one, ← Nat.pow_mul, Nat.mul_comm]

/-- One physical scalar operation transports every packed address to its ordered-affine
destination, keeping its outer prefix and its payload. -/
theorem step_entry (op : Step k) (hv : v.beforeH = B*prime^(k*w)) (a : LabelProgram.Array v)
    (z : Cell v B) (x : Fin k → ZMod (modulus w)) :
    let y := OrderedAffine.execute (OrderedAffine.mapOp (ratMod (modulus w)) op.rational) x
    op.apply hv a (position z hv y) = a (position z hv x) := by
  obtain ⟨⟨⟨s,t⟩,hst⟩, act⟩ := op
  let u := LabelView.colView prime w k s t B v
  let H := LabelView.colView_volume prime w k s t B v hv hst t.isLt
  let op : Step k := ⟨⟨(s,t),hst⟩,act⟩
  let y := OrderedAffine.execute (OrderedAffine.mapOp (ratMod (modulus w)) op.rational) x
  obtain ⟨lp, gap, ls, hx, hy⟩ := LabelColumns.rank_pair_update x s t hst (y s) (y t)
  have radix (n : ℕ) : (modulus w)^n = prime^(n*w) := by rw [modulus, ← pow_mul, Nat.mul_comm]
  let addr : Address u := LabelShift.viewAddress z.a z.row z.b lp (x s).val gap (x t).val ls
    z.h z.mid z.d z.after z.a.isLt z.row.isLt z.b.isLt (lp.isLt.trans_eq (radix _))
    (ZMod.val_lt _) (gap.isLt.trans_eq (radix _)) (ZMod.val_lt _) (ls.isLt.trans_eq (radix _))
    z.h.isLt z.mid.isLt z.d.isLt z.after.isLt
  obtain ⟨hh, hd, hy'⟩ := dest_fields act addr s t hst x rfl rfl
  change Function.update (Function.update x s (y s)) t (y t) = y at hy'
  rw [hy'] at hy
  have hx := hx.trans (label_radix prime w _ _ _ _ _ _ _ _)
  have hy := hy.trans (label_radix prime w _ _ _ _ _ _ _ _)
  have idx (i j : Fin (modulus w)) :
      (index ({addr with h := i, d := j} : Address u)).val =
        RecursiveInterchangeLayout.index prime v z.a z.row
          (z.b.val*prime^(k*w)+LabelView.label prime w k s t lp i gap j ls) z.h z.mid z.d z.after := by
    rw [RecursiveInterchangeScaling.index_val]
    exact LabelView.colView_index prime w k s t B v hv hst t.isLt _ _ _ _ _ _ _ _ _ _ _ _
  have hsrc : Fin.cast H (index addr) = position z hv x := by
    apply Fin.ext
    rw [Fin.val_cast, show (index addr).val = _ from idx addr.h addr.d, position,
      RecursiveInterchangeScaling.index_val]
    simp only [hx]; rfl
  have hdst : Fin.cast H (index (dest act addr)) = position z hv y := by
    apply Fin.ext
    rw [Fin.val_cast, dest_shape act addr, idx (dest act addr).h (dest act addr).d, hh, hd, position, RecursiveInterchangeScaling.index_val]
    simp only [hy]; rfl
  change op.apply hv a (position z hv y) = a (position z hv x)
  rw [← hsrc, ← hdst]
  exact dest_entry act (fun i => a (Fin.cast H i)) addr

theorem list_entry (ops : List (Step k)) (hv : v.beforeH = B*prime^(k*w)) (a : LabelProgram.Array v)
    (z : Cell v B) (x : Fin k → ZMod (modulus w)) :
    let out := ops.foldl (fun b op => op.apply hv b) a
    let y := OrderedAffine.run ((ops.map Step.rational).map (OrderedAffine.mapOp (ratMod (modulus w)))) x
    out (position z hv y) = a (position z hv x) := by
  induction ops generalizing a x with
  | nil => rfl
  | cons op ops ih =>
    exact (ih (op.apply hv a) (OrderedAffine.execute
      (OrderedAffine.mapOp (ratMod (modulus w)) op.rational) x)).trans (step_entry op hv a z x)

/-- The compiled tape pass realizes the right matrix product on every caller cell. -/
theorem pass_entry {m : ℕ} (hk : 2 ≤ m*m) (E : Matrix (Fin m) (Fin m) ℚ)
    (hs : ∀ op ∈ LabelAddress.pass E, FlatCoordinateSchedule.Supported op)
    (hE : IntegerMultBounds.Swap.Shear.LowerTriangular E)
    (hu : IsUnit (IntegerMultBounds.Swap.Modular.reduce (modulus w) E))
    (hv : v.beforeH = B*prime^((m*m)*w)) (a : LabelProgram.Array v) (z : Cell v B)
    (g : Matrix (Fin m) (Fin m) (ZMod (modulus w))) :
    let ops := LabelProgram.pass hk E hs
    let out := ops.foldl (fun b op => op.apply hv b) a
    let coords := M8.AtomOps.refine ∘ Route.cols (m := m) (R := ZMod (modulus w))
    out (position z hv (coords (g * (IntegerMultBounds.Swap.Modular.reduce (modulus w) E).transpose))) =
      a (position z hv (coords g)) := by
  have h := list_entry (LabelProgram.pass hk E hs) hv a z (M8.AtomOps.refine (Route.cols g))
  dsimp only at h
  rw [LabelProgram.pass_rational, ← LabelAddress.pass_map] at h
  have hl := IntegerMultBounds.Swap.Modular.reduce_lowerTriangular (modulus w) hE
  rw [← IntegerMultBounds.Swap.Modular.reduce, LabelAddress.pass_run hl (OrderedAffine.program_legal hl hu) g] at h
  exact h

/-- A single machine run and its matrix-label postcondition on the same output tape. -/
theorem pass_runs {m T : ℕ} (hk : 2 ≤ m*m) (E : Matrix (Fin m) (Fin m) ℚ)
    (hs : ∀ op ∈ LabelAddress.pass E, FlatCoordinateSchedule.Supported op)
    (hE : IntegerMultBounds.Swap.Shear.LowerTriangular E)
    (hu : IsUnit (IntegerMultBounds.Swap.Modular.reduce (modulus w) E))
    (hv : v.beforeH = B*prime^((m*m)*w)) (hw : 0 < w) (hb : 0 < B) (hp : v.Positive)
    (io : Fin T) (roles : Tapes T prime) (a : LabelProgram.Array v)
    (hh : roles.head io = 0) (hx : roles.tape io = RecursiveShiftRoleBank.source a) :
    let ops := LabelProgram.pass hk E hs
    let d := M8.Stage2Machine.Straight.words (LabelSchedule.base v w)
    ∃ out : LabelProgram.Array v,
      M8.RevMachine.GraphContract.Runs (LabelProgram.program io ops) (LabelCall.bank roles v d)
        (LabelCall.bank (SharedPlacementAlphabet.setTape roles io (RecursiveShiftRoleBank.source out) 0) v d)
        (LabelProgram.coefficient ops * volume prime v) ∧
      ∀ (z : Cell v B) (g : Matrix (Fin m) (Fin m) (ZMod (modulus w))),
        let coords := M8.AtomOps.refine ∘ Route.cols (m := m) (R := ZMod (modulus w))
        out (position z hv (coords (g * (IntegerMultBounds.Swap.Modular.reduce (modulus w) E).transpose))) =
          a (position z hv (coords g)) :=
  ⟨_, LabelProgram.runs _ hw hb hv hp io roles a hh hx, pass_entry hk E hs hE hu hv a⟩

end
end IntegerMultBounds.MathlibTM2.Cover.LabelEntry
