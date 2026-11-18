module

public import IntegerMultBounds.MathlibTM2.Cover.LabelInstruction
public import IntegerMultBounds.MathlibTM2.Cover.LabelPass

/-! Compiling a rational scalar schedule on one role of the cover descriptor. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelProgram
noncomputable section

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.M8.RevMachine
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveViewedAction (Action transform)
open RecursiveShiftRoleBank (source)
open LabelCall (bank)
open M8.Stage2Machine.Straight (words)
variable {T k c B : ℕ} {v : Descriptor}

structure Step (k : ℕ) where
  pair : LabelSchedule.Pair k
  act : Action 1

/-- A shift already specifies both fields. For a scale use the first field as spectator,
or the second if the target itself is first. -/
def compile (hk : 2 ≤ k) : FlatCoordinateSchedule.Op k → Step k
  | .shift t s h r hr => ⟨⟨(s,t),h⟩, .shift 0 r (Networks.Shared50AffineCoefficients.denominator_bound hr)⟩
  | .scale t r hr =>
    if h : t.val = 0 then
      ⟨⟨(t, ⟨1, by omega⟩), by change t.val < 1; omega⟩, .scale 0 r hr .h⟩
    else
      ⟨⟨(⟨0, by omega⟩, t), by change 0 < t.val; omega⟩, .scale 0 r hr .d⟩

/-- Coordinate instruction selected by a two-field view. -/
def Step.rational (op : Step k) : Networks.OrderedAffine.Op (Fin k) ℚ :=
  match op.act with
  | .shift _ r _ => .shift op.pair.val.2 op.pair.val.1 r
  | .scale _ r _ .h => .scale op.pair.val.1 r
  | .scale _ r _ .d => .scale op.pair.val.2 r

@[simp] theorem rational_compile (hk : 2 ≤ k) (op : FlatCoordinateSchedule.Op k) :
    (compile hk op).rational = op.rational := by
  cases op with
  | shift => rfl
  | scale t r hr => by_cases h : t.val = 0 <;> simp [compile, h, Step.rational, FlatCoordinateSchedule.Op.rational]

/-- The compiled triangular pass has precisely the original ordered coefficients and indices. -/
def pass {m : ℕ} (hk : 2 ≤ m*m) (E : Matrix (Fin m) (Fin m) ℚ)
    (hs : ∀ op ∈ LabelAddress.pass E, FlatCoordinateSchedule.Supported op) :=
  (FlatCoordinateSchedule.ofList (LabelAddress.pass E) hs).map (compile hk)

theorem pass_rational {m : ℕ} (hk : 2 ≤ m*m) (E : Matrix (Fin m) (Fin m) ℚ)
    (hs : ∀ op ∈ LabelAddress.pass E, FlatCoordinateSchedule.Supported op) :
    (pass hk E hs).map Step.rational = LabelAddress.pass E := by
  simp only [pass, List.map_map, Function.comp_def, rational_compile]
  exact FlatCoordinateSchedule.rational_ofList _ _

abbrev Array (v : Descriptor) := Fin (volume prime v) → Fin 4

def Step.apply (op : Step k) (hv : v.beforeH = B*prime^(k*c)) (x : Array v) : Array v :=
  let h := LabelView.colView_volume prime c k op.pair.val.1 op.pair.val.2 B v hv op.pair.property op.pair.val.2.isLt
  fun i => transform op.act (fun _ j => x (Fin.cast h j)) 0 (Fin.cast h.symm i)

def Step.coefficient (op : Step k) : ℕ :=
  3808274 + RecursiveViewedAction.coefficient op.act + LabelSchedule.setupCost k op.pair.val.1 op.pair.val.2 +
    LabelSchedule.clearCost k op.pair.val.1 op.pair.val.2 + 2

theorem step_runs (op : Step k) (hc : 0 < c) (hb : 0 < B) (hv : v.beforeH = B*prime^(k*c))
    (hp : v.Positive) (io : Fin T) (roles : Tapes T prime) (x : Array v)
    (hh : roles.head io = 0) (hx : roles.tape io = source x) :
    let d := words (LabelSchedule.base v c)
    GraphContract.Runs (LabelInstruction.program op.pair io op.act) (bank roles v d)
      (bank (SharedPlacementAlphabet.setTape roles io (source (op.apply hv x)) 0) v d)
      (op.coefficient * volume prime v) := by
  let h := LabelView.colView_volume prime c k _ _ B v hv op.pair.property op.pair.val.2.isLt
  have hr := LabelInstruction.runs op.pair hc hb hv hp io roles op.act
    (fun _ j => x (Fin.cast h j)) hh (hx.trans (LeafCore.pair_cast h x).symm)
  unfold Step.apply
  rw [show source (v := v) (fun i => transform op.act (fun _ j => x (Fin.cast h j)) 0 (Fin.cast h.symm i)) = _ from
    LeafCore.pair_cast h.symm _]
  exact hr

def program (io : Fin T) : List (Step k) → Graph.Block (T+24) prime
  | [] => SharedBankSkeleton.identity _ _ (by omega)
  | op :: ops => Blocks.seqB (LabelInstruction.program op.pair io op.act) (program io ops)

theorem leading (io : Fin T) (ops : List (Step k)) : Blocks.Leading (program io ops) := by
  cases ops <;> exact fun _ => rfl

def coefficient (ops : List (Step k)) := (ops.map Step.coefficient).sum + ops.length

theorem runs (ops : List (Step k)) (hc : 0 < c) (hb : 0 < B) (hv : v.beforeH = B*prime^(k*c))
    (hp : v.Positive) (io : Fin T) (roles : Tapes T prime) (x : Array v)
    (hh : roles.head io = 0) (hx : roles.tape io = source x) :
    let d := words (LabelSchedule.base v c)
    GraphContract.Runs (program io ops) (bank roles v d)
      (bank (SharedPlacementAlphabet.setTape roles io
        (source (ops.foldl (fun z op => op.apply hv z) x)) 0) v d)
      (coefficient ops * volume prime v) := by
  induction ops generalizing roles x with
  | nil =>
    have hself : SharedPlacementAlphabet.setTape roles io (source x) 0 = roles := by
      rw [← hh, ← hx]; simp [SharedPlacementAlphabet.setTape, Function.update_eq_self]
    simp only [List.foldl_nil, hself, coefficient, List.map_nil, List.sum_nil, List.length_nil,
      Nat.zero_add, Nat.zero_mul]
    exact skip_hoare _ _
  | cons op ops ih =>
    have h := step_runs op hc hb hv hp io roles x hh hx
    have htail := ih (SharedPlacementAlphabet.setTape roles io (source (op.apply hv x)) 0) (op.apply hv x)
      (by simp [SharedPlacementAlphabet.setTape]) (by simp [SharedPlacementAlphabet.setTape])
    simp only [SharedPlacementAlphabet.setTape_setTape] at htail
    apply Blocks.runs_mono (Blocks.seq_runs (Blocks.seq_leading _ _) (leading io ops) h htail)
    simp only [coefficient, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.succ_mul]
    have := RecursiveAffinePrepare.volume_positive prime_prime.two_le v hp
    omega

end
end IntegerMultBounds.MathlibTM2.Cover.LabelProgram
