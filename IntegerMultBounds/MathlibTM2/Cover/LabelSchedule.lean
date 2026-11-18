module

public import IntegerMultBounds.MathlibTM2.Cover.Route
public import IntegerMultBounds.MathlibTM2.Cover.LabelSwap
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Width

/-! A fixed column exchange supplies its own column counts and returns their tapes blank. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelSchedule
noncomputable section

open IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2.M8.RevMachine
open IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Straight (State words)
open IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Width (constAt const_step)
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open FlatCoordinateSchedule (bits)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open SharedPlacementAlphabet (setTape)
open LabelCall (bank)
variable {T k : ℕ}

def base (v : Descriptor) (c : ℕ) : State :=
  ![none,none,none,some v.beforeH,none,none,some c,none,none,none,some v.width,
    some v.between,some v.afterD,none,none,none,none,none,none,none,none,none]

def setup (k s t : ℕ) :=
  seq (seq (constAt (q := prime) (k-s) 7) (constAt (q := prime) (k-1-t) 20))
    (constAt (q := prime) (t-s-1) 21)

def clear := seq (seq (Headers.eraseAt (q := prime) 21) (Headers.eraseAt 20)) (Headers.eraseAt 7)

def setupCost (k s t : ℕ) := RecursiveChildQuotientsConstant.cost (k-s) +
  RecursiveChildQuotientsConstant.cost (k-1-t) + RecursiveChildQuotientsConstant.cost (t-s-1) + 2

def clearCost (k s t : ℕ) := 2*((bits (k-s)).length+(bits (k-1-t)).length+(bits (t-s-1)).length)+14

theorem setup_runs (v : Descriptor) (k s t c : ℕ) :
    HoareTime (setup k s t) (fun w => w = Headers.bank (words (base v c)))
      (fun w => w = Headers.bank (LabelPrepare.input v k s t c)) (setupCost k s t) := by
  let a := Function.update (base v c) (7 : Fin 22) (some (k-s))
  let b := Function.update a (20 : Fin 22) (some (k-1-t))
  have h := ((const_step (q := prime) (s := base v c) (j := 7) (k-s) rfl).seq
    (const_step (s := a) (j := 20) (k-1-t) rfl)).seq (const_step (s := b) (j := 21) (t-s-1) rfl)
  have he : words (Function.update b 21 (some (t-s-1))) = LabelPrepare.input v k s t c := by
    funext i; fin_cases i <;> rfl
  rw [he] at h
  exact h.consequence (fun _ h => h) (fun _ h => h) (by unfold setupCost; omega)

theorem clear_runs (v : Descriptor) (k s t c : ℕ) :
    HoareTime clear (fun w => w = Headers.bank (LabelPrepare.input v k s t c))
      (fun w => w = Headers.bank (words (base v c))) (clearCost k s t) := by
  let d := LabelPrepare.input v k s t c
  let a := Function.update d (21 : Fin 22) none
  let b := Function.update a (20 : Fin 22) none
  have h := ((Headers.erase_step (q := prime) (d := d) (j := 21) (xs := bits (t-s-1)) rfl).seq
    (Headers.erase_step (d := a) (j := 20) (xs := bits (k-1-t)) rfl)).seq
    (Headers.erase_step (d := b) (j := 7) (xs := bits (k-s)) rfl)
  have he : Function.update b 7 none = words (base v c) := by funext i; fin_cases i <;> rfl
  rw [he] at h
  exact h.consequence (fun _ h => h) (fun _ h => h) (by unfold clearCost; omega)

abbrev Pair (k : ℕ) := {p : Fin k × Fin k // p.1 < p.2}

def atPair (p : Pair k) (body : Graph.Block (T+24) prime) :=
  Blocks.seqB (Blocks.seqB (LabelSwap.onHeaders (p := 0) (setup k p.val.1 p.val.2))
    body) (LabelSwap.onHeaders (p := 0) clear)

def exchange [M8.Machine.Net] (io : Fin T) (p : Pair k) := atPair p (LabelSwap.program io)

theorem atPair_runs (p : Pair k) {body : Graph.Block (T+24) prime} (hl : Blocks.Leading body)
    {roles roles' : Tapes T prime} {v : Descriptor} {c cost : ℕ}
    (h : let d := LabelPrepare.input v k p.val.1 p.val.2 c
         GraphContract.Runs body (bank roles v d) (bank roles' v d) cost) :
    let d := words (base v c)
    GraphContract.Runs (atPair p body) (bank roles v d) (bank roles' v d)
      (setupCost k p.val.1 p.val.2 + cost + clearCost k p.val.1 p.val.2 + 2) := by
  have hset := LabelSwap.onHeaders_runs (p := 0) roles v (M := setup k p.val.1 p.val.2)
    (d := words (base v c)) (e := LabelPrepare.input v k p.val.1 p.val.2 c)
    (by simpa only [LabelSwap.append_zero] using setup_runs v k p.val.1 p.val.2 c)
  have hend := LabelSwap.onHeaders_runs (p := 0) roles' v (M := clear)
    (d := LabelPrepare.input v k p.val.1 p.val.2 c) (e := words (base v c))
    (by simpa only [LabelSwap.append_zero] using clear_runs v k p.val.1 p.val.2 c)
  have h₁ := Blocks.seq_runs (LabelSwap.headers_leading _) hl hset h
  exact Blocks.runs_mono (Blocks.seq_runs (Blocks.seq_leading _ _) (LabelSwap.headers_leading _) h₁ hend)
    (by omega)

theorem exchange_runs [M8.Machine.Net] {v : Descriptor} {c B : ℕ} (p : Pair k)
    (hc : 0 < c) (hb : 0 < B) (hv : v.beforeH = B*prime^(k*c)) (hp : v.Positive)
    (roles : Tapes T prime) (io : Fin T) (x : Fin (volume prime v) → ZMod 2)
    (hh : roles.head io = 0) (hx : roles.tape io = sourceWord x) :
    let s := p.val.1.val
    let t := p.val.2.val
    let d := words (base v c)
    ∃ y : Fin (volume prime v) → ZMod 2,
      LabelView.Swapped prime (LabelView.colView prime c k s t B v) (ext x) (ext y) ∧
      GraphContract.Runs (exchange io p) (bank roles v d) (bank (setTape roles io (sourceWord y) 0) v d)
        (setupCost k s t + (3808274 * volume prime v + LeafCore.coreCost (volume prime v) c) +
          clearCost k s t + 2) := by
  obtain ⟨y, hy, h⟩ := LabelSwap.runs p.property p.val.2.isLt hc hb hv hp roles io x hh hx
  exact ⟨y, hy, atPair_runs p (Blocks.seq_leading _ _) h⟩

/-- Execute the exchanges in list order on a common role and descriptor bank. -/
def schedule [M8.Machine.Net] (io : Fin T) : List (Pair k) → Graph.Block (T+24) prime
  | [] => SharedBankSkeleton.identity _ _ (by omega)
  | p :: ps => Blocks.seqB (exchange io p) (schedule io ps)

theorem schedule_leading [M8.Machine.Net] (io : Fin T) (ps : List (Pair k)) :
    Blocks.Leading (schedule io ps) := by cases ps <;> exact fun _ => rfl

/-- Entrywise specification for the intermediate arrays of a column permutation. -/
def Swaps (v : Descriptor) (c B : ℕ) : List (Pair k) → (ℕ → ZMod 2) → (ℕ → ZMod 2) → Prop
  | [], x, y => x = y
  | p :: ps, x, y => ∃ z, LabelView.Swapped prime (LabelView.colView prime c k p.val.1 p.val.2 B v) x z ∧
      Swaps v c B ps z y

def countCost (ps : List (Pair k)) :=
  (ps.map fun p => setupCost k p.val.1 p.val.2 + clearCost k p.val.1 p.val.2 + 3).sum

private theorem cost_cons (p : Pair k) (ps : List (Pair k)) (b : ℕ) :
    setupCost k p.val.1 p.val.2 + b + clearCost k p.val.1 p.val.2 + 2 +
      (countCost ps + ps.length*b) + 1 ≤ countCost (p::ps) + (p::ps).length*b := by
  simp only [countCost, List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
  omega

theorem schedule_runs [M8.Machine.Net] {v : Descriptor} {c B : ℕ} (ps : List (Pair k))
    (hc : 0 < c) (hb : 0 < B) (hv : v.beforeH = B*prime^(k*c)) (hp : v.Positive)
    (roles : Tapes T prime) (io : Fin T) (x : Fin (volume prime v) → ZMod 2)
    (hh : roles.head io = 0) (hx : roles.tape io = sourceWord x) :
    let d := words (base v c)
    ∃ y : Fin (volume prime v) → ZMod 2, Swaps v c B ps (ext x) (ext y) ∧
      GraphContract.Runs (schedule io ps) (bank roles v d) (bank (setTape roles io (sourceWord y) 0) v d)
        (countCost ps + ps.length * (3808274 * volume prime v + LeafCore.coreCost (volume prime v) c)) := by
  induction ps generalizing roles x with
  | nil =>
    have hself : setTape roles io (sourceWord x) 0 = roles := by
      rw [← hh, ← hx]
      simp [setTape, Function.update_eq_self]
    refine ⟨x, rfl, ?_⟩
    rw [hself]
    rw [show countCost ([] : List (Pair k)) = 0 from rfl, List.length_nil, Nat.zero_mul, Nat.zero_add]
    exact skip_hoare _ _
  | cons p ps ih =>
    obtain ⟨z, hz, hr⟩ := exchange_runs p hc hb hv hp roles io x hh hx
    obtain ⟨y, hy, ht⟩ := ih (setTape roles io (sourceWord z) 0) z
      (by simp [setTape]) (by simp [setTape])
    simp only [SharedPlacementAlphabet.setTape_setTape] at ht
    refine ⟨y, ⟨ext z, hz, hy⟩, ?_⟩
    have h := Blocks.seq_runs (Blocks.seq_leading _ _) (schedule_leading io ps) hr
      (by simpa only [SharedPlacementAlphabet.setTape_setTape] using ht)
    exact Blocks.runs_mono h (cost_cons p ps _)

/-- Choose the fixed exchange schedule before seeing the runtime descriptor or data. -/
theorem permutation_schedule [M8.Machine.Net] (π : Equiv.Perm (Fin k)) (io : Fin T) :
    ∃ ps : List (Pair k), π = (ps.map fun p => Equiv.swap p.val.1 p.val.2).prod ∧
      ps.length ≤ k-1 ∧ ∀ (v : Descriptor) (c B : ℕ), 0 < c → 0 < B →
        v.beforeH = B*prime^(k*c) → v.Positive → ∀ (roles : Tapes T prime)
        (x : Fin (volume prime v) → ZMod 2), roles.head io = 0 → roles.tape io = sourceWord x →
        ∃ y : Fin (volume prime v) → ZMod 2, Swaps v c B ps (ext x) (ext y) ∧
          GraphContract.Runs (schedule io ps) (bank roles v (words (base v c)))
            (bank (setTape roles io (sourceWord y) 0) v (words (base v c)))
            (countCost ps + (k-1)*(3808274 * volume prime v + LeafCore.coreCost (volume prime v) c)) := by
  obtain ⟨ps, hn, he⟩ := Route.swaps_le π
  refine ⟨ps, he, hn, ?_⟩
  intro v c B hc hb hv hp roles x hh hx
  obtain ⟨y, hy, hr⟩ := schedule_runs ps hc hb hv hp roles io x hh hx
  exact ⟨y, hy, Blocks.runs_mono hr (Nat.add_le_add_left (Nat.mul_le_mul_right _ hn) _)⟩

end
end IntegerMultBounds.MathlibTM2.Cover.LabelSchedule
