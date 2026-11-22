module

public import IntegerMultBounds.MathlibTM2.Cover.LabelCall

/-! One clean column exchange, from the staged dimension words back to the same words. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelSwap
noncomputable section

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.M8.RevMachine
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open RecursiveInterchangeLayout (Descriptor volume)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open SharedBankStageInput (raw)
open GraphContract (Runs)
open LabelCall (bank)
variable {T p r : ℕ}

def slot : Fin (22+p) → Fin ((T+24)+p) :=
  Fin.addCases (fun i => Fin.castAdd p (Fin.natAdd T (Fin.natAdd 2 i))) (Fin.natAdd (T+24))

theorem slot_injective : Function.Injective (slot (T := T) (p := p)) := by
  have h (i : Fin (22+p)) : (slot (T := T) i).val = T+2+i.val := by
    induction i using Fin.addCases <;> simp [slot] <;> omega
  intro i j hij
  apply Fin.ext
  have := congrArg Fin.val hij
  rw [h, h] at this
  omega

def onHeaders (M : Program (22+p) r prime) : Graph.Block (T+24) prime :=
  Embed.place M slot slot_injective (u := T+2) (by omega)

private theorem reads (roles : Tapes T prime) (v : Descriptor) (d : Fin 22 → Option (List Bool))
    (i : Fin (22+p)) :
    let w := raw (bank roles v d) ((T+24)+p)
    let z := (Headers.bank (q := prime) d).append (SharedBank.empty p prime)
    w.head (slot i) = z.head i ∧ w.tape (slot i) = z.tape i := by
  induction i using Fin.addCases with
  | left i =>
    simpa only [slot, Fin.addCases_left, Tapes.append, LabelCall.bank, Fin.addCases_right]
      using Embed.raw_left (p := p) (bank roles v d) (Fin.natAdd T (Fin.natAdd 2 i))
  | right i =>
    simpa only [slot, Fin.addCases_right, Tapes.append, SharedBank.empty]
      using Embed.raw_right (bank roles v d) i

theorem onHeaders_runs {M : Program (22+p) r prime} {d e : Fin 22 → Option (List Bool)} {cost : ℕ}
    (roles : Tapes T prime) (v : Descriptor)
    (h : HoareTime M (fun w => w = (Headers.bank d).append (SharedBank.empty p prime))
      (fun w => w = (Headers.bank e).append (SharedBank.empty p prime)) cost) :
    Runs (onHeaders M) (bank roles v d) (bank roles v e) cost := by
  apply Embed.place_runs h slot slot_injective (u := T+2) (by omega) _ _
    (reads roles v d) (reads roles v e)
  intro j hj
  induction j using Fin.addCases with
  | left j => simp [bank, Tapes.append]
  | right j =>
    change Fin (2+22) at j
    induction j using Fin.addCases with
    | left j => simp [bank, Tapes.append]
    | right i => exact (hj (Fin.castAdd p i) (by simp [slot])).elim

abbrev supplierSize [M8.Machine.Net] (T : ℕ) := M8.Machine.ArbitraryWidthOriginalZeroBranch.count (T+24)

theorem fits [M8.Machine.Net] : T+24 ≤ supplierSize T := by
  simp only [supplierSize, M8.Machine.ArbitraryWidthOriginalZeroBranch.count,
    M8.Machine.ArbitraryWidthOriginalZeroBranch.highCount]
  omega

def leadingBlock {k n r a : ℕ} (hk : k ≤ n) (M : Program n r a) : Graph.Block k a where
  tapes := n
  states := r
  program := M
  slots := Fin.castLE hk
  slots_injective := Fin.castLE_injective _

theorem leadingBlock_runs {k n r a : ℕ} (hk : k ≤ n) (M : Program n r a)
    {x y : Tapes k a} {b : ℕ} (h : HoareTime M (fun w => w = raw x n) (fun w => w = raw y n) b) :
    Runs (leadingBlock hk M) x y b := h

theorem leadingBlock_leading {k n r a : ℕ} (hk : k ≤ n) (M : Program n r a) :
    Blocks.Leading (leadingBlock hk M) := fun _ => rfl

abbrev supplier [M8.Machine.Net] (io : Fin T) :=
  leadingBlock fits (M8.Machine.ArbitraryWidthOriginalTotalRun.program LabelCall.ports (Fin.castAdd 24 io))

theorem headers_leading (M : Program (22+p) r prime) : Blocks.Leading (onHeaders (T := T) M) :=
  fun _ => rfl

def withView (body : Graph.Block (T+24) prime) :=
  Blocks.seqB (Blocks.seqB (onHeaders (LabelPrepareClean.program prime_prime.two_le)) body)
    (onHeaders (p := 0) (LabelPrepareClean.release prime))

def program [M8.Machine.Net] (io : Fin T) := withView (supplier io)

theorem append_zero (d : Fin 22 → Option (List Bool)) :
    (Headers.bank (q := prime) d).append (SharedBank.empty 0 prime) = Headers.bank d := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

/-- Surround any operation on the prepared view with the same header setup and release. -/
theorem withView_runs {v : Descriptor} {k s t c B cost : ℕ} (hs : s < t) (ht : t < k)
    (hc : 0 < c) (hb : 0 < B) (hv : v.beforeH = B*prime^(k*c)) (hp : v.Positive)
    {roles roles' : Tapes T prime} {body : Graph.Block (T+24) prime} (hl : Blocks.Leading body)
    (hbody : let d := LabelPrepareClean.output prime v k s t c B
             Runs body (bank roles v d) (bank roles' v d) cost) :
    let d := LabelPrepare.input v k s t c
    Runs (withView body) (bank roles v d) (bank roles' v d) (3808274 * volume prime v + cost) := by
  have hpre := onHeaders_runs roles v (LabelPrepareClean.prepares prime_prime.two_le v k s t c B
    hs ht hc hb hp hv)
  have hrel := LabelPrepareClean.restores (q := prime) v k s t c B
  have hend := onHeaders_runs (p := 0) roles' v
    (d := LabelPrepareClean.output prime v k s t c B) (e := LabelPrepare.input v k s t c)
    (M := LabelPrepareClean.release prime) (by simpa only [append_zero] using hrel)
  have h₁ := Blocks.seq_runs (s := onHeaders (LabelPrepareClean.program prime_prime.two_le))
    (r := body) (headers_leading _) hl hpre hbody
  refine Blocks.runs_mono (Blocks.seq_runs (Blocks.seq_leading _ _) (headers_leading _) h₁ hend) ?_
  let u := LabelView.colView prime c k s t B v
  have hvol : volume prime u = volume prime v := LabelView.colView_volume _ _ _ _ _ _ _ hv hs ht
  have hV := RecursiveAffinePrepare.volume_positive prime_prime.two_le v hp
  obtain ⟨ha, hm, he⟩ := LabelPrepare.factors u (hvol ▸ hV)
  rw [hvol] at ha hm he
  have h₁ := FlatCoordinateDimensions.bits_length_le_twice ha hV
  have h₂ := FlatCoordinateDimensions.bits_length_le_twice hm hV
  have h₃ := FlatCoordinateDimensions.bits_length_le_twice he hV
  dsimp only [u] at h₁ h₂ h₃
  omega

theorem runs_at_view_cost [M8.Machine.Net] {v : Descriptor} {k s t c B : ℕ} (hs : s < t) (ht : t < k)
    (hc : 0 < c) (hb : 0 < B) (hv : v.beforeH = B*prime^(k*c)) (hp : v.Positive)
    (roles : Tapes T prime) (io : Fin T) (x : Fin (volume prime v) → ZMod 2)
    (hh : roles.head io = 0) (hx : roles.tape io = sourceWord x) :
    let d := LabelPrepare.input v k s t c
    let u := LabelView.colView prime c k s t B v
    ∃ y : Fin (volume prime v) → ZMod 2, LabelView.Swapped prime u (ext x) (ext y) ∧
      Runs (program io) (bank roles v d)
        (bank (SharedPlacementAlphabet.setTape roles io (sourceWord y) 0) v d)
        (3808274 * volume prime v + M8.Machine.ArbitraryWidthOriginalTotalRun.cost u (Routines.hdr u)) := by
  obtain ⟨y, hy, hcall⟩ := LabelCall.runs hs ht hv hp roles io x hh hx
  rw [LeafCore.input_eq, LeafCore.input_eq] at hcall
  have hsup := leadingBlock_runs fits _ hcall
  exact ⟨y, hy, withView_runs hs ht hc hb hv hp (leadingBlock_leading _ _) hsup⟩

theorem runs [M8.Machine.Net] {v : Descriptor} {k s t c B : ℕ} (hs : s < t) (ht : t < k)
    (hc : 0 < c) (hb : 0 < B) (hv : v.beforeH = B*prime^(k*c)) (hp : v.Positive)
    (roles : Tapes T prime) (io : Fin T) (x : Fin (volume prime v) → ZMod 2)
    (hh : roles.head io = 0) (hx : roles.tape io = sourceWord x) :
    let d := LabelPrepare.input v k s t c
    let u := LabelView.colView prime c k s t B v
    ∃ y : Fin (volume prime v) → ZMod 2, LabelView.Swapped prime u (ext x) (ext y) ∧
      Runs (program io) (bank roles v d)
        (bank (SharedPlacementAlphabet.setTape roles io (sourceWord y) 0) v d)
        (3808274 * volume prime v + LeafCore.coreCost (volume prime v) c) := by
  obtain ⟨y, swap, run⟩ := runs_at_view_cost hs ht hc hb hv hp roles io x hh hx
  let u := LabelView.colView prime c k s t B v
  have volume_eq := LabelView.colView_volume prime c k s t B v hv hs ht
  have positive : u.Positive := LeafCore.positive_of_volume
    (volume_eq ▸ RecursiveAffinePrepare.volume_positive prime_prime.two_le v hp)
  refine ⟨y, swap, Blocks.runs_mono run (Nat.add_le_add_left ?_ _)⟩
  simpa only [u, volume_eq, show (LabelView.colView prime c k s t B v).width = c from rfl]
    using LeafCore.cost_le positive

end
end IntegerMultBounds.MathlibTM2.Cover.LabelSwap
