module

public import IntegerMultBounds.MathlibTM2.Cover.LabelPrepareClean
public import IntegerMultBounds.MathlibTM2.Cover.LabelExchange

/-! Call the interchange supplier directly on the output ports of header preparation. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelCall
noncomputable section

open IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2.M8.RevMachine
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open LabelView (colView Swapped)
open SharedPlacementAlphabet (setTape)
variable {T : ℕ}

/-- The two row headers stay with the caller. The other four are read in place. -/
def ports : Fin 6 → Fin (T + (2+22)) := fun i =>
  Fin.natAdd T (![0,1,10,8,17,15] i : Fin (2+22))

def bank (roles : Tapes T prime) (v : Descriptor) (d : Fin 22 → Option (List Bool)) :=
  let rows : Tapes 2 prime :=
    ⟨fun _ => 1, fun i => RadixZeroFill.encodedBinary (![Routines.hdr v 0, Routines.hdr v 1] i)⟩
  roles.append (rows.append (Headers.bank d))

theorem runs [M8.Machine.Net] {v : Descriptor} {k s t c B : ℕ} (hs : s < t) (ht : t < k)
    (hv : v.beforeH = B * prime^(k*c)) (hp : v.Positive) (roles : Tapes T prime)
    (io : Fin T) (x : Fin (volume prime v) → ZMod 2)
    (hh : roles.head io = 0) (hx : roles.tape io = sourceWord x) :
    let d := LabelPrepareClean.output prime v k s t c B
    let u := colView prime c k s t B v
    ∃ y : Fin (volume prime v) → ZMod 2, Swapped prime u (ext x) (ext y) ∧
      HoareTime (M8.Machine.ArbitraryWidthOriginalTotalRun.program ports (Fin.castAdd 24 io))
        (fun w => w = M8.Machine.ArbitraryWidthOriginalTotalRun.input (bank roles v d))
        (fun w => w = M8.Machine.ArbitraryWidthOriginalTotalRun.input
          (bank (setTape roles io (sourceWord y) 0) v d)) (M8.Machine.ArbitraryWidthOriginalTotalRun.cost u (Routines.hdr u)) := by
  let d := LabelPrepareClean.output prime v k s t c B
  let u := colView prime c k s t B v
  have hvol : volume prime u = volume prime v := LabelView.colView_volume _ _ _ _ _ _ _ hv hs ht
  have hu : u.Positive := LeafCore.positive_of_volume
    (hvol ▸ RecursiveAffinePrepare.volume_positive Networks.Shared50ModularControl.prime_prime.two_le v hp)
  let z := fun i : Fin (volume prime u) => x (Fin.cast hvol i)
  let y := RevSemantics.leafOut u hvol x
  refine ⟨y, LabelExchange.leafOut_swapped hvol x, ?_⟩
  have h := M8.Machine.ArbitraryWidthOriginalTotalRun.runs (bank roles v d) ports (Fin.castAdd 24 io)
    u (Routines.hdr u) hu (Routines.hdr_headers u)
    (fun i => by fin_cases i <;> simp only [bank, ports, Tapes.append, Fin.addCases_right] <;> rfl)
    (fun i => by fin_cases i <;> simp only [bank, ports, Tapes.append, Fin.addCases_right] <;> rfl)
    z (by simpa only [bank, Tapes.append, Fin.addCases_left] using
      hx.trans (LeafCore.sourceWord_cast hvol x).symm)
    (by simpa only [bank, Tapes.append, Fin.addCases_left] using hh)
  have hout : sourceWord y = sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd u.rows) z) :=
    LeafCore.sourceWord_cast hvol.symm _
  apply h.consequence (fun _ h => h) ?_ ?_
  · intro w hw
    rw [hw, ← hout]
    simp only [bank, d, SharedPlacementAlphabet.setTape_append_left]
  · exact le_rfl

end
end IntegerMultBounds.MathlibTM2.Cover.LabelCall
