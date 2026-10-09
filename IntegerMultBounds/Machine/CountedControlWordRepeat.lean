import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatCopy
import IntegerMultBounds.Machine.ArbitraryWidthZeroHeaderShared

/-! Physical repetition of one original control word for an address-table
scan. The immutable runtime repetition descriptor is retained; the local
clock is physically initialized and erased, both output/source heads return
and no repeated control stream is supplied. -/
namespace IntegerMultBounds.Machine.CountedControlWordRepeat
noncomputable section
open BinaryAddressOffsetRepeatData (copies)
open BinaryAddressOffsetRepeatCopy (bank state)

def descriptor (bs : List Bool) : Tapes 1 0 :=
  ⟨fun _ => 1,fun _ => CountedLoopReuseAlphabet.binary bs⟩
def input (xs : List Bool) (g : ℤ → Fin 4) (p : ℤ) (bs : List Bool) :=
  ((bank xs g p).append (ArbitraryWidthZeroHeaderShared.empty (a := 0))).append (descriptor bs)
def output (xs : List Bool) (g : ℤ → Fin 4) (p : ℤ) (bs : List Bool) (n : ℕ) :=
  input xs (putWord g p ((copies xs n).map bitSymbol)) p bs

def setup := extend (ArbitraryWidthZeroHeaderShared.program (a := 0) (t := 2)) 1
def cleanup := extend (ArbitraryWidthZeroHeaderShared.cleanup (a := 0) (t := 2)) 1
def rewindPlacement : Fin (1+3) ≃ Fin 4 where
  toFun := ![1,0,2,3]
  invFun := ![1,0,2,3]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def rewind := reindex (extend (ReturnOrigin.program (a := 0)) 3) rewindPlacement
def program := seq (seq (seq setup
  (CountedLoopReuseAlphabet.program BinaryAddressOffsetRepeatCopy.program)) rewind) cleanup

theorem ready (body : Tapes 2 0) (bs : List Bool) :
    (body.append (ArbitraryWidthZeroHeaderShared.header (a := 0))).append (descriptor bs) =
      CountedLoopReuseAlphabet.bank body CountedLoopReuseAlphabet.empty
        (CountedLoopReuseAlphabet.binary bs) 1 1 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem returns (xs : List Bool) (g : ℤ → Fin 4) (p : ℤ) (bs : List Bool) (n : ℕ)
    (hg : g (p-1)=blank) :
    HoareTime rewind
      (fun z => z=CountedLoopReuseAlphabet.bank (state xs g p n)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary bs) 1 1)
      (fun z => z=CountedLoopReuseAlphabet.bank
        (bank xs (putWord g p ((copies xs n).map bitSymbol)) p)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary bs) 1 1)
      (n*xs.length+2) := by
  let extra : Tapes 3 0 :=
    ⟨![0,1,1],![putWord (fun _ => blank) 0 (xs.map bitSymbol),
      CountedLoopReuseAlphabet.empty,CountedLoopReuseAlphabet.binary bs]⟩
  have h := hoare_place (ReturnOrigin.return_hoare_at g p ((copies xs n).map bitSymbol)
    (ReturnOrigin.bits_nonblank _) hg) rewindPlacement extra
  simp only [List.length_map,BinaryAddressOffsetRepeatData.copies_length] at h
  have h0 : ((ReturnOrigin.cfg (putWord g p ((copies xs n).map bitSymbol))
      (p+(n*xs.length : ℕ)) 0).tapes.append extra).reindex rewindPlacement =
      CountedLoopReuseAlphabet.bank (state xs g p n) CountedLoopReuseAlphabet.empty
        (CountedLoopReuseAlphabet.binary bs) 1 1 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have h1 : ((ReturnOrigin.cfg (putWord g p ((copies xs n).map bitSymbol)) p 2).tapes.append extra).reindex rewindPlacement =
      CountedLoopReuseAlphabet.bank (bank xs (putWord g p ((copies xs n).map bitSymbol)) p)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary bs) 1 1 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  simpa only [rewind,h0,h1] using h

/-- Actual word copying, source returns, counted iteration and output rewind;
empty controls and zero repetitions are included. -/
theorem runs (xs : List Bool) (g : ℤ → Fin 4) (p : ℤ) (bs : List Bool) (n : ℕ)
    (hv : Counter.value bs=n) (hg : g (p-1)=blank) :
    HoareTime program (fun z => z=input xs g p bs)
      (fun z => z=output xs g p bs n)
      (n*(3*xs.length+9)+7*bs.length+31) := by
  have h0 := hoare_extend_eq (ArbitraryWidthZeroHeaderShared.constructs (bank xs g p)) (descriptor bs)
  rw [ready] at h0
  have h1 := CountedLoopReuseAlphabet.loop_hoare BinaryAddressOffsetRepeatCopy.program bs n
    (state xs g p) (fun _ => 2*xs.length+3) hv
    (fun i _ => BinaryAddressOffsetRepeatCopy.step xs g p i)
  have h2 := returns xs g p bs n hg
  have h3 := hoare_extend_eq (ArbitraryWidthZeroHeaderShared.cleans
    (bank xs (putWord g p ((copies xs n).map bitSymbol)) p)) (descriptor bs)
  rw [ready] at h3
  have he : state xs g p 0=bank xs g p := by simp [state,putWord]
  rw [he] at h1
  exact (((h0.seq h1).seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h) (by
    simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
    ring_nf
    omega)

/-- The descriptor cost is paid and absorbed for nonempty repetition ranges. -/
theorem cost_bound (xs : List Bool) (bs : List Bool) (n : ℕ)
    (hn : 0<n) (hv : Counter.value bs=n) (hc : GrowingCounterData.Canonical bs) :
    n*(3*xs.length+9)+7*bs.length+31 ≤ 54*n*(xs.length+1) := by
  have hl := GrowingCounterData.canonical_width bs hc
  rw [hv] at hl
  have hnlog := Nat.log2_le_self n
  nlinarith
end
end IntegerMultBounds.Machine.CountedControlWordRepeat
