import IntegerMultBounds.Machine.CompactGlobalRowInitialCleanup

/-! Exact complete execution of global row padding from the four original
public numbers. Every computed header and private tape is erased. Only the
source interval is consumed and the complete padded destination is written. -/
namespace IntegerMultBounds.Machine.CompactGlobalRowInitialRun
noncomputable section
open CompactGlobalRowHeaders (initial recordWidth)
open CompactGlobalRowPadding
open CompactGlobalRowInitialData (bank)
variable {a : ℕ}

def program (c m : ℕ) := seq
  (seq (CompactGlobalRowInitialData.prepare (a := a) c m) CompactGlobalRowInitialData.padProgram)
  CompactGlobalRowInitialCleanup.program

def cost (c m d D K P : ℕ) := CompactGlobalRowHeaders.cost c m d D K P+
  413*(initialRows c m d K*recordWidth c m d D K P)+
  CompactGlobalRowInitialCleanup.cost c m d D K P+2

theorem runs (c m d D K P : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hK : 0<K) (hp : 0<P) (hD : rowAxes c m d≤D)
    (source dest : ℤ → Fin 4) (p q : ℤ)
    (x : Fin (1*originalRows c m d K*recordWidth c m d D K P) → Bool) :
    HoareTime (program (a := a) c m)
      (fun v => v=bank (initial K d D P)
        (putWord (RowPaddingConstructedAlphabet.mapTape source) p (List.ofFn (fun i => bitSymbol (x i))))
        (RowPaddingConstructedAlphabet.mapTape dest) p q)
      (fun v => v=bank (initial K d D P)
        (RowPaddingConstructedAlphabet.erased
          (putWord (RowPaddingConstructedAlphabet.mapTape source) p (List.ofFn (fun i => bitSymbol (x i))))
          p (1*originalRows c m d K*recordWidth c m d D K P))
        (putWord (RowPaddingConstructedAlphabet.mapTape dest) q
          (List.ofFn (RecursiveRowPadding.pad (initialRows c m d K) (bitSymbol false) (fun i => bitSymbol (x i))))) p q)
      (cost c m d D K P) := by
  have h0 := CompactGlobalRowInitialData.prepares (a := a) c m d D K P hc hm hd hK hp hD
    (putWord (RowPaddingConstructedAlphabet.mapTape source) p (List.ofFn (fun i => bitSymbol (x i))))
    (RowPaddingConstructedAlphabet.mapTape dest) p q
  have h1 := CompactGlobalRowInitialData.pads (a := a) c m d D K P hc hK hp source dest p q x
  have h2 := CompactGlobalRowInitialCleanup.runs (a := a) c m d D K P
    (RowPaddingConstructedAlphabet.erased
      (putWord (RowPaddingConstructedAlphabet.mapTape source) p (List.ofFn (fun i => bitSymbol (x i))))
      p (1*originalRows c m d K*recordWidth c m d D K P))
    (putWord (RowPaddingConstructedAlphabet.mapTape dest) q
      (List.ofFn (RecursiveRowPadding.pad (initialRows c m d K) (bitSymbol false) (fun i => bitSymbol (x i))))) p q
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

/-- Reinterpreting the initial row boundary retains every original address. -/
theorem original_volume (c m d D K P : ℕ) (hD : rowAxes c m d≤D) :
    originalRows c m d K*recordWidth c m d D K P=2^(D*K)*P := by
  unfold originalRows recordWidth
  rw [← Nat.mul_assoc,← pow_add]
  congr 2
  have he := Nat.add_sub_of_le hD
  nlinarith

/-- The actual output is whole-row padding and crops to the original literal
array, independently of temporary/control/spectator/payload contents. -/
theorem crop_pad (c m d D K P : ℕ) (hc : 2≤c) (hK : 0<K)
    (x : Fin (1*originalRows c m d K*recordWidth c m d D K P) → Bool) :
    RecursiveRowPadding.crop (initial_bounds c m d K (by omega) hK).1
      (RecursiveRowPadding.pad (initialRows c m d K) (bitSymbol (a := a) false)
        (fun i => bitSymbol (x i))) = fun i => bitSymbol (x i) :=
  RecursiveRowPadding.crop_pad _ _ _

end
end IntegerMultBounds.Machine.CompactGlobalRowInitialRun
