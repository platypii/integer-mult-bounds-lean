module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardWindowSetup
public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardRingSetup
public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardPrecisionSetup

/-! # One program computes the selected forward parameters from p and α -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.MathlibTM2.Fast.TableVM

namespace ForwardParameters

def window : Fin 6 → Fin 13 := fun i => ⟨i.val, by omega⟩
def ring : Fin 4 → Fin 13 := ![5, 6, 7, 8]
def precision : Fin 6 → Fin 13 := ![0, 8, 9, 10, 11, 12]

theorem window_inj : Function.Injective window := by
  intro i j h
  have hv := congrArg (fun x : Fin 13 => x.val) h
  exact Fin.ext hv
theorem ring_inj : Function.Injective ring := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [ring]
theorem precision_inj : Function.Injective precision := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [precision]

end ForwardParameters

def tblChirpForwardParameters : TblCode 13 :=
  .seq (tblChirpForwardWindow.rename ForwardParameters.window)
    (.seq (tblChirpForwardRing.rename ForwardParameters.ring)
      (tblChirpForwardPrecision.rename ForwardParameters.precision))

/-- All principal parameters are computed from the two original scalar words. -/
theorem tblChirpForwardParameters_do {A W e : ℕ} (st : TblSt 13 A) (p α : ℕ)
    (hp : st.val 0 = p) (hα : st.val 1 = α) (hp0 : 1 ≤ p)
    (hα0 : 1 ≤ α) (hαp : α ^ 2 ≤ p) (hroom : 125 * p < 2 ^ W) :
    let m := chirpForwardWindow p α
    let l := chirpForwardRingLog p α
    let Γ := chirpForwardGrowth p
    let q := chirpForwardPrecision p Γ l
    TblDo A W e tblChirpForwardParameters st
      (fun z => z.val 0 = p ∧ z.val 1 = α ∧ z.val 5 = m ∧ z.val 8 = l ∧
        z.val 9 = Γ ∧ z.val 10 = q ∧ z.val 11 = q + l + Γ + 5 ∧
        z.val 12 = p + l + Γ + 5 ∧ z.acc = st.acc ∧ ∀ i, z.val i < 2 ^ W)
      ((4 * (Nat.sqrt p + 1) + 7) + ((4 * l + 9) + 36)) := by
  dsimp only
  have hm0 : 1 ≤ chirpForwardWindow p α := by
    unfold chirpForwardWindow
    nlinarith [Nat.zero_le (Nat.sqrt p)]
  have hm := chirpForwardWindow_le p α hαp
  have hw := (chirpForwardWidths_le p α hp0 hαp).2.1
  have hwindow := (tblChirpForwardWindow_do (A := A) (W := W) (w := e)
    (st.restrict ForwardParameters.window) p α hp hα hp0 hαp (by omega)).rename ForwardParameters.window_inj
  unfold tblChirpForwardParameters
  refine hwindow.seq (fun z ⟨⟨hz, ha, hzfit⟩, hoff⟩ => ?_)
  have hval (i : Fin 6) : z.val (ForwardParameters.window i) = chirpForwardWindowValues p α i :=
    congrFun hz i
  have h0 : z.val 0 = p := hval 0
  have h1 : z.val 1 = α := hval 1
  have h5 : z.val 5 = chirpForwardWindow p α := hval 5
  have hring := (tblChirpForwardRing_do (A := A) (W := W) (e := e)
    (z.restrict ForwardParameters.ring) _ h5 hm0 (by omega)).rename ForwardParameters.ring_inj
  refine hring.seq (fun u ⟨⟨hu, hua, hufit⟩, huoff⟩ => ?_)
  have hrv (i : Fin 4) : u.val (ForwardParameters.ring i) =
      (![chirpForwardWindow p α, 7 * chirpForwardWindow p α,
        2 ^ Nat.clog 2 (7 * chirpForwardWindow p α), Nat.clog 2 (7 * chirpForwardWindow p α)] : Fin 4 → ℕ) i :=
    congrFun hu i
  have hu0 : u.val 0 = p := (huoff 0 (by intro i; fin_cases i <;> decide)).trans h0
  have hu1 : u.val 1 = α := (huoff 1 (by intro i; fin_cases i <;> decide)).trans h1
  have hu5 : u.val 5 = chirpForwardWindow p α := hrv 0
  have hu8 : u.val 8 = chirpForwardRingLog p α := hrv 3
  have hprec := (tblChirpForwardPrecision_do (A := A) (W := W) (e := e)
    (u.restrict ForwardParameters.precision) p (chirpForwardRingLog p α) hu0 hu8 (hw.trans_lt hroom)).rename
      ForwardParameters.precision_inj
  exact hprec.mono (fun x ⟨⟨hx, hxa, hxfit⟩, hxoff⟩ => by
    have hv (i : Fin 6) : x.val (ForwardParameters.precision i) =
        chirpForwardPrecisionValues p (chirpForwardRingLog p α) i := congrFun hx i
    refine ⟨hv 0, (hxoff 1 (by intro i; fin_cases i <;> decide)).trans hu1,
      (hxoff 5 (by intro i; fin_cases i <;> decide)).trans hu5, hv 1, hv 2, hv 3, hv 4, hv 5,
      hxa.trans (hua.trans ha), ?_⟩
    have keep (i : Fin 6) (hr : ∀ j, ForwardParameters.ring j ≠ ForwardParameters.window i)
        (hp : ∀ j, ForwardParameters.precision j ≠ ForwardParameters.window i) :
        x.val (ForwardParameters.window i) < 2 ^ W := by
      rw [hxoff _ hp, huoff _ hr]
      exact hzfit i
    have ringFit (i : Fin 4) (hp : ∀ j, ForwardParameters.precision j ≠ ForwardParameters.ring i) :
        x.val (ForwardParameters.ring i) < 2 ^ W := by
      rw [hxoff _ hp]
      exact hufit i
    intro i
    fin_cases i
    · exact hxfit 0
    · exact keep 1 (by intro j; fin_cases j <;> decide) (by intro j; fin_cases j <;> decide)
    · exact keep 2 (by intro j; fin_cases j <;> decide) (by intro j; fin_cases j <;> decide)
    · exact keep 3 (by intro j; fin_cases j <;> decide) (by intro j; fin_cases j <;> decide)
    · exact keep 4 (by intro j; fin_cases j <;> decide) (by intro j; fin_cases j <;> decide)
    · exact ringFit 0 (by intro j; fin_cases j <;> decide)
    · exact ringFit 1 (by intro j; fin_cases j <;> decide)
    · exact ringFit 2 (by intro j; fin_cases j <;> decide)
    · exact hxfit 1
    · exact hxfit 2
    · exact hxfit 3
    · exact hxfit 4
    · exact hxfit 5) (by rfl)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
