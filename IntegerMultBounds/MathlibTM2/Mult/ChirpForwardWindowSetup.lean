module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardWindow
public import IntegerMultBounds.MathlibTM2.Fast.TableProg

/-! # Execute the selected square-root window from p and α

Increment the integer root until its square exceeds p, then multiply by α.
The loop invariant proves the result is α(⌊√p⌋+1); no square-root input is supplied.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.MathlibTM2.Fast.TableVM

def tblChirpForwardWindow : TblCode 6 :=
  .seq (tblBlock 6 [.zero 4, .zero 3, .copy 0 2] (.inc 2))
    (.seq (.loop 4 2 (tblBlock 6 [.inc 3] (.mul 3 3 4))) (.ins (.mul 1 3 5)))

def chirpForwardWindowValues (p α : ℕ) : Fin 6 → ℕ :=
  ![p, α, p + 1, Nat.sqrt p + 1, (Nat.sqrt p + 1) ^ 2, chirpForwardWindow p α]

/-- The root search and multiplication execute in O(√p) table atoms, with all fits derived. -/
theorem tblChirpForwardWindow_do {A W w : ℕ} (st : TblSt 6 A) (p α : ℕ)
    (hp : st.val 0 = p) (hα : st.val 1 = α) (hp0 : 1 ≤ p) (hαp : α ^ 2 ≤ p)
    (hW : 4 * p < 2 ^ W) :
    TblDo A W w tblChirpForwardWindow st
      (fun z => z.val = chirpForwardWindowValues p α ∧ z.acc = st.acc ∧
        ∀ i, z.val i < 2 ^ W) (4 * (Nat.sqrt p + 1) + 7) := by
  let N := Nat.sqrt p + 1
  have hN2 : N ^ 2 ≤ 4 * p := by
    have hs : 1 ≤ Nat.sqrt p := by have := Nat.sqrt_pos.mpr hp0; omega
    have hsq := Nat.sqrt_le' p
    dsimp [N]
    nlinarith
  have hN : N < 2 ^ W := (by nlinarith [Nat.le_mul_self N] : N ≤ 4 * p).trans_lt hW
  let st₁ : TblSt 6 A := ⟨Function.update (Function.update (Function.update st.val 4 0) 3 0) 2 (p + 1), st.acc⟩
  have hinit : TblDo A W w (tblBlock 6 [.zero 4, .zero 3, .copy 0 2] (.inc 2)) st
      (fun z => z = st₁) 4 := TblDo.block _ _
    (by simp [tblFitsList, TblIns.fits, TblIns.exact, hp]; omega)
    (by simp [tblExactList, TblIns.exact, st₁, hp])
  let Inv := fun j (z : TblSt 6 A) =>
    z.val 0 = p ∧ z.val 1 = α ∧ z.val 2 = p + 1 ∧ z.val 3 = j ∧ z.val 4 = j ^ 2 ∧ z.acc = st.acc
  have hloop : TblDo A W w (.loop 4 2 (tblBlock 6 [.inc 3] (.mul 3 3 4))) st₁
      (Inv N) (N * 4 + 2) := by
    apply TblDo.loop Inv N 2
    · simp [Inv, st₁, hp, hα]
    · intro j hj z ⟨h0, h1, h2, h3, h4, ha⟩
      have hjroot : j ≤ Nat.sqrt p := by dsimp [N] at hj; omega
      have hj2 : j ^ 2 ≤ p := (Nat.pow_le_pow_left hjroot _).trans (Nat.sqrt_le' p)
      have hjN : j + 1 ≤ N := by omega
      have hjW : (j + 1) ^ 2 < 2 ^ W := (Nat.pow_le_pow_left hjN _).trans_lt (hN2.trans_lt hW)
      refine ⟨by rw [h4, h2]; omega, TblDo.block _ _ ?_ ?_⟩
      · simp [tblFitsList, TblIns.fits, TblIns.exact, h3]
        exact ⟨by omega, by simpa only [pow_two] using hjW⟩
      · simp [Inv, tblExactList, TblIns.exact, h0, h1, h2, h3, ha, pow_two]
    · intro z hz
      refine ⟨?_, hz⟩
      rcases hz with ⟨_, _, h2, _, h4, _⟩
      rw [h4, h2]
      have hlast : p < (Nat.sqrt p + 1) ^ 2 := by
        simpa only [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' p
      dsimp [N]
      omega
  have hr : TblDo A W w tblChirpForwardWindow st
      (fun z => z.val = chirpForwardWindowValues p α ∧ z.acc = st.acc ∧ ∀ i, z.val i < 2 ^ W)
      (4 + ((N * 4 + 2) + 1)) := hinit.seq (fun z hz => by
    cases hz
    exact hloop.seq (fun z ⟨h0, h1, h2, h3, h4, ha⟩ => by
      have hmW : α * N < 2 ^ W :=
        (chirpForwardWindow_le p α hαp).trans_lt (by omega)
      have hlast : tblFitsList A W w [.mul 1 3 5] z := by
        simpa [tblFitsList, TblIns.fits, h1, h3] using hmW
      exact (TblDo.block [] (.mul 1 3 5) hlast ⟨by
        funext i
        fin_cases i <;> simp [tblExactList, TblIns.exact, chirpForwardWindowValues,
          chirpForwardWindow, N, h0, h1, h2, h3, h4], by simpa [tblExactList, TblIns.exact] using ha,
        by
          intro i
          fin_cases i <;> simp [tblExactList, TblIns.exact, h0, h1, h2, h3, h4]
          all_goals first
            | exact hmW
            | exact hN
            | exact hN2.trans_lt hW
            | nlinarith [Nat.sqrt_le_self p, Nat.le_sqrt'.mpr hαp]⟩)))
  exact hr.mono (fun _ h => h) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
