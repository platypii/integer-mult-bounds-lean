module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardWindow
public import IntegerMultBounds.MathlibTM2.Fast.TableProg

/-! # Compute the ring logarithm by an executed doubling loop -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.MathlibTM2.Fast.TableVM

def tblChirpForwardRing : TblCode 4 :=
  .seq (tblBlock 4 [.add 0 0 1, .add 1 0 1, .add 1 1 1, .add 1 0 1, .zero 2, .inc 2] (.zero 3))
    (.loop 2 1 (tblBlock 4 [.add 2 2 2] (.inc 3)))

/-- From m alone, compute the smallest ring power covering 7m and its logarithm. -/
theorem tblChirpForwardRing_do {A W e : ℕ} (st : TblSt 4 A) (m : ℕ)
    (hm : st.val 0 = m) (hm0 : 1 ≤ m) (hroom : 14 * m + 1 < 2 ^ W) :
    TblDo A W e tblChirpForwardRing st
      (fun z => z.val = ![m, 7 * m, 2 ^ Nat.clog 2 (7 * m), Nat.clog 2 (7 * m)] ∧
        z.acc = st.acc ∧ ∀ i, z.val i < 2 ^ W) (4 * Nat.clog 2 (7 * m) + 9) := by
  have hW : W ≠ 0 := by intro h; subst W; norm_num at hroom
  have h7 : m + m + m + (m + m + m) + m = 7 * m := by omega
  let N := Nat.clog 2 (7 * m)
  have hN : N ≤ 7 * m := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
  let st₁ : TblSt 4 A := ⟨Function.update (Function.update (Function.update st.val 1 (7 * m)) 2 1) 3 0, st.acc⟩
  have hi : TblDo A W e (tblBlock 4 [.add 0 0 1, .add 1 0 1, .add 1 1 1, .add 1 0 1, .zero 2, .inc 2] (.zero 3))
      st (fun z => z = st₁) 7 := TblDo.block _ _
    (by simp [tblFitsList, TblIns.fits, TblIns.exact, hm, hW]; omega)
    (by simp [tblExactList, TblIns.exact, st₁, hm, h7])
  let Inv := fun j (z : TblSt 4 A) => z.val 0 = m ∧ z.val 1 = 7 * m ∧
    z.val 2 = 2 ^ j ∧ z.val 3 = j ∧ z.acc = st.acc ∧ 2 ^ j ≤ 14 * m
  have hl : TblDo A W e (.loop 2 1 (tblBlock 4 [.add 2 2 2] (.inc 3))) st₁
      (Inv N) (N * 4 + 2) := by
    apply TblDo.loop Inv N 2
    · simp [Inv, st₁, hm]; omega
    · intro j hj z ⟨h0, h1, h2, h3, ha, hb⟩
      have hpow : 2 ^ j < 7 * m := Nat.pow_lt_of_lt_clog hj
      refine ⟨by rw [h2, h1]; exact hpow, TblDo.block _ _ ?_ ?_⟩
      · simp [tblFitsList, TblIns.fits, TblIns.exact, h2, h3]
        constructor <;> omega
      · simp [Inv, tblExactList, TblIns.exact, h0, h1, h2, h3, ha, pow_succ]
        omega
    · intro z hz
      refine ⟨?_, hz⟩
      rcases hz with ⟨_, h1, h2, _⟩
      rw [h2, h1]
      exact Nat.not_lt.mpr (Nat.le_pow_clog (by decide) _)
  have hr := hi.seq (fun z hz => by cases hz; exact hl)
  exact hr.mono
    (fun z ⟨h0, h1, h2, h3, ha, hb⟩ => ⟨by
      funext i
      fin_cases i <;> simp [h0, h1, h2, h3, N], ha, by
      intro i
      fin_cases i <;> simp [h0, h1, h2, h3] <;> omega⟩) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
