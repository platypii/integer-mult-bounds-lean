import IntegerMultBounds.Schoenhage.LevelDown

/-! A whole level of the batched recursion on word tapes. The batch is a
flat list of residues, read as consecutive pairs; the down-sweep maps it to
the next level's batch, the up-sweep maps the next level's products, `K` at a
time, to this level's products. -/

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule

namespace Tp
abbrev tK : Fin 𝕋 := 54
end Tp

/-- Consecutive pairs of a flat list. -/
def pairsOf : List ℕ → List (ℕ × ℕ)
  | x :: y :: L => (x, y) :: pairsOf L
  | _ => []

/-- The next level's batch, as the tapes compute it. -/
def nextBatch (Np k M : ℕ) : List ℕ → List ℕ
  | x :: y :: L => zipFlat (tpieces Np k M x) (tpieces Np k M y) ++ nextBatch Np k M L
  | _ => []

/-! ### The down-sweep of a batch -/

/-- Every pair of `tIn`. -/
noncomputable def downBatch : Cmd 0 𝕋 := .loop tIn downPair

theorem length_zipFlat : ∀ (X Y : List ℕ), X.length = Y.length → (zipFlat X Y).length = 2 * X.length
  | [], [], _ => rfl
  | x :: X, y :: Y, h => by
    simp only [zipFlat, List.length_cons] at h ⊢
    rw [length_zipFlat X Y (by omega)]; ring

theorem batch_arith (A B N n : ℕ) :
    2 * (A + 10 * N + 100) + B + 100 + 2 + n * (A + 10 * N + B + 200) ≤
      (n + 1 + 1) * (A + 10 * N + B + 200) := by
  nlinarith

theorem runs_downBatch {N Np k M : ℕ} (hNp : 0 < Np) (hs : N = M * 2 ^ k) (hMN : M ≤ Np) :
    ∀ (L : List ℕ) (σ : Fin 𝕋 → WTape) (Il O : List (List Bool)), Even L.length →
      (∀ x ∈ L, x < 2 ^ N + 1) → LevelRegs N Np k M σ →
      σ cR = reg (Rules.ruler M (Np + 1) (2 ^ k)) → σ pKh = reg (ones (2 ^ k / 2)) →
      σ tX = emp → σ tY = emp → σ tD = emp → σ tIn = ⟨Il, rwds N L⟩ → σ tOut = ⟨O, []⟩ →
      Runs downBatch σ (· = Function.update (Function.update σ tIn ⟨(rwds N L).reverse ++ Il, []⟩)
          tOut ⟨(rwds Np (nextBatch Np k M L)).reverse ++ O, []⟩)
        (L.length * ((k + 2) * (5000 * (2 ^ k + 1) * (Np + 2)) + 10 * N + 2 ^ k * (20 * Np + 100) + 200))
  | [], σ, Il, O, _, _, _, _, _, _, _, _, hIn, hO => by
    refine (Runs.loop_done (by simp [hIn, rwds]) rfl).mono (fun σ' h' => ?_) (by simp)
    subst h'
    funext i; fin_cases i <;> tsimp [hIn, hO, rwds, nextBatch]
  | [_], _, _, _, he, _, _, _, _, _, _, _, _, _ => by simp at he
  | x :: y :: L, σ, Il, O, he, hv, hL, hR, hKh, hX, hY, hD0, hIn, hO => by
    have hx := hv x (by simp)
    have hy := hv y (by simp)
    have s1 := runs_downPair hNp hs hMN hx hy σ hL hR hKh hX hY hD0 (Il := Il) (Ir := rwds N L) (O := O)
      (by simpa [rwds] using hIn) hO
    set σ₁ := Function.update (Function.update σ tIn ⟨rwd N y :: rwd N x :: Il, rwds N L⟩)
        tOut ⟨(rwds Np (zipFlat (tpieces Np k M x) (tpieces Np k M y))).reverse ++ O, []⟩
    have hL₁ : LevelRegs N Np k M σ₁ := (hL.update tIn _ (by decide)).update tOut _ (by decide)
    have ih := runs_downBatch hNp hs hMN L σ₁ (rwd N y :: rwd N x :: Il)
      ((rwds Np (zipFlat (tpieces Np k M x) (tpieces Np k M y))).reverse ++ O)
      (by simpa [Nat.even_add_one, parity_simps] using he) (fun z hz => hv z (by simp [hz])) hL₁
      (by tsimp [σ₁, hR]) (by tsimp [σ₁, hKh]) (by tsimp [σ₁, hX]) (by tsimp [σ₁, hY]) (by tsimp [σ₁, hD0])
      (by tsimp [σ₁]) (by tsimp [σ₁])
    refine (Runs.loop_step (by simp [hIn, rwds]) (s1.mono (fun σ' h' => by rw [h']; exact ih) le_rfl)).mono
      (fun σ' h' => ?_) ?_
    · rw [h']
      funext i; fin_cases i <;> tsimp [σ₁, rwds, nextBatch, rwds_append]
    · simp only [List.length_cons]
      exact batch_arith _ _ _ _

/-! ### The up-sweep of a batch -/

/-- The level outputs of consecutive groups of `K` products. -/
noncomputable def upList (N K : ℕ) : ℕ → List ℕ → List ℕ
  | 0, _ => []
  | g + 1, Q => levelOut N (Q.take K) :: upList N K g (Q.drop K)

/-- Move the next group to `tD` and run its up-sweep. -/
noncomputable def upStep : Cmd 0 𝕋 :=
  .seq (moveN tK tIn tD tJ (by decide) (by decide)) <| .seq (rewind tK) <| .seq (rewind tD) upGroup

theorem upb_arith (K Np A C X g : ℕ) (hX : 5000 * (K * (Np + 2)) ≤ X) :
    K * (2 * (Np + 1) + 15) + 1 + (K + 2 + 1 + (K * (Np + 2) + 2 + 1 + (A + C + 5000))) + 2 +
      g * (A + X + C + 6000) ≤ (g + 1) * (A + X + C + 6000) := by
  nlinarith [Nat.zero_le (K * Np)]

/-- Every group of `tIn`. -/
noncomputable def upBatch : Cmd 0 𝕋 := .loop tIn upStep

set_option maxHeartbeats 1000000 in
theorem runs_upBatch {N : ℕ} (hN0 : N0 ≤ N) (hk : 2 ^ kOf N ∣ N) :
    ∀ (g : ℕ) (Q : List ℕ) (σ : Fin 𝕋 → WTape) (Il O : List (List Bool)),
      Q.length = g * 2 ^ kOf N → (∀ q ∈ Q, q < Fm (nextN N)) →
      LevelRegs N (nextN N) (kOf N) (pieceOf N) σ → σ tK = ⟨[], List.replicate (2 ^ kOf N) []⟩ →
      σ tD = emp → σ tIn = ⟨Il, rwds (nextN N) Q⟩ → σ tOut = ⟨O, []⟩ →
      Runs upBatch σ (· = Function.update (Function.update σ tIn ⟨(rwds (nextN N) Q).reverse ++ Il, []⟩)
          tOut ⟨(rwds N (upList N (2 ^ kOf N) g Q)).reverse ++ O, []⟩)
        (g * ((kOf N + 4) * (5000 * (2 ^ kOf N + 1) * (nextN N + 2)) + 24 * pieceOf N * 2 ^ kOf N +
          1000 * N + 6000))
  | 0, Q, σ, Il, O, hl, _, _, _, _, hIn, hO => by
    have : Q = [] := List.length_eq_zero_iff.mp (by simpa using hl)
    subst this
    refine (Runs.loop_done (by simp [hIn, rwds]) rfl).mono (fun σ' h' => ?_) (by simp)
    subst h'
    funext i; fin_cases i <;> tsimp [hIn, hO, rwds, upList]
  | g + 1, Q, σ, Il, O, hl, hv, hL, hK, hD0, hIn, hO => by
    have hKQ : (2 ^ kOf N) ≤ Q.length := by rw [hl]; nlinarith
    have hq : Q = Q.take (2 ^ kOf N) ++ Q.drop (2 ^ kOf N) := (List.take_append_drop (2 ^ kOf N) Q).symm
    have hP : (Q.take (2 ^ kOf N)).length = (2 ^ kOf N) := by simp; omega
    have s1 := runs_moveN (a := 0) (k := tK) (s := tIn) (d := tD) (j := tJ) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) ((nextN N) + 1) (List.replicate (2 ^ kOf N) []) σ [] Il (rwds (nextN N) (Q.take (2 ^ kOf N)))
      (rwds (nextN N) (Q.drop (2 ^ kOf N))) [] hK (by rw [hIn, ← rwds_append, ← hq]) (by simp [length_rwds, hP])
      (by simpa [emp] using hD0) (by rw [hL.2.1 tJ (by decide)]; rfl) (rwds_length_le (nextN N) _) (by simp)
    set σ₁ := Function.update (Function.update (Function.update σ tK ⟨(List.replicate (2 ^ kOf N) []).reverse ++ [], []⟩)
      tIn ⟨(rwds (nextN N) (Q.take (2 ^ kOf N))).reverse ++ Il, rwds (nextN N) (Q.drop (2 ^ kOf N))⟩) tD ⟨(rwds (nextN N) (Q.take (2 ^ kOf N))).reverse ++ [], []⟩
    have s2 := runs_rewind (a := 0) tK σ₁
    set σ₂ := Function.update σ₁ tK ⟨[], (σ₁ tK).left.reverse ++ (σ₁ tK).right⟩
    have s3 := runs_rewind (a := 0) tD σ₂
    set σ₃ := Function.update σ₂ tD ⟨[], (σ₂ tD).left.reverse ++ (σ₂ tD).right⟩
    have hL₃ : LevelRegs N (nextN N) (kOf N) (pieceOf N) σ₃ :=
      (((((hL.update tK _ (by decide)).update tIn _ (by decide)).update tD _ (by decide)).update tK _
        (by decide)).update tD _ (by decide))
    have hPv : ∀ p ∈ Q.take (2 ^ kOf N), p < Fm (nextN N) := fun p hp => hv p (List.mem_of_mem_take hp)
    have s4 := runs_upGroup_level hN0 hk (Q.take (2 ^ kOf N)) hP hPv σ₃ hL₃ (by tsimp [σ₃, σ₂, σ₁])
      (O := O) (by tsimp [σ₃, σ₂, σ₁, hO])
    set σ₄ := Function.update (Function.update σ₃ tD emp) tOut ⟨rwd N (levelOut N (Q.take (2 ^ kOf N))) :: O, []⟩
    have hL₄ : LevelRegs N (nextN N) (kOf N) (pieceOf N) σ₄ :=
      (hL₃.update tD _ (by decide)).update tOut _ (by decide)
    have ih := runs_upBatch hN0 hk g (Q.drop (2 ^ kOf N)) σ₄ ((rwds (nextN N) (Q.take (2 ^ kOf N))).reverse ++ Il)
      (rwd N (levelOut N (Q.take (2 ^ kOf N))) :: O) (by rw [List.length_drop, hl, Nat.add_mul, one_mul]; omega)
      (fun q hq => hv q (List.mem_of_mem_drop hq)) hL₄ (by tsimp [σ₄, σ₃, σ₂, σ₁, hK]) (by tsimp [σ₄])
      (by tsimp [σ₄, σ₃, σ₂, σ₁]) (by tsimp [σ₄])
    have hQ0 : Q ≠ [] := by
      intro h; rw [h] at hl; simp at hl
    have hne : (σ tIn).right ≠ [] := by
      rw [hIn]; simpa [rwds] using hQ0
    refine (Runs.loop_step hne (Runs.then s1 (Runs.then s2 (Runs.then s3
      (s4.mono (fun σ' h' => by rw [h']; exact ih) le_rfl))))).mono (fun σ' h' => ?_) ?_
    · rw [h']
      have eQ : (rwds (nextN N) (Q.drop (2 ^ kOf N))).reverse ++ ((rwds (nextN N) (Q.take (2 ^ kOf N))).reverse ++ Il)
          = (rwds (nextN N) Q).reverse ++ Il := by
        conv_rhs => rw [hq, rwds_append, List.reverse_append, List.append_assoc]
      have eO : (rwds N (upList N (2 ^ kOf N) g (Q.drop (2 ^ kOf N)))).reverse ++
          rwd N (levelOut N (Q.take (2 ^ kOf N))) :: O =
          (rwds N (upList N (2 ^ kOf N) (g + 1) Q)).reverse ++ O := by simp [rwds, upList]
      funext i; fin_cases i <;> tsimp [σ₄, σ₃, σ₂, σ₁, hK, hD0, eQ, eO]
    · have c1 : clen (σ₁ tK).left = 2 ^ kOf N := by tsimp [σ₁, clen]
      have c2 : clen (σ₂ tD).left = 2 ^ kOf N * (nextN N + 2) := by
        tsimp [σ₂, σ₁, clen_reverse]; rw [clen_rwds, hP]
      rw [c1, c2, List.length_replicate]
      have hX : 5000 * (2 ^ kOf N * (nextN N + 2)) ≤ 5000 * (2 ^ kOf N + 1) * (nextN N + 2) := by
        nlinarith
      have e : (kOf N + 4) * (5000 * (2 ^ kOf N + 1) * (nextN N + 2)) =
          (kOf N + 3) * (5000 * (2 ^ kOf N + 1) * (nextN N + 2)) + 5000 * (2 ^ kOf N + 1) * (nextN N + 2) := by
        ring
      rw [e]
      have := upb_arith (2 ^ kOf N) (nextN N) ((kOf N + 3) * (5000 * (2 ^ kOf N + 1) * (nextN N + 2)))
        (24 * pieceOf N * 2 ^ kOf N + 1000 * N) (5000 * (2 ^ kOf N + 1) * (nextN N + 2)) g hX
      linarith

end IntegerMultBounds.Schoenhage
