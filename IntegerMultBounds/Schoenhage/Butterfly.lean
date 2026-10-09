import IntegerMultBounds.Schoenhage.Alu
import IntegerMultBounds.Schoenhage.Lists

/-! Butterflies of the twisted transform on word tapes. The forward butterfly
reads `u` and `v` from the half-block tapes and appends `u + 2^t v` and
`u - 2^t v` modulo `2^N + 1` to the two output tapes; the shift `t` is a unary
register. Modular negation is subtraction from zero. -/

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp

namespace Tp
abbrev tU : Fin 𝕋 := 12
abbrev tV : Fin 𝕋 := 13
abbrev tO1 : Fin 𝕋 := 14
abbrev tO2 : Fin 𝕋 := 15
abbrev bX : Fin 𝕋 := 16
abbrev bY : Fin 𝕋 := 17
end Tp

/-- The arithmetic unit is idle: constants in place and every work tape empty. -/
def AluReady (N : ℕ) (σ : Fin 𝕋 → WTape) : Prop :=
  AluConst N σ ∧ σ cN = reg (ones N) ∧ σ c1 = reg [true] ∧ σ aX = emp ∧ σ aY = emp ∧ σ aO = emp ∧
    σ aS1 = emp ∧ σ aS2 = emp ∧ σ aS3 = emp ∧ σ bX = emp ∧ σ bY = emp

/-- The canonical word of a residue. -/
def rwd (N r : ℕ) : List Bool := bits (N + 1) r

theorem rwd_length (N r : ℕ) : (rwd N r).length = N + 1 := by simp [rwd]

theorem bval_rwd {N r : ℕ} (h : r < 2 ^ N + 1) : bval (rwd N r) = r := by
  rw [rwd, bval_bits, Nat.mod_eq_of_lt]
  rw [pow_succ]; have := Nat.one_le_two_pow (n := N); omega

theorem subRes_rwd (N r s : ℕ) (hr : r < 2 ^ N + 1) (hs : s < 2 ^ N + 1) :
    subRes N (rwd N r) (rwd N s) = rwd N ((r + (2 ^ N + 1) - s) % (2 ^ N + 1)) := by
  rw [subRes, bval_rwd hr, bval_rwd hs]; rfl

theorem addRes_rwd (N r s : ℕ) (hr : r < 2 ^ N + 1) (hs : s < 2 ^ N + 1) :
    addRes N (rwd N r) (rwd N s) = rwd N ((r + s) % (2 ^ N + 1)) := by
  rw [addRes, bval_rwd hr, bval_rwd hs]; rfl

theorem mulRes_rwd (N t r : ℕ) (hr : r < 2 ^ N + 1) :
    mulRes N t (rwd N r) = rwd N (2 ^ t * r % (2 ^ N + 1)) := by
  rw [mulRes, bval_rwd hr]; rfl

theorem mod_lt' (N v : ℕ) : v % (2 ^ N + 1) < 2 ^ N + 1 := Nat.mod_lt _ (by positivity)

/-! ### Forward butterfly -/

/-- The forward butterfly: load `v`, shift it, keep `2^t v` and `u` in work and
backup registers, add, restore, subtract. -/
noncomputable def bflyF : Cmd 0 𝕋 :=
  .seq (regIn tV aX (by decide)) <| .seq mulPow2 <|
  .seq (regMove aO aY (by decide)) <| .seq (regIn tU aX (by decide)) <|
  .seq (regDup aX bX (by decide)) <| .seq (regDup aY bY (by decide)) <| .seq addMod <|
  .seq (regOut aO tO1 (by decide)) <| .seq (regMove bX aX (by decide)) <|
  .seq (regMove bY aY (by decide)) <| .seq subMod (regOut aO tO2 (by decide))

theorem runs_bflyF {N t : ℕ} (hN : 0 < N) (htN : t ≤ N) (σ : Fin 𝕋 → WTape) (hr : AluReady N σ)
    (hcT : σ cT = reg (ones t)) {u v : ℕ} (hu : u < 2 ^ N + 1) (hv : v < 2 ^ N + 1)
    {LU RU LV RV M1 M2 : List (List Bool)}
    (hU : σ tU = ⟨LU, rwd N u :: RU⟩) (hV : σ tV = ⟨LV, rwd N v :: RV⟩)
    (h1 : σ tO1 = ⟨M1, []⟩) (h2 : σ tO2 = ⟨M2, []⟩) :
    Runs bflyF σ (· = Function.update (Function.update (Function.update (Function.update σ
        tU ⟨rwd N u :: LU, RU⟩) tV ⟨rwd N v :: LV, RV⟩)
        tO1 ⟨rwd N ((u + 2 ^ t * v % (2 ^ N + 1)) % (2 ^ N + 1)) :: M1, []⟩)
        tO2 ⟨rwd N ((u + (2 ^ N + 1) - 2 ^ t * v % (2 ^ N + 1)) % (2 ^ N + 1)) :: M2, []⟩)
      (1000 * N + 2000) := by
  obtain ⟨⟨hW, hF⟩, hcN, hc1, hX, hY, hO, hS1, hS2, hS3, hbX, hbY⟩ := hr
  have hz := mod_lt' N (2 ^ t * v)
  have lu := rwd_length N u
  have lv := rwd_length N v
  have lz := rwd_length N (2 ^ t * v % (2 ^ N + 1))
  unfold bflyF
  refine (Runs.then (runs_regIn (s := tV) (r := aX) (by decide) σ hV hX) <|
    Runs.then (runs_mulPow2 hN htN _ ⟨by tsimp [hW], by tsimp [hF]⟩ (by tsimp [hcN]) (by tsimp [hc1])
      (by tsimp [hcT]) (v := rwd N v) (by tsimp) lv (by rw [bval_rwd hv]; exact hv) (by tsimp [hY])
      (by tsimp [hO]) (by tsimp [hS1]) (by tsimp [hS2]) (by tsimp [hS3])) <|
    Runs.then (runs_regMove (r := aO) (r' := aY) (by decide) _ (w := mulRes N t (rwd N v)) (by tsimp) (by tsimp [hY])) <|
    Runs.then (runs_regIn (s := tU) (r := aX) (by decide) _ (L := LU) (R := RU) (w := rwd N u) (by tsimp [hU]) (by tsimp)) <|
    Runs.then (runs_regDup (r := aX) (r' := bX) (by decide) _ (w := rwd N u) (by tsimp) (by tsimp [hbX])) <|
    Runs.then (runs_regDup (r := aY) (r' := bY) (by decide) _ (w := mulRes N t (rwd N v)) (by tsimp) (by tsimp [hbY])) <|
    Runs.then (runs_addMod hN _ ⟨by tsimp [hW], by tsimp [hF]⟩ (x := rwd N u)
      (y := mulRes N t (rwd N v)) (by tsimp) (by tsimp) lu (by rw [mulRes_rwd _ _ _ hv]; exact lz)
      (by rw [bval_rwd hu]; exact hu) (by rw [mulRes_rwd _ _ _ hv, bval_rwd hz]; exact hz)
      (by tsimp) (by tsimp [hS1]) (by tsimp [hS2])) <|
    Runs.then (runs_regOut (r := aO) (d := tO1) (by decide) _ (M := M1) (w := addRes N (rwd N u) (mulRes N t (rwd N v))) (by tsimp)
      (by tsimp [h1])) <|
    Runs.then (runs_regMove (r := bX) (r' := aX) (by decide) _ (w := rwd N u) (by tsimp) (by tsimp)) <|
    Runs.then (runs_regMove (r := bY) (r' := aY) (by decide) _ (w := mulRes N t (rwd N v)) (by tsimp) (by tsimp)) <|
    Runs.then (runs_subMod hN _ ⟨by tsimp [hW], by tsimp [hF]⟩ (x := rwd N u)
      (y := mulRes N t (rwd N v)) (by tsimp) (by tsimp) lu (by rw [mulRes_rwd _ _ _ hv]; exact lz)
      (by rw [bval_rwd hu]; exact hu) (by rw [mulRes_rwd _ _ _ hv, bval_rwd hz]; exact hz)
      (by tsimp) (by tsimp [hS1]) (by tsimp [hS2])) <|
    runs_regOut (r := aO) (d := tO2) (by decide) _ (M := M2) (w := subRes N (rwd N u) (mulRes N t (rwd N v))) (by tsimp)
      (by tsimp [h2])).mono ?_ ?_
  · intro σ' h
    rw [h, mulRes_rwd _ _ _ hv, addRes_rwd _ _ _ hu hz, subRes_rwd _ _ _ hu hz]
    funext i; fin_cases i <;> tsimp [hX, hY, hO, hbX, hbY]
  · simp only [lu, lz, mulRes_rwd _ _ _ hv, addRes_length, subRes_length]
    omega

end IntegerMultBounds.Schoenhage
