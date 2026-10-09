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

/-! ### Negation and the inverse butterfly -/

/-- `-v mod 2^N + 1` with `v` in `aY`: subtract from the zero word. -/
noncomputable def negMod : Cmd 0 𝕋 :=
  .seq (op0 (Rules.fill false) false cW aX (by decide)) <| .seq (rewind aX) <| .seq (rewind cW) subMod

theorem runs_negMod {N : ℕ} (hN : 0 < N) (σ : Fin 𝕋 → WTape) (hc : AluConst N σ) {v : List Bool}
    (hY : σ aY = reg v) (hlv : v.length = N + 1) (hv : bval v < 2 ^ N + 1)
    (hX : σ aX = emp) (hO : σ aO = emp) (h1 : σ aS1 = emp) (h2 : σ aS2 = emp) :
    Runs negMod σ (· = Function.update (Function.update σ aY emp) aO
      (reg (rwd N ((2 ^ N + 1 - bval v) % (2 ^ N + 1))))) (90 * N + 220) := by
  obtain ⟨hW, hF⟩ := hc
  have hz : (List.replicate (N + 1) false).length = N + 1 := by simp
  have hzv : bval (List.replicate (N + 1) false) = 0 := bval_replicate_false _
  unfold negMod
  have s1 : Runs (op0 (a := 0) (Rules.fill false) false cW aX (by decide)) σ
      (· = Function.update (Function.update σ cW ⟨[ones (N + 1)], []⟩) aX
        ⟨[List.replicate (N + 1) false], []⟩) (N + 7) := by
    apply Runs.of_wp
    simp only [wp_op0]
    tsimp [hW, hX, emp, reg, Rules.output_fill]
    have := time_le (Rules.fill false) (ones (N + 1)) (fun j => j.elim0) 0 (fun j => j.elim0)
    simp at this; omega
  refine (Runs.then s1 <| Runs.then (runs_rewind aX _) <| Runs.then (runs_rewind cW _) <|
    runs_subMod hN _ ⟨by tsimp [hW, reg], by tsimp [hF]⟩ (x := List.replicate (N + 1) false) (y := v)
      (by tsimp [reg]) (by tsimp [hY]) hz hlv (by rw [hzv]; omega) hv (by tsimp [hO])
      (by tsimp [h1]) (by tsimp [h2])).mono ?_ ?_
  · intro σ' h; rw [h]
    have : subRes N (List.replicate (N + 1) false) v = rwd N ((2 ^ N + 1 - bval v) % (2 ^ N + 1)) := by
      rw [subRes, hzv, rwd]; simp
    rw [this]
    funext i; fin_cases i <;> tsimp [hX, hW, emp, reg]
  · tsimp [clen]; omega

/-- The inverse butterfly: `p + q` and `-(2^s (p - q))`, with `s = N - t` in `cT`. -/
noncomputable def bflyI : Cmd 0 𝕋 :=
  .seq (regIn tU aX (by decide)) <| .seq (regIn tV aY (by decide)) <|
  .seq (regDup aX bX (by decide)) <| .seq (regDup aY bY (by decide)) <| .seq addMod <|
  .seq (regOut aO tO1 (by decide)) <| .seq (regMove bX aX (by decide)) <|
  .seq (regMove bY aY (by decide)) <| .seq subMod <| .seq (regMove aO aX (by decide)) <|
  .seq mulPow2 <| .seq (regMove aO aY (by decide)) <| .seq negMod (regOut aO tO2 (by decide))

theorem runs_bflyI {N s : ℕ} (hN : 0 < N) (hsN : s ≤ N) (σ : Fin 𝕋 → WTape) (hr : AluReady N σ)
    (hcT : σ cT = reg (ones s)) {p q : ℕ} (hp : p < 2 ^ N + 1) (hq : q < 2 ^ N + 1)
    {LU RU LV RV M1 M2 : List (List Bool)}
    (hU : σ tU = ⟨LU, rwd N p :: RU⟩) (hV : σ tV = ⟨LV, rwd N q :: RV⟩)
    (h1 : σ tO1 = ⟨M1, []⟩) (h2 : σ tO2 = ⟨M2, []⟩) :
    Runs bflyI σ (· = Function.update (Function.update (Function.update (Function.update σ
        tU ⟨rwd N p :: LU, RU⟩) tV ⟨rwd N q :: LV, RV⟩)
        tO1 ⟨rwd N ((p + q) % (2 ^ N + 1)) :: M1, []⟩)
        tO2 ⟨rwd N ((2 ^ N + 1 - 2 ^ s * ((p + (2 ^ N + 1) - q) % (2 ^ N + 1)) % (2 ^ N + 1)) %
          (2 ^ N + 1)) :: M2, []⟩)
      (2000 * N + 4000) := by
  obtain ⟨⟨hW, hF⟩, hcN, hc1, hX, hY, hO, hS1, hS2, hS3, hbX, hbY⟩ := hr
  set d := (p + (2 ^ N + 1) - q) % (2 ^ N + 1)
  have hd := mod_lt' N (p + (2 ^ N + 1) - q)
  have hz := mod_lt' N (2 ^ s * d)
  have lp := rwd_length N p
  have lq := rwd_length N q
  have ld := rwd_length N d
  have lz := rwd_length N (2 ^ s * d % (2 ^ N + 1))
  unfold bflyI
  refine (Runs.then (runs_regIn (s := tU) (r := aX) (by decide) σ hU hX) <|
    Runs.then (runs_regIn (s := tV) (r := aY) (by decide) _ (L := LV) (R := RV) (w := rwd N q)
      (by tsimp [hV]) (by tsimp [hY])) <|
    Runs.then (runs_regDup (r := aX) (r' := bX) (by decide) _ (w := rwd N p) (by tsimp) (by tsimp [hbX])) <|
    Runs.then (runs_regDup (r := aY) (r' := bY) (by decide) _ (w := rwd N q) (by tsimp) (by tsimp [hbY])) <|
    Runs.then (runs_addMod hN _ ⟨by tsimp [hW], by tsimp [hF]⟩ (x := rwd N p) (y := rwd N q)
      (by tsimp) (by tsimp) lp lq (by rw [bval_rwd hp]; exact hp) (by rw [bval_rwd hq]; exact hq)
      (by tsimp [hO]) (by tsimp [hS1]) (by tsimp [hS2])) <|
    Runs.then (runs_regOut (r := aO) (d := tO1) (by decide) _ (M := M1) (w := addRes N (rwd N p) (rwd N q))
      (by tsimp) (by tsimp [h1])) <|
    Runs.then (runs_regMove (r := bX) (r' := aX) (by decide) _ (w := rwd N p) (by tsimp) (by tsimp)) <|
    Runs.then (runs_regMove (r := bY) (r' := aY) (by decide) _ (w := rwd N q) (by tsimp) (by tsimp)) <|
    Runs.then (runs_subMod hN _ ⟨by tsimp [hW], by tsimp [hF]⟩ (x := rwd N p) (y := rwd N q)
      (by tsimp) (by tsimp) lp lq (by rw [bval_rwd hp]; exact hp) (by rw [bval_rwd hq]; exact hq)
      (by tsimp) (by tsimp [hS1]) (by tsimp [hS2])) <|
    Runs.then (runs_regMove (r := aO) (r' := aX) (by decide) _ (w := subRes N (rwd N p) (rwd N q))
      (by tsimp) (by tsimp)) <|
    Runs.then (runs_mulPow2 hN hsN _ ⟨by tsimp [hW], by tsimp [hF]⟩ (by tsimp [hcN]) (by tsimp [hc1])
      (by tsimp [hcT]) (v := rwd N d) (by tsimp [subRes_rwd _ _ _ hp hq]; rfl) ld
      (by rw [bval_rwd hd]; exact hd) (by tsimp) (by tsimp) (by tsimp [hS1]) (by tsimp [hS2])
      (by tsimp [hS3])) <|
    Runs.then (runs_regMove (r := aO) (r' := aY) (by decide) _ (w := mulRes N s (rwd N d))
      (by tsimp) (by tsimp)) <|
    Runs.then (runs_negMod hN _ ⟨by tsimp [hW], by tsimp [hF]⟩ (v := mulRes N s (rwd N d))
      (by tsimp) (by rw [mulRes_rwd _ _ _ hd]; exact lz) (by rw [mulRes_rwd _ _ _ hd, bval_rwd hz]; exact hz)
      (by tsimp) (by tsimp) (by tsimp [hS1]) (by tsimp [hS2])) <|
    runs_regOut (r := aO) (d := tO2) (by decide) _ (M := M2)
      (w := rwd N ((2 ^ N + 1 - bval (mulRes N s (rwd N d))) % (2 ^ N + 1))) (by tsimp)
      (by tsimp [h2])).mono ?_ ?_
  · intro σ' h
    rw [h, mulRes_rwd _ _ _ hd, bval_rwd hz, addRes_rwd _ _ _ hp hq]
    funext i; fin_cases i <;> tsimp [hX, hY, hO, hbX, hbY]
  · simp only [lp, lq, rwd_length, mulRes_length, addRes_length, subRes_length]
    omega

end IntegerMultBounds.Schoenhage
