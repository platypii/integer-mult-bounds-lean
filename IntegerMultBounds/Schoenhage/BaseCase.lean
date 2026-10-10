import IntegerMultBounds.Schoenhage.Batch

/-! The base case on word tapes: schoolbook multiplication modulo `2^N + 1`.
For every bit `yᵢ` of the second operand the residue `2^i x` is added to the
accumulator when `yᵢ = 1`; the products of all pairs of `tIn` go to `tOut`. -/

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule

/-! ### The arithmetic -/

/-- The accumulator after the bits `w`, the first with weight `2^t`. -/
def accF (N x : ℕ) : ℕ → ℕ → List Bool → ℕ
  | a, _, [] => a
  | a, t, b :: w => accF N x (if b then (a + 2 ^ t * x % (2 ^ N + 1)) % (2 ^ N + 1) else a) (t + 1) w

theorem accF_eq (N x : ℕ) : ∀ (a t : ℕ) (w : List Bool), a < 2 ^ N + 1 →
    accF N x a t w = (a + 2 ^ t * x * bval w) % (2 ^ N + 1)
  | a, t, [], ha => by simp [accF, Nat.mod_eq_of_lt ha]
  | a, t, b :: w, ha => by
    rw [accF, accF_eq N x _ (t + 1) w (by split_ifs <;> [exact Nat.mod_lt _ (by positivity); exact ha])]
    simp only [bval_cons]
    split_ifs with hb
    · have e : a + 2 ^ t * x * (1 + 2 * bval w) = a + 2 ^ t * x + 2 ^ (t + 1) * x * bval w := by ring
      rw [e]
      exact ((Nat.mod_modEq _ _).add_right _).trans (((Nat.mod_modEq _ _).add_left a).add_right _)
    · simp only [Nat.zero_add]; congr 1; ring

/-! ### One bit -/

/-- Take the next bit of `tY` into `sT1`. -/
noncomputable def bitOut : Cmd 0 𝕋 :=
  .seq (op1 Rules.take false c1 tY sT1 (by decide) (by decide) (by decide)) <| .seq (rewind c1) <|
  .seq (rewind tY) <| .seq (op1 Rules.drop false tY c1 sT2 (by decide) (by decide) (by decide)) <|
  .seq (rewind c1) <| .seq (clear tY) <| .seq (rewind sT2) <| .seq (regMove sT2 tY (by decide)) (rewind sT1)

theorem runs_bitOut (σ : Fin 𝕋 → WTape) (h1 : σ c1 = reg [true]) {b : Bool} {w : List Bool}
    (hY : σ tY = reg (b :: w)) (hT1 : σ sT1 = emp) (hT2 : σ sT2 = emp) :
    Runs bitOut σ (· = Function.update (Function.update σ tY (reg w)) sT1 (reg [b])) (10 * w.length + 80) := by
  apply Runs.of_wp
  simp only [bitOut, regMove, regIn, cpy, WP, wp_op0, wp_op1, wp_rewind, wp_clear]
  tsimp [h1, hY, hT1, hT2, emp, reg, Rules.output_take, Rules.output_drop, Rules.output_copy, Rules.fit]
  have t1 := time_le Rules.take [true] (fun _ => b :: w) (w.length + 1) (fun _ => by simp)
  have t2 := time_le Rules.drop (b :: w) (fun _ => [true]) 1 (fun _ => by simp)
  have t3 := time_le Rules.copy w (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [h1, hY, hT1, hT2, emp, reg]
  · simp [clen, WTape.words] at t1 t2 t3 ⊢; omega

/-- Copy the operand `sX` into the unit. -/
noncomputable def loadX : Cmd 0 𝕋 := .seq (op0 Rules.copy false sX aX (by decide)) <| .seq (rewind sX) (rewind aX)

/-- Add `2^t x` (shift `cT`) to the accumulator `sRA`. -/
noncomputable def addTerm : Cmd 0 𝕋 :=
  .seq loadX <| .seq mulPow2 <|
  .seq (regMove aO aY (by decide)) <| .seq (regMove sRA aX (by decide)) <| .seq addMod (regMove aO sRA (by decide))

theorem runs_addTerm {N x a t : ℕ} (hN : 0 < N) (htN : t ≤ N) (hx : x < 2 ^ N + 1) (ha : a < 2 ^ N + 1)
    (σ : Fin 𝕋 → WTape) (hr : AluReady N σ) (hX : σ sX = reg (rwd N x)) (hA : σ sRA = reg (rwd N a))
    (hT : σ cT = reg (ones t)) :
    Runs addTerm σ (· = Function.update σ sRA (reg (rwd N ((a + 2 ^ t * x % (2 ^ N + 1)) % (2 ^ N + 1)))))
      (400 * N + 1000) := by
  obtain ⟨⟨hW, hF⟩, hcN, hc1, haX, haY, haO, hS1, hS2, hS3, hbX, hbY⟩ := hr
  unfold addTerm
  have s1 : Runs loadX σ
      (· = Function.update σ aX (reg (rwd N x))) (3 * N + 20) := by
    apply Runs.of_wp
    simp only [loadX, WP, wp_op0, wp_rewind]
    tsimp [hX, haX, emp, reg, Rules.output_copy]
    have t1 := time_le Rules.copy (rwd N x) (fun j => j.elim0) 0 (fun j => j.elim0)
    refine ⟨?_, ?_⟩
    · funext i; fin_cases i <;> tsimp [hX, haX, emp, reg]
    · simp [rwd_length] at t1 ⊢; omega
  set σ₁ := Function.update σ aX (reg (rwd N x))
  have s2 := runs_mulPow2 (N := N) (t := t) hN htN σ₁ ⟨by tsimp [σ₁, hW], by tsimp [σ₁, hF]⟩
    (by tsimp [σ₁, hcN]) (by tsimp [σ₁, hc1]) (by tsimp [σ₁, hT]) (v := rwd N x) (by tsimp [σ₁])
    (rwd_length N x) (by rw [bval_rwd hx]; exact hx) (by tsimp [σ₁, haY]) (by tsimp [σ₁, haO])
    (by tsimp [σ₁, hS1]) (by tsimp [σ₁, hS2]) (by tsimp [σ₁, hS3])
  rw [mulRes_rwd _ _ _ hx] at s2
  set m := 2 ^ t * x % (2 ^ N + 1)
  have hm : m < 2 ^ N + 1 := mod_lt' _ _
  set σ₂ := Function.update (Function.update σ₁ aX emp) aO (reg (rwd N m))
  have s3 := runs_regMove (a := 0) (r := aO) (r' := aY) (by decide) σ₂ (w := rwd N m) (by tsimp [σ₂])
    (by tsimp [σ₂, σ₁, haY])
  set σ₃ := Function.update (Function.update σ₂ aO emp) aY (reg (rwd N m))
  have s4 := runs_regMove (a := 0) (r := sRA) (r' := aX) (by decide) σ₃ (w := rwd N a)
    (by tsimp [σ₃, σ₂, σ₁, hA]) (by tsimp [σ₃, σ₂])
  set σ₄ := Function.update (Function.update σ₃ sRA emp) aX (reg (rwd N a))
  have s5 := runs_addMod hN σ₄ ⟨by tsimp [σ₄, σ₃, σ₂, σ₁, hW], by tsimp [σ₄, σ₃, σ₂, σ₁, hF]⟩
    (x := rwd N a) (y := rwd N m) (by tsimp [σ₄]) (by tsimp [σ₄, σ₃]) (rwd_length _ _) (rwd_length _ _)
    (by rw [bval_rwd ha]; exact ha) (by rw [bval_rwd hm]; exact hm) (by tsimp [σ₄, σ₃])
    (by tsimp [σ₄, σ₃, σ₂, σ₁, hS1]) (by tsimp [σ₄, σ₃, σ₂, σ₁, hS2])
  rw [addRes_rwd _ _ _ ha hm] at s5
  set σ₅ := Function.update (Function.update (Function.update σ₄ aX emp) aY emp) aO
    (reg (rwd N ((a + m) % (2 ^ N + 1))))
  have s6 := runs_regMove (a := 0) (r := aO) (r' := sRA) (by decide) σ₅ (w := rwd N ((a + m) % (2 ^ N + 1)))
    (by tsimp [σ₅]) (by tsimp [σ₅, σ₄])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 s6))))).mono
    (fun σ' h => ?_) ?_
  · rw [h]; funext i; fin_cases i <;> tsimp [σ₅, σ₄, σ₃, σ₂, σ₁, haX, haY, haO, emp]
  · simp only [rwd_length]; omega

/-- Lengthen the shift register `cT` by one. -/
noncomputable def incT : Cmd 0 𝕋 :=
  .seq (skp cT tJ (by decide)) <| .seq (op0 Rules.copy true c1 cT (by decide)) <| .seq (rewind c1) (rewind cT)

theorem runs_incT {t : ℕ} (σ : Fin 𝕋 → WTape) (hT : σ cT = reg (ones t)) (h1 : σ c1 = reg [true])
    (hJ : σ tJ = emp) :
    Runs incT σ (· = Function.update σ cT (reg (ones (t + 1)))) (3 * t + 30) := by
  apply Runs.of_wp
  simp only [incT, skp, WP, wp_op0, wp_rewind]
  tsimp [hT, h1, hJ, emp, reg, Rules.output_skip, Rules.output_copy]
  have t1 := time_le Rules.skip (ones t) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t2 := time_le Rules.copy [true] (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hT, h1, hJ, emp, reg, ones, List.replicate_succ']
  · simp at t1 t2 ⊢; omega

/-- One bit of the second operand. -/
noncomputable def baseStep : Cmd 0 𝕋 :=
  .seq bitOut <| .seq (.cond sT1 addTerm (rewind sT1)) <| .seq (clear sT1) <| .seq incT (skp tS tJ (by decide))

theorem runs_baseStep {N x a t : ℕ} (hN : 0 < N) (htN : t ≤ N) (hx : x < 2 ^ N + 1) (ha : a < 2 ^ N + 1)
    (σ : Fin 𝕋 → WTape) (hr : AluReady N σ) (hX : σ sX = reg (rwd N x)) (hA : σ sRA = reg (rwd N a))
    (hT : σ cT = reg (ones t)) {b : Bool} {w : List Bool} (hY : σ tY = reg (b :: w))
    (hT1 : σ sT1 = emp) (hT2 : σ sT2 = emp) (hJ : σ tJ = emp) {Sl Sr : List (List Bool)}
    (hS : σ tS = ⟨Sl, [] :: Sr⟩) :
    Runs baseStep σ (· = Function.update (Function.update (Function.update (Function.update σ
        sRA (reg (rwd N (if b then (a + 2 ^ t * x % (2 ^ N + 1)) % (2 ^ N + 1) else a))))
        cT (reg (ones (t + 1)))) tY (reg w)) tS ⟨[] :: Sl, Sr⟩)
      (10 * w.length + 3 * t + 400 * N + 1200) := by
  unfold baseStep
  have s1 := runs_bitOut σ hr.2.2.1 hY hT1 hT2
  set σ₁ := Function.update (Function.update σ tY (reg w)) sT1 (reg [b])
  have hr₁ : AluReady N σ₁ := (hr.update tY _ (by decide)).update sT1 _ (by decide)
  have s2 : Runs (a := 0) (.cond sT1 addTerm (rewind sT1)) σ₁ (· = Function.update σ₁ sRA
      (reg (rwd N (if b then (a + 2 ^ t * x % (2 ^ N + 1)) % (2 ^ N + 1) else a)))) (400 * N + 1003) := by
    cases b
    · refine Runs.cond_false (by tsimp [σ₁, reg, startsOne_mk]) ?_
      refine (runs_rewind sT1 σ₁).mono (fun σ' h => ?_) (by tsimp [σ₁, reg])
      rw [h]; funext i; fin_cases i <;> tsimp [σ₁, hA, reg]
    · refine Runs.cond_true (by tsimp [σ₁, reg, startsOne_mk]) ?_
      refine (runs_addTerm hN htN hx ha σ₁ hr₁ (by tsimp [σ₁, hX]) (by tsimp [σ₁, hA])
        (by tsimp [σ₁, hT])).mono (fun σ' h => ?_) (by omega)
      rw [h]; simp
  set σ₂ := Function.update σ₁ sRA (reg (rwd N (if b then (a + 2 ^ t * x % (2 ^ N + 1)) % (2 ^ N + 1) else a)))
  have s3 := runs_clear (a := 0) sT1 σ₂
  set σ₃ := Function.update σ₂ sT1 ⟨[], []⟩
  have s4 := runs_incT (t := t) σ₃ (by tsimp [σ₃, σ₂, σ₁, hT]) (by tsimp [σ₃, σ₂, σ₁, hr.2.2.1])
    (by tsimp [σ₃, σ₂, σ₁, hJ])
  set σ₄ := Function.update σ₃ cT (reg (ones (t + 1)))
  have s5 := runs_skp (a := 0) (s := tS) (j := tJ) (by decide) σ₄ (by tsimp [σ₄, σ₃, σ₂, σ₁, hS])
    (by tsimp [σ₄, σ₃, σ₂, σ₁, hJ, emp])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 s5)))).mono (fun σ' h => ?_) ?_
  · rw [h]; funext i; fin_cases i <;> tsimp [σ₄, σ₃, σ₂, σ₁, hS, hT1, emp]
  · tsimp [σ₂, σ₁, reg, WTape.words, clen, σ₄, σ₃, hS]
    omega

/-- Every bit of the second operand. -/
noncomputable def baseLoop : Cmd 0 𝕋 := .loop tS baseStep

theorem runs_baseLoop {N x : ℕ} (hN : 0 < N) (hx : x < 2 ^ N + 1) :
    ∀ (w : List Bool) (a t : ℕ) (σ : Fin 𝕋 → WTape) (Sl : List (List Bool)),
      a < 2 ^ N + 1 → t + w.length ≤ N + 1 → AluReady N σ → σ sX = reg (rwd N x) →
      σ sRA = reg (rwd N a) → σ cT = reg (ones t) → σ tY = reg w → σ sT1 = emp → σ sT2 = emp →
      σ tJ = emp → σ tS = ⟨Sl, List.replicate w.length []⟩ →
      Runs baseLoop σ (· = Function.update (Function.update (Function.update (Function.update σ
          sRA (reg (rwd N (accF N x a t w)))) cT (reg (ones (t + w.length)))) tY (reg []))
          tS ⟨List.replicate w.length [] ++ Sl, []⟩)
        (w.length * (420 * N + 1300))
  | [], a, t, σ, Sl, _, _, _, _, hA, hT, hY, _, _, _, hS => by
    refine (Runs.loop_done (by simp [hS]) rfl).mono (fun σ' h' => ?_) (by simp)
    subst h'
    funext i; fin_cases i <;> tsimp [hA, hT, hY, hS, accF]
  | b :: w, a, t, σ, Sl, ha, htw, hr, hX, hA, hT, hY, hT1, hT2, hJ, hS => by
    have s1 := runs_baseStep hN (by simp at htw; omega) hx ha σ hr hX hA hT hY hT1 hT2 hJ
      (Sl := Sl) (Sr := List.replicate w.length []) (by simpa [List.replicate_succ] using hS)
    set a' := if b then (a + 2 ^ t * x % (2 ^ N + 1)) % (2 ^ N + 1) else a
    have ha' : a' < 2 ^ N + 1 := by
      simp only [a']; split_ifs
      · exact mod_lt' _ _
      · exact ha
    set σ₁ := Function.update (Function.update (Function.update (Function.update σ
        sRA (reg (rwd N a'))) cT (reg (ones (t + 1)))) tY (reg w)) tS ⟨[] :: Sl, List.replicate w.length []⟩
    have hr₁ : AluReady N σ₁ :=
      (((hr.update sRA _ (by decide)).update cT _ (by decide)).update tY _ (by decide)).update tS _ (by decide)
    have ih := runs_baseLoop hN hx w a' (t + 1) σ₁ ([] :: Sl) ha' (by simp at htw; omega) hr₁
      (by tsimp [σ₁, hX]) (by tsimp [σ₁]) (by tsimp [σ₁]) (by tsimp [σ₁]) (by tsimp [σ₁, hT1])
      (by tsimp [σ₁, hT2]) (by tsimp [σ₁, hJ]) (by tsimp [σ₁])
    refine (Runs.loop_step (by simp [hS]) (s1.mono (fun σ' h' => by rw [h']; exact ih) le_rfl)).mono
      (fun σ' h' => ?_) ?_
    · rw [h']
      have e1 : t + 1 + w.length = t + (b :: w).length := by simp; omega
      funext i; fin_cases i <;> tsimp [σ₁, accF, a', e1, List.replicate_succ, replicate_append_cons]
    · simp only [List.length_cons] at htw ⊢; nlinarith

/-- A zero accumulator, an empty shift and `N + 1` bit ticks. -/
noncomputable def baseInit : Cmd 0 𝕋 :=
  .seq (op0 (Rules.fill false) false cW sRA (by decide)) <| .seq (rewind cW) <| .seq (rewind sRA) <|
  .seq (emit [[]] cT) <| .seq (rewind cT) <|
  .seq (op0 Rules.ticks false cW tS (by decide)) <| .seq (rewind cW) (rewind tS)

/-- Drop the operands and the loop registers. -/
noncomputable def baseClean : Cmd 0 𝕋 := .seq (clear sX) <| .seq (clear tY) <| .seq (clear cT) (clear tS)

/-- The product of the next pair of `tIn` modulo `2^N + 1`, onto `tOut`. -/
noncomputable def basePair : Cmd 0 𝕋 :=
  .seq (regIn tIn sX (by decide)) <| .seq (regIn tIn tY (by decide)) <| .seq baseInit <| .seq baseLoop <|
  .seq (regOut sRA tOut (by decide)) baseClean

theorem runs_basePair {N x y : ℕ} (hN : 0 < N) (hx : x < 2 ^ N + 1) (hy : y < 2 ^ N + 1)
    (σ : Fin 𝕋 → WTape) (hr : AluReady N σ) (hX : σ sX = emp) (hY : σ tY = emp) (hA : σ sRA = emp)
    (hT : σ cT = emp) (hS : σ tS = emp) (hT1 : σ sT1 = emp) (hT2 : σ sT2 = emp) (hJ : σ tJ = emp)
    {Il Ir O : List (List Bool)} (hIn : σ tIn = ⟨Il, rwd N x :: rwd N y :: Ir⟩) (hO : σ tOut = ⟨O, []⟩) :
    Runs basePair σ (· = Function.update (Function.update σ tIn ⟨rwd N y :: rwd N x :: Il, Ir⟩)
        tOut ⟨rwd N (x * y % (2 ^ N + 1)) :: O, []⟩) ((N + 2) * (420 * N + 1400)) := by
  have hW := hr.1.1
  unfold basePair
  have s1 := runs_regIn (a := 0) (s := tIn) (r := sX) (by decide) σ hIn hX
  set σ₁ := Function.update (Function.update σ tIn ⟨rwd N x :: Il, rwd N y :: Ir⟩) sX (reg (rwd N x))
  have s2 := runs_regIn (a := 0) (s := tIn) (r := tY) (by decide) σ₁ (L := rwd N x :: Il) (R := Ir)
    (w := rwd N y) (by tsimp [σ₁]) (by tsimp [σ₁, hY])
  set σ₂ := Function.update (Function.update σ₁ tIn ⟨rwd N y :: rwd N x :: Il, Ir⟩) tY (reg (rwd N y))
  have s3 : Runs baseInit σ₂ (· = Function.update (Function.update (Function.update σ₂
      sRA (reg (rwd N 0))) cT (reg (ones 0))) tS ⟨[], List.replicate (N + 1) []⟩) (8 * N + 50) := by
    apply Runs.of_wp
    simp only [baseInit, WP, wp_op0, wp_rewind, wp_emit]
    tsimp [σ₂, σ₁, hW, hA, hT, hS, emp, reg, Rules.output_fill, Rules.output_ticks]
    have t1 := time_le (Rules.fill false) (ones (N + 1)) (fun j => j.elim0) 0 (fun j => j.elim0)
    have t2 := time_le Rules.ticks (ones (N + 1)) (fun j => j.elim0) 0 (fun j => j.elim0)
    refine ⟨?_, ?_⟩
    · funext i; fin_cases i <;> tsimp [σ₂, σ₁, hW, hA, hT, hS, emp, reg, rwd_zero, ones]
    · simp [clen] at t1 t2 ⊢; omega
  set σ₃ := Function.update (Function.update (Function.update σ₂
      sRA (reg (rwd N 0))) cT (reg (ones 0))) tS ⟨[], List.replicate (N + 1) []⟩
  have hr₃ : AluReady N σ₃ := by
    refine ((((((hr.update tIn _ (by decide)).update sX _ (by decide)).update tIn _ (by decide)).update tY _
      (by decide)).update sRA _ (by decide)).update cT _ (by decide)).update tS _ (by decide)
  have s4 := runs_baseLoop hN hx (rwd N y) 0 0 σ₃ [] (by positivity) (by simp [rwd_length]) hr₃
    (by tsimp [σ₃, σ₂, σ₁]) (by tsimp [σ₃]) (by tsimp [σ₃]) (by tsimp [σ₃, σ₂]) (by tsimp [σ₃, σ₂, σ₁, hT1])
    (by tsimp [σ₃, σ₂, σ₁, hT2]) (by tsimp [σ₃, σ₂, σ₁, hJ]) (by tsimp [σ₃, rwd_length])
  have hv : accF N x 0 0 (rwd N y) = x * y % (2 ^ N + 1) := by
    rw [accF_eq N x 0 0 _ (by positivity), bval_rwd hy]; ring_nf
  rw [hv] at s4
  set σ₄ := Function.update (Function.update (Function.update (Function.update σ₃
      sRA (reg (rwd N (x * y % (2 ^ N + 1))))) cT (reg (ones (0 + (rwd N y).length)))) tY (reg []))
      tS ⟨List.replicate (rwd N y).length [] ++ [], []⟩
  have s5 := runs_regOut (a := 0) (r := sRA) (d := tOut) (by decide) σ₄ (M := O)
    (w := rwd N (x * y % (2 ^ N + 1))) (by tsimp [σ₄]) (by tsimp [σ₄, σ₃, σ₂, σ₁, hO])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5
    (runs_clear sX _ |>.then (runs_clear tY _ |>.then (runs_clear cT _ |>.then (runs_clear tS _))))))))).mono
    (fun σ' h => ?_) ?_
  · rw [h]; funext i; fin_cases i <;> tsimp [σ₄, σ₃, σ₂, σ₁, hX, hY, hA, hT, hS, emp]
  · tsimp [σ₄, σ₃, σ₂, σ₁, rwd_length, reg, WTape.words, clen]
    nlinarith

/-- Products of every pair of `tIn`. -/
noncomputable def baseBatch : Cmd 0 𝕋 := .loop tIn basePair

theorem runs_baseBatch {N : ℕ} (hN : 0 < N) :
    ∀ (L : List ℕ) (σ : Fin 𝕋 → WTape) (Il O : List (List Bool)), Even L.length →
      (∀ x ∈ L, x < 2 ^ N + 1) → AluReady N σ → σ sX = emp → σ tY = emp → σ sRA = emp → σ cT = emp →
      σ tS = emp → σ sT1 = emp → σ sT2 = emp → σ tJ = emp → σ tIn = ⟨Il, rwds N L⟩ → σ tOut = ⟨O, []⟩ →
      Runs baseBatch σ (· = Function.update (Function.update σ tIn ⟨(rwds N L).reverse ++ Il, []⟩)
          tOut ⟨(rwds N ((pairsOf L).map fun p => p.1 * p.2 % (2 ^ N + 1))).reverse ++ O, []⟩)
        (L.length * ((N + 2) * (420 * N + 1400)))
  | [], σ, Il, O, _, _, _, _, _, _, _, _, _, _, _, hIn, hO => by
    refine (Runs.loop_done (by simp [hIn, rwds]) rfl).mono (fun σ' h' => ?_) (by simp)
    subst h'
    funext i; fin_cases i <;> tsimp [hIn, hO, rwds, pairsOf]
  | [_], _, _, _, he, _, _, _, _, _, _, _, _, _, _, _, _ => by simp at he
  | x :: y :: L, σ, Il, O, he, hv, hr, hX, hY, hA, hT, hS, hT1, hT2, hJ, hIn, hO => by
    have s1 := runs_basePair hN (hv x (by simp)) (hv y (by simp)) σ hr hX hY hA hT hS hT1 hT2 hJ
      (Il := Il) (Ir := rwds N L) (O := O) (by simpa [rwds] using hIn) hO
    set σ₁ := Function.update (Function.update σ tIn ⟨rwd N y :: rwd N x :: Il, rwds N L⟩)
        tOut ⟨rwd N (x * y % (2 ^ N + 1)) :: O, []⟩
    have ih := runs_baseBatch hN L σ₁ (rwd N y :: rwd N x :: Il) (rwd N (x * y % (2 ^ N + 1)) :: O)
      (by simpa [Nat.even_add_one, parity_simps] using he) (fun z hz => hv z (by simp [hz]))
      ((hr.update tIn _ (by decide)).update tOut _ (by decide)) (by tsimp [σ₁, hX]) (by tsimp [σ₁, hY])
      (by tsimp [σ₁, hA]) (by tsimp [σ₁, hT]) (by tsimp [σ₁, hS]) (by tsimp [σ₁, hT1]) (by tsimp [σ₁, hT2])
      (by tsimp [σ₁, hJ]) (by tsimp [σ₁]) (by tsimp [σ₁])
    refine (Runs.loop_step (by simp [hIn, rwds]) (s1.mono (fun σ' h' => by rw [h']; exact ih) le_rfl)).mono
      (fun σ' h' => ?_) ?_
    · rw [h']
      funext i; fin_cases i <;> tsimp [σ₁, rwds, pairsOf]
    · simp only [List.length_cons]; nlinarith

end IntegerMultBounds.Schoenhage
