import IntegerMultBounds.Schoenhage.RingProgram

/-! The ring product's constants built on tapes from `p`, `ℓ` and `w` in
unary: the digit width `W = 2^(size M)` with `M = 2p + ℓ + w + 3`, the size
`N = W 2^ℓ`, the ruler, the offset words and the half and rounding words
(`runs_ringConst`). -/

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule

/-! ### Words -/

theorem bits_eq_of {n v : ℕ} {x : List Bool} (hl : x.length = n) (hv : bval x = v) : bits n v = x := by
  rw [← hl, ← hv, bits_bval]

theorem bval_ones (n : ℕ) : bval (ones n) + 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ones, List.replicate_succ, pow_succ] at *; omega

theorem bval_replicate_flatten (b : List Bool) : ∀ r : ℕ,
    bval (List.replicate r b).flatten = wsum b.length (List.replicate r (bval b))
  | 0 => rfl
  | r + 1 => by
    rw [List.replicate_succ, List.flatten_cons, bval_append, bval_replicate_flatten b r]
    simp [wsum, List.replicate_succ]

/-- The rounding word `2^s - 1` in `W + 1` bits. -/
theorem kC_word {W s : ℕ} (hs : s ≤ W + 1) :
    bits (W + 1) (2 ^ s - 1) = ones s ++ List.replicate (W + 1 - s) false := by
  refine bits_eq_of (by simp; omega) ?_
  rw [bval_append, bval_replicate_false]
  have := bval_ones s; simp; omega

/-- An offset word: `r` blocks of the digit `b`, then a zero bit. -/
theorem offset_word (b : List Bool) (r : ℕ) :
    rwd (b.length * r) (wsum b.length (List.replicate r (bval b))) = (List.replicate r b).flatten ++ [false] := by
  refine bits_eq_of (by simp [List.length_flatten, List.sum_replicate]; ring) ?_
  rw [bval_append, bval_replicate_flatten]; simp

theorem clen_replicate_nil (n : ℕ) : clen (List.replicate n []) = n := by
  simp [clen, List.map_replicate, List.sum_replicate]

/-! ### Repeating a block -/

theorem replicate_nil_append (n : ℕ) (Tl : List (List Bool)) :
    List.replicate n [] ++ [] :: Tl = [] :: (List.replicate n [] ++ Tl) := by
  rw [← List.singleton_append, ← List.append_assoc, ← List.replicate_succ', List.replicate_succ]; rfl

/-- Append the block made from `src` once per tick of `qT`. -/
noncomputable def repeatLoop (R : Rule 0) (src dst : Fin 𝕌) (h1 : src ≠ dst) (h2 : src ≠ ι qT) : Cmd 0 𝕌 :=
  .loop (ι qT) (.seq (op0 R true src dst h1) <| .seq (rewind src) (skp (ι qT) (ι tJ) (by decide)))

theorem runs_repeatLoop (R : Rule 0) {src dst : Fin 𝕌} (h1 : src ≠ dst) (h2 : src ≠ ι qT) (h3 : dst ≠ ι qT)
    (h4 : src ≠ ι tJ) (h5 : dst ≠ ι tJ) {x b : List Bool} (hb : output R x (fun j => j.elim0) = syms [b])
    (B : ℕ) (hB : time R x (fun j => j.elim0) ≤ B) :
    ∀ (n : ℕ) (τ : Fin 𝕌 → WTape) (Tl : List (List Bool)) (acc : List Bool) (L : List (List Bool)),
      τ src = reg x → τ dst = ⟨acc :: L, []⟩ → τ (ι qT) = ⟨Tl, List.replicate n []⟩ → τ (ι tJ) = emp →
      Runs (repeatLoop R src dst h1 h2) τ (· = Function.update (Function.update τ dst
        ⟨(acc ++ (List.replicate n b).flatten) :: L, []⟩) (ι qT) ⟨List.replicate n [] ++ Tl, []⟩)
        (n * (B + x.length + 12))
  | 0, τ, Tl, acc, L, hs, hd, hT, _ => by
    refine (Runs.loop_done (by simp [hT]) rfl).mono (fun τ' h => ?_) (by simp)
    rw [← h]; funext y
    by_cases a1 : y = dst <;> by_cases a2 : y = ι qT <;> simp_all [Function.update_apply]
  | n + 1, τ, Tl, acc, L, hs, hd, hT, hJ => by
    have s1 := runs_op0 (a := 0) R true h1 τ (by simp [hs]) (by simp [hd]) [b] (by simpa [hs] using hb)
      (fun _ => ⟨by simp [hd], by simp⟩)
    set τ₁ := Function.update (Function.update τ src (τ src).next) dst ((τ dst).put true [b])
    have s2 := runs_rewind (a := 0) src τ₁
    set τ₂ := Function.update τ₁ src ⟨[], (τ₁ src).left.reverse ++ (τ₁ src).right⟩
    have s3 := runs_skp (a := 0) (show ι qT ≠ ι tJ by decide) τ₂
      (by simp [τ₂, τ₁, h3.symm, h2.symm, hT, List.replicate_succ])
      (by simp [τ₂, τ₁, h4.symm, h5.symm, hJ])
    have hc : (τ₂ (ι qT)).cur.length = 0 := by simp [τ₂, τ₁, h3.symm, h2.symm, hT, List.replicate_succ]
    set τ₃ := Function.update τ₂ (ι qT) (τ₂ (ι qT)).next
    have ih := runs_repeatLoop R h1 h2 h3 h4 h5 hb B hB n τ₃ ([] :: Tl) (acc ++ b) L
      (by simp [τ₃, τ₂, τ₁, h2, h1, hs, reg])
      (by simp [τ₃, τ₂, τ₁, h3, h1.symm, hd])
      (by simp [τ₃, τ₂, τ₁, h3.symm, h2.symm, hT, List.replicate_succ])
      (by simp [τ₃, τ₂, τ₁, (show ι tJ ≠ ι qT by decide), h4.symm, h5.symm, hJ])
    refine (Runs.loop_step (by simp [hT]) ((Runs.then s1 (Runs.then s2 s3)).mono
      (fun τ' h => by rw [h]; exact ih) le_rfl)).mono (fun τ' h => ?_) ?_
    · rw [h]; funext y
      by_cases a1 : y = dst <;> by_cases a2 : y = ι qT <;> by_cases a3 : y = src <;>
        simp_all [τ₃, τ₂, τ₁, Function.update_apply, List.replicate_succ, List.flatten_cons, reg,
          replicate_nil_append]
    · rw [hc]; simp [τ₁, hs, hd, h1, reg]
      nlinarith

/-! ### Unary sums -/

/-- `kS = ones (p + ℓ)`, `kw = ones w`, `qR = ones M`, `qT` with `M` ticks, `qB = ones 0`, `c1 = [1]`. -/
noncomputable def constA : Cmd 0 𝕌 :=
  .seq (op0 Rules.copy false iP kS (by decide)) <| .seq (rewind iP) <|
  .seq (op0 Rules.copy true iL kS (by decide)) <| .seq (rewind iL) <| .seq (rewind kS) <|
  .seq (op0 Rules.copy false iW kw (by decide)) <| .seq (rewind iW) <| .seq (rewind kw) <|
  .seq (op0 Rules.copy false iP (ι qR) (by decide)) <| .seq (rewind iP) <|
  .seq (op0 Rules.copy true iP (ι qR) (by decide)) <| .seq (rewind iP) <|
  .seq (op0 Rules.copy true iL (ι qR) (by decide)) <| .seq (rewind iL) <|
  .seq (op0 Rules.copy true iW (ι qR) (by decide)) <| .seq (rewind iW) <|
  .seq (op0 Rules.copy true iW (ι qR) (by decide)) <| .seq (rewind iW) <| .seq (rewind (ι qR)) <|
  .seq (emit [[true]] (ι c1)) <| .seq (rewind (ι c1)) <|
  .seq (op0 Rules.ticks false (ι qR) (ι qT) (by decide)) <| .seq (rewind (ι qR)) <| .seq (rewind (ι qT)) <|
  .seq (emit [[]] (ι qB)) (rewind (ι qB))

/-- The width bound before rounding up to a power of two. -/
def mW (p l w : ℕ) : ℕ := p + p + l + w + w

set_option maxHeartbeats 2000000 in
theorem runs_constA {p l w : ℕ} (τ : Fin 𝕌 → WTape) (hc : Clean τ) (hP : τ iP = reg (ones p))
    (hL : τ iL = reg (ones l)) (hW : τ iW = reg (ones w)) (hS : τ kS = emp) (hw : τ kw = emp) :
    Runs constA τ (· = Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update τ kS (reg (ones (p + l)))) kw (reg (ones w))) (ι qR) (reg (ones (mW p l w))))
      (ι c1) (reg [true])) (ι qT) ⟨[], List.replicate (mW p l w) []⟩) (ι qB) (reg []))
      (20 * (p + l + w) + 200) := by
  have hz : ∀ i : Fin 𝕋, τ (ι i) = emp := fun i => congrFun hc i
  have hR := hz qR; have h1 := hz c1; have hT := hz qT; have hB := hz qB
  apply Runs.of_wp
  simp only [constA, WP, wp_op0, wp_rewind, wp_emit]
  tsimp [hP, hL, hW, hS, hw, hR, h1, hT, hB, emp, reg, Rules.output_copy, Rules.output_ticks, ones_append]
  have t1 := time_le Rules.copy (ones p) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t2 := time_le Rules.copy (ones l) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t3 := time_le Rules.copy (ones w) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t4 := time_le Rules.ticks (ones (p + p + l + w + w)) (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext x
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [hP, hL, hW, hS, hw, hR, h1, hT, hB, emp, reg, ones_append,
      mW] at *
  · simp only [time_copy, length_ones]
    have hB : Rules.ticks.B = 0 := rfl
    rw [length_ones, hB] at t4
    generalize time Rules.ticks (ones (p + p + l + w + w)) (fun j => j.elim0) = T at t4 ⊢
    have e : clen (List.replicate (p + p + l + w + w) []) = p + p + l + w + w := by
      simp [clen, List.map_replicate, List.sum_replicate]
    rw [e]
    clear t1 t2 t3 hz hR h1 hT hB hP hL hW hS hw hc e
    linarith

/-! ### Powers of two -/

/-- Ticks from `qB` onto `qT`, `qB` cleared, `qR = ones 1`. -/
noncomputable def constB2 : Cmd 0 𝕌 :=
  .seq (op0 Rules.ticks false (ι qB) (ι qT) (by decide)) <| .seq (rewind (ι qB)) <| .seq (rewind (ι qT)) <|
  .seq (clear (ι qB)) <| .seq (emit [[true]] (ι qR)) (rewind (ι qR))

theorem runs_constB2 {b : ℕ} (τ : Fin 𝕌 → WTape) (hB : τ (ι qB) = reg (ones b)) (hT : τ (ι qT) = emp)
    (hR : τ (ι qR) = emp) :
    Runs constB2 τ (· = Function.update (Function.update (Function.update τ (ι qB) emp) (ι qT)
      ⟨[], List.replicate b []⟩) (ι qR) (reg (ones 1))) (6 * b + 30) := by
  apply Runs.of_wp
  simp only [constB2, WP, wp_op0, wp_rewind, wp_clear, wp_emit]
  tsimp [hB, hT, hR, emp, reg, Rules.output_ticks]
  have t1 := time_le Rules.ticks (ones b) (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext x
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [hB, hT, hR, emp, reg, ones] at *
  · have hb : Rules.ticks.B = 0 := rfl
    rw [length_ones, hb] at t1
    generalize time Rules.ticks (ones b) (fun j => j.elim0) = T at t1 ⊢
    simp only [WTape.words, clen_cons, clen_nil, clen_replicate_nil, length_ones, List.reverse_nil,
      List.nil_append, reg, List.length_replicate]
    linarith

/-- Ticks from a unary register `src` onto `qT`. -/
noncomputable def ticksFrom (src : Fin 𝕌) (h : src ≠ ι qT) : Cmd 0 𝕌 :=
  .seq (op0 Rules.ticks false src (ι qT) h) <| .seq (rewind src) (rewind (ι qT))

theorem runs_ticksFrom {src : Fin 𝕌} (h : src ≠ ι qT) {b : ℕ} (τ : Fin 𝕌 → WTape) (hs : τ src = reg (ones b))
    (hT : τ (ι qT) = emp) :
    Runs (ticksFrom src h) τ (· = Function.update τ (ι qT) ⟨[], List.replicate b []⟩) (3 * b + 20) := by
  apply Runs.of_wp
  simp only [ticksFrom, WP, wp_op0, wp_rewind]
  have e1 : (τ src).cur = ones b := by rw [hs]; rfl
  have e2 : (τ src).right = [ones b] := by rw [hs]; rfl
  have e3 : (τ (ι qT)).right = [] := by rw [hT]; rfl
  have e4 : (τ (ι qT)).left = [] := by rw [hT]; rfl
  simp only [e1, e2, e3, Rules.output_ticks, length_ones, ne_eq, reduceCtorEq, not_false_eq_true, true_and,
    parse_syms, Bool.false_eq_true, false_implies, and_true, Function.update_self,
    Function.update_of_ne h.symm, Function.update_of_ne h]
  refine ⟨?_, ?_⟩
  · funext x
    by_cases a1 : x = ι qT
    · subst a1; simp [e4, hT, emp]
    · by_cases a2 : x = src
      · subst a2; simp [a1, hs, reg]
      · simp [a1, a2]
  · have t1 := time_le Rules.ticks (ones b) (fun j => j.elim0) 0 (fun j => j.elim0)
    have hb : Rules.ticks.B = 0 := rfl
    rw [length_ones, hb] at t1
    generalize time Rules.ticks (ones b) (fun j => j.elim0) = T at t1 ⊢
    simp [e4, hs, hT, emp, reg, clen_replicate_nil, WTape.words]
    linarith

/-- Multiply `qR` by two per tick of `qT`, then drop the ticks. -/
noncomputable def doubleT : Cmd 0 𝕌 := .seq (up doubleLoop) (clear (ι qT))

theorem runs_doubleT {j r : ℕ} (τ : Fin 𝕌 → WTape) (hR : τ (ι qR) = reg (ones r)) (hS : τ (ι qS) = emp)
    (hJ : τ (ι tJ) = emp) (hT : τ (ι qT) = ⟨[], List.replicate j []⟩) :
    Runs doubleT τ (· = Function.update (Function.update τ (ι qR) (reg (ones (r * 2 ^ j)))) (ι qT) emp)
      (20 * (r * 2 ^ j - r) + 50 * j + 2 * j + 3) := by
  have s1 : Runs (up doubleLoop) τ (· = Function.update (Function.update τ (ι qR) (reg (ones (r * 2 ^ j))))
      (ι qT) ⟨List.replicate j [] ++ [], []⟩) (20 * (r * 2 ^ j - r) + 50 * j) :=
    runs_up' (runs_doubleLoop j r (τ ∘ ι) [] hR hS hJ hT) (by rw [ext_update, ext_update, ext_self])
  refine (Runs.then s1 (runs_clear (ι qT) _)).mono (fun τ' h => ?_) ?_
  · rw [h, Function.update_idem]; rfl
  · simp [WTape.words, clen_replicate_nil]; omega

theorem runs_upSize {n : ℕ} (τ : Fin 𝕌 → WTape) (hR : τ (ι qR) = reg (ones n)) (hB : τ (ι qB) = reg [])
    (hT : τ (ι qT) = ⟨[], List.replicate n []⟩) (h1 : τ (ι c1) = reg [true]) (hS : τ (ι qS) = emp)
    (hJ : τ (ι tJ) = emp) :
    Runs (up (.seq sizeLoop (.seq (clear qR) (clear qT)))) τ
      (· = Function.update (Function.update (Function.update τ (ι qR) emp) (ι qB) (reg (ones (Nat.size n))))
        (ι qT) emp) (150 * n + 100) :=
  runs_up' (runs_sizeOf (τ ∘ ι) hR hB hT h1 hS hJ) (by rw [ext_update, ext_update, ext_update, ext_self])

/-- The digit width, the size and the count `r = 2^ℓ` in unary. -/
noncomputable def constB : Cmd 0 𝕌 :=
  .seq (up (.seq sizeLoop (.seq (clear qR) (clear qT)))) <| .seq constB2 <| .seq doubleT <|
  .seq (regDup (ι qR) kW (by decide)) <| .seq (ticksFrom iL (by decide)) <| .seq doubleT <|
  .seq (regMove (ι qR) kN (by decide)) <| .seq (emit [[true]] (ι qR)) <| .seq (rewind (ι qR)) <|
  .seq (ticksFrom iL (by decide)) doubleT

/-- The digit width. -/
def wOf (p l w : ℕ) : ℕ := 2 ^ Nat.size (mW p l w)

set_option maxHeartbeats 4000000 in
theorem runs_constB {p l w : ℕ} (τ : Fin 𝕌 → WTape) (hL : τ iL = reg (ones l))
    (hR : τ (ι qR) = reg (ones (mW p l w))) (hB : τ (ι qB) = reg []) (hT : τ (ι qT) = ⟨[], List.replicate (mW p l w) []⟩)
    (h1 : τ (ι c1) = reg [true]) (hS : τ (ι qS) = emp) (hJ : τ (ι tJ) = emp) (hW : τ kW = emp) (hN : τ kN = emp) :
    Runs constB τ (· = Function.update (Function.update (Function.update (Function.update (Function.update τ
      (ι qT) emp) (ι qB) emp) kW (reg (ones (wOf p l w)))) kN (reg (ones (wOf p l w * 2 ^ l)))) (ι qR) (reg (ones (2 ^ l))))
      (220 * (mW p l w) + 30 * (wOf p l w * 2 ^ l) + 100 * wOf p l w + 60 * 2 ^ l + 200 * l + 600) := by
  set M := mW p l w
  set W := wOf p l w
  have s1 := runs_upSize τ hR hB hT h1 hS hJ
  set τ₁ := Function.update (Function.update (Function.update τ (ι qR) emp) (ι qB) (reg (ones (Nat.size M))))
    (ι qT) emp
  have s2 := runs_constB2 τ₁ (b := Nat.size M) (by tsimp [τ₁]) (by tsimp [τ₁]) (by tsimp [τ₁])
  set τ₂ := Function.update (Function.update (Function.update τ₁ (ι qB) emp) (ι qT)
    ⟨[], List.replicate (Nat.size M) []⟩) (ι qR) (reg (ones 1))
  have s3 := runs_doubleT (j := Nat.size M) (r := 1) τ₂ (by tsimp [τ₂]) (by tsimp [τ₂, τ₁, hS])
    (by tsimp [τ₂, τ₁, hJ]) (by tsimp [τ₂])
  rw [one_mul] at s3
  set τ₃ := Function.update (Function.update τ₂ (ι qR) (reg (ones W))) (ι qT) emp
  have s4 := runs_regDup (a := 0) (show ι qR ≠ kW by decide) τ₃ (w := ones W) (by tsimp [τ₃]) (by tsimp [τ₃, τ₂, τ₁, hW])
  set τ₄ := Function.update τ₃ kW (reg (ones W))
  have s5 := runs_ticksFrom (show iL ≠ ι qT by decide) τ₄ (b := l) (by tsimp [τ₄, τ₃, τ₂, τ₁, hL]) (by tsimp [τ₄, τ₃])
  set τ₅ := Function.update τ₄ (ι qT) ⟨[], List.replicate l []⟩
  have s6 := runs_doubleT (j := l) (r := W) τ₅ (by tsimp [τ₅, τ₄, τ₃]) (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, hS])
    (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, hJ]) (by tsimp [τ₅])
  set τ₆ := Function.update (Function.update τ₅ (ι qR) (reg (ones (W * 2 ^ l)))) (ι qT) emp
  have s7 := runs_regMove (a := 0) (show ι qR ≠ kN by decide) τ₆ (w := ones (W * 2 ^ l)) (by tsimp [τ₆])
    (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hN])
  set τ₇ := Function.update (Function.update τ₆ (ι qR) emp) kN (reg (ones (W * 2 ^ l)))
  have s8 := runs_emit (a := 0) [[true]] (ι qR) τ₇ (by tsimp [τ₇, emp])
  set τ₈ := Function.update τ₇ (ι qR) ⟨[[true]].reverse ++ (τ₇ (ι qR)).left, []⟩
  have s9 := runs_rewind (a := 0) (ι qR) τ₈
  set τ₉ := Function.update τ₈ (ι qR) ⟨[], (τ₈ (ι qR)).left.reverse ++ (τ₈ (ι qR)).right⟩
  have s10 := runs_ticksFrom (show iL ≠ ι qT by decide) τ₉ (b := l) (by tsimp [τ₉, τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hL])
    (by tsimp [τ₉, τ₈, τ₇, τ₆])
  set τ₁₀ := Function.update τ₉ (ι qT) ⟨[], List.replicate l []⟩
  have s11 := runs_doubleT (j := l) (r := 1) τ₁₀ (by tsimp [τ₁₀, τ₉, τ₈, τ₇, emp, reg, ones])
    (by tsimp [τ₁₀, τ₉, τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hS]) (by tsimp [τ₁₀, τ₉, τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hJ])
    (by tsimp [τ₁₀])
  rw [one_mul] at s11
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 (Runs.then s7
    (Runs.then s8 (Runs.then s9 (Runs.then s10 s11)))))))))).mono (fun τ' h => ?_) ?_
  · rw [h]; funext x
    simp only [τ₁₀, τ₉, τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [hT, hR, emp, reg] at *
  · have e1 := size_le_self M
    tsimp [τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₈, emp, reg, WTape.words, clen_cons, clen_nil]
    have hW : 2 ^ Nat.size M = W := rfl
    rw [hW]
    omega

/-! ### The ruler -/

theorem rep_tt (n : ℕ) : List.replicate n true ++ [true, true] = List.replicate (n + 2) true := by
  rw [List.replicate_add]; rfl

/-- The ruler builder's drivers from `qR = ones r` and `kW = ones W`. -/
noncomputable def constC1 : Cmd 0 𝕌 :=
  .seq (op1 Rules.drop false (ι qR) (ι c1) (ι sT2) (by decide) (by decide) (by decide)) <|
  .seq (rewind (ι qR)) <| .seq (rewind (ι c1)) <| .seq (rewind (ι sT2)) <|
  .seq (op0 Rules.ticks false (ι sT2) (ι qT) (by decide)) <| .seq (rewind (ι qT)) <| .seq (clear (ι sT2)) <|
  .seq (op0 Rules.copy false kW (ι tU) (by decide)) <| .seq (rewind kW) <|
  .seq (op0 Rules.copy true kW (ι tU) (by decide)) <| .seq (rewind kW) <| .seq (rewind (ι tU)) <|
  .seq (emit [[true, true]] (ι tV)) <| .seq (rewind (ι tV)) <|
  .seq (emit [[true, true]] (ι tO1)) <| .seq (rewind (ι tO1)) <|
  .seq (op0 Rules.copy false (ι tU) (ι tO2) (by decide)) <| .seq (rewind (ι tU)) <|
  .seq (op0 Rules.copy true (ι tO1) (ι tO2) (by decide)) <| .seq (rewind (ι tO1)) <| .seq (rewind (ι tO2)) <|
  .seq (emit [[]] (ι tC)) (rewind (ι tC))

set_option maxHeartbeats 4000000 in
theorem runs_constC1 {r W : ℕ} (τ : Fin 𝕌 → WTape) (hR : τ (ι qR) = reg (ones r)) (h1 : τ (ι c1) = reg [true])
    (hK : τ kW = reg (ones W)) (hS : τ (ι sT2) = emp) (hT : τ (ι qT) = emp) (hU : τ (ι tU) = emp)
    (hV : τ (ι tV) = emp) (hO : τ (ι tO1) = emp) (hO2 : τ (ι tO2) = emp) (hC : τ (ι tC) = emp) :
    Runs constC1 τ (· = Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update τ (ι qT) ⟨[], List.replicate (r - 1) []⟩) (ι tU) (reg (ones (2 * W))))
      (ι tV) (reg (ones (2 * (W + 1 - W))))) (ι tO1) (reg (ones 2))) (ι tO2) (reg (ones (2 * (W + 1)))))
      (ι tC) (reg (ones (2 * (W + 1 - (W + 1)))))) (20 * (r + W) + 300) := by
  have htl : (ones r).tail = ones (r - 1) := by simp [ones, List.tail_replicate]
  have e2 : ones 2 = [true, true] := rfl
  have e3 : 2 * (W + 1 - W) = 2 := by omega
  have e4 : 2 * (W + 1 - (W + 1)) = 0 := by omega
  have e5 : 2 * (W + 1) = W + W + 2 := by ring
  have e6 : 2 * W = W + W := by ring
  rw [e3, e4, e5, e6, e2]
  apply Runs.of_wp
  simp only [constC1, WP, wp_op0, wp_op1, wp_rewind, wp_clear, wp_emit]
  tsimp [hR, h1, hK, hS, hT, hU, hV, hO, hO2, hC, emp, reg, Rules.output_drop, Rules.output_ticks,
    Rules.output_copy, ones_append, htl]
  have t1 := time_le Rules.drop (ones r) (fun _ => [true]) 1 (fun _ => by simp)
  have t2 := time_le Rules.ticks (ones (r - 1)) (fun j => j.elim0) 0 (fun j => j.elim0)
  have hb : Rules.ticks.B = 0 := rfl
  have hd : Rules.drop.B = 1 := rfl
  rw [length_ones, hb] at t2
  rw [length_ones, hd] at t1
  generalize time Rules.ticks (ones (r - 1)) (fun j => j.elim0) = T2 at t2 ⊢
  generalize time Rules.drop (ones r) (fun _ => [true]) = T1 at t1 ⊢
  refine ⟨?_, ?_⟩
  · funext x
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [hR, h1, hK, hS, hT, hU, hV, hO, hO2, hC, emp, reg, ones_append,
      ones, rep_tt] at *
  · simp only [time_copy, length_ones, clen_replicate_nil, List.length_cons, List.length_nil, WTape.words,
      clen_cons, clen_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.append_nil, List.length_replicate]
    omega

/-- Move the ruler to `kR` and clear the drivers. -/
noncomputable def constC3 : Cmd 0 𝕌 :=
  .seq (regMove (ι cR) kR (by decide)) <| .seq (clear (ι tU)) <| .seq (clear (ι tV)) <| .seq (clear (ι tO1)) <|
  .seq (clear (ι tO2)) <| .seq (clear (ι tC)) (clear (ι qT))

/-- The ruler `kR`. -/
noncomputable def constC : Cmd 0 𝕌 := .seq constC1 <| .seq (up rulerBuild) constC3

set_option maxHeartbeats 4000000 in
theorem runs_constC {r W : ℕ} (hr : 1 ≤ r) (τ : Fin 𝕌 → WTape) (hR : τ (ι qR) = reg (ones r))
    (h1 : τ (ι c1) = reg [true]) (hK : τ kW = reg (ones W)) (hS : τ (ι sT2) = emp) (hT : τ (ι qT) = emp)
    (hU : τ (ι tU) = emp) (hV : τ (ι tV) = emp) (hO : τ (ι tO1) = emp) (hO2 : τ (ι tO2) = emp)
    (hC : τ (ι tC) = emp) (hcR : τ (ι cR) = emp) (hJ : τ (ι tJ) = emp) (hkR : τ kR = emp) :
    Runs constC τ (· = Function.update τ kR (reg (Rules.ruler W (W + 1) r)))
      (r * (40 * W + 200) + 80 * W + 800) := by
  have s1 := runs_constC1 τ hR h1 hK hS hT hU hV hO hO2 hC
  set τ₁ := Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update τ (ι qT) ⟨[], List.replicate (r - 1) []⟩) (ι tU) (reg (ones (2 * W))))
      (ι tV) (reg (ones (2 * (W + 1 - W))))) (ι tO1) (reg (ones 2))) (ι tO2) (reg (ones (2 * (W + 1)))))
      (ι tC) (reg (ones (2 * (W + 1 - (W + 1)))))
  have hK1 : r - 1 + 1 = r := by omega
  have s2 : Runs (up rulerBuild) τ₁ (· = Function.update (Function.update τ₁ (ι cR) (reg (Rules.ruler W (W + 1) r)))
      (ι qT) ⟨List.replicate (r - 1) [], []⟩) ((r - 1 + 2) * (12 * (W + (W + 1)) + 100)) := by
    have := runs_rulerBuild (M := W) (W := W + 1) (K := r - 1) (τ₁ ∘ ι) (by tsimp [τ₁, hcR])
      (by tsimp [τ₁]) (by tsimp [τ₁]) (by tsimp [τ₁]) (by tsimp [τ₁])
      (by tsimp [τ₁]) (by tsimp [τ₁, hJ]) (by tsimp [τ₁])
    rw [hK1] at this
    exact runs_up' this (by rw [ext_update, ext_update, ext_self])
  set τ₂ := Function.update (Function.update τ₁ (ι cR) (reg (Rules.ruler W (W + 1) r))) (ι qT)
    ⟨List.replicate (r - 1) [], []⟩
  have s3 : Runs constC3 τ₂ (· = Function.update τ kR (reg (Rules.ruler W (W + 1) r)))
      (6 * (Rules.ruler W (W + 1) r).length + 20 * W + 4 * r + 200) := by
    apply Runs.of_wp
    simp only [constC3, regMove, regIn, cpy, WP, wp_op0, wp_rewind, wp_clear]
    tsimp [τ₂, τ₁, hkR, emp, reg, Rules.output_copy]
    refine ⟨?_, ?_⟩
    · funext x
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> tsimp [hT, hU, hV, hO, hO2, hC, hcR, hkR, emp, reg] at *
    · simp only [time_copy, WTape.words, clen_cons, clen_nil, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.append_nil, length_ones, clen_replicate_nil, clen_reverse]
      omega
  refine (Runs.then s1 (Runs.then s2 s3)).mono (fun τ' h => h) ?_
  have hl := length_ruler (show W + 1 ≤ W + 1 from le_rfl) r
  have e : (r - 1 + 2) * (12 * (W + (W + 1)) + 100) ≤ r * (24 * W + 112) + (24 * W + 112) := by
    have : r - 1 + 2 = r + 1 := by omega
    rw [this]; ring_nf; omega
  nlinarith

/-! ### The half and rounding words -/

/-- `kH = 2^(W-1)` and `kC = 2^s - 1` in `W + 1` bits. -/
noncomputable def constD : Cmd 0 𝕌 :=
  .seq (op0 Rules.mark false kW kH (by decide)) <| .seq (rewind kW) <|
  .seq (op0 (Rules.fill false) true (ι c1) kH (by decide)) <| .seq (rewind (ι c1)) <| .seq (rewind kH) <|
  .seq (op0 Rules.copy false kS kC (by decide)) <| .seq (rewind kS) <|
  .seq (op1 Rules.drop false kW kS (ι sT2) (by decide) (by decide) (by decide)) <| .seq (rewind kW) <|
  .seq (rewind kS) <| .seq (rewind (ι sT2)) <|
  .seq (op0 (Rules.fill false) true (ι sT2) kC (by decide)) <| .seq (clear (ι sT2)) <|
  .seq (op0 (Rules.fill false) true (ι c1) kC (by decide)) <| .seq (rewind (ι c1)) (rewind kC)

set_option maxHeartbeats 4000000 in
theorem runs_constD {W s : ℕ} (hW : 1 ≤ W) (hs : s ≤ W) (τ : Fin 𝕌 → WTape) (hK : τ kW = reg (ones W))
    (hS : τ kS = reg (ones s)) (h1 : τ (ι c1) = reg [true]) (hT : τ (ι sT2) = emp) (hH : τ kH = emp)
    (hC : τ kC = emp) :
    Runs constD τ (· = Function.update (Function.update τ kH (reg (bits (W + 1) (2 ^ (W - 1)))))
      kC (reg (bits (W + 1) (2 ^ s - 1)))) (20 * W + 200) := by
  have eH : bits (W + 1) (2 ^ (W - 1)) = List.replicate (W - 1) false ++ [true] ++ [false] := by
    have := bits_two_pow2 (W - 1)
    rw [show W - 1 + 2 = W + 1 by omega] at this
    rw [this]; simp
  have eC : bits (W + 1) (2 ^ s - 1) = ones s ++ List.replicate (W - s) false ++ [false] := by
    rw [kC_word (by omega), show W + 1 - s = W - s + 1 by omega, List.replicate_succ', List.append_assoc]
  rw [eH, eC]
  have hne : ones W ≠ [] := by simp [ones]; omega
  apply Runs.of_wp
  simp only [constD, WP, wp_op0, wp_op1, wp_rewind, wp_clear]
  tsimp [hK, hS, h1, hT, hH, hC, emp, reg, Rules.output_mark _ _ hne, Rules.output_fill, Rules.output_copy,
    Rules.output_drop]
  have t1 := time_le Rules.mark (ones W) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t2 := time_le (Rules.fill false) [true] (fun j => j.elim0) 0 (fun j => j.elim0)
  have t3 := time_le Rules.drop (ones W) (fun _ => ones s) s (fun _ => by simp)
  have t4 := time_le (Rules.fill false) (ones (W - s)) (fun j => j.elim0) 0 (fun j => j.elim0)
  have b1 : Rules.mark.B = 2 := rfl
  have b2 : (Rules.fill false).B = 1 := rfl
  have b3 : Rules.drop.B = 1 := rfl
  rw [length_ones, b1] at t1; rw [b2] at t2; rw [length_ones, b3] at t3; rw [length_ones, b2] at t4
  generalize time Rules.mark (ones W) (fun j => j.elim0) = T1 at t1 ⊢
  generalize time (Rules.fill false) [true] (fun j => j.elim0) = T2 at t2 ⊢
  generalize time Rules.drop (ones W) (fun _ => ones s) = T3 at t3 ⊢
  generalize time (Rules.fill false) (ones (W - s)) (fun j => j.elim0) = T4 at t4 ⊢
  refine ⟨?_, ?_⟩
  · funext x
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [hK, hS, h1, hT, hH, hC, emp, reg, ones, List.append_assoc] at *
  · simp only [time_copy, length_ones, WTape.words, clen_cons, clen_nil, List.reverse_nil, List.nil_append,
      List.length_replicate, List.length_append, List.length_cons, List.length_nil]
    have e : clen ([ones (W - s)].reverse ++ []) = W - s + 1 := by simp [clen]
    rw [e]
    simp only [List.length_singleton] at t2
    omega

/-! ### The offset words -/

theorem bval_unitBlock (k m : ℕ) : bval (List.replicate k false ++ [true] ++ List.replicate m false) = 2 ^ k := by
  rw [bval_append, bval_append, bval_replicate_false, bval_replicate_false]; simp

/-- `kO`: `r` blocks of `2^(W-1)` and a zero bit. -/
noncomputable def constE1 : Cmd 0 𝕌 :=
  .seq (ticksFrom (ι qR) (by decide)) <| .seq (emit [[]] kO) <|
  .seq (repeatLoop Rules.mark kW kO (by decide) (by decide)) <| .seq (clear (ι qT)) <|
  .seq (op0 (Rules.fill false) true (ι c1) kO (by decide)) <| .seq (rewind (ι c1)) (rewind kO)

set_option maxHeartbeats 4000000 in
theorem runs_constE1 {W r : ℕ} (hW : 1 ≤ W) (τ : Fin 𝕌 → WTape) (hR : τ (ι qR) = reg (ones r))
    (h1 : τ (ι c1) = reg [true]) (hK : τ kW = reg (ones W)) (hT : τ (ι qT) = emp) (hJ : τ (ι tJ) = emp)
    (hO : τ kO = emp) :
    Runs constE1 τ (· = Function.update τ kO
      (reg (rwd (W * r) (wsum W (List.replicate r (2 ^ (W - 1)))))))
      (r * (2 * W + 30) + 6 * W * r + 6 * r + 80) := by
  have hne : ones W ≠ [] := by simp [ones]; omega
  set b := List.replicate (W - 1) false ++ [true]
  have hb : output Rules.mark (ones W) (fun j => j.elim0) = syms [b] := by
    rw [Rules.output_mark _ _ hne, length_ones]
  have hbl : b.length = W := by simp [b]; omega
  have hbv : bval b = 2 ^ (W - 1) := by
    have := bval_unitBlock (W - 1) 0; simpa [b] using this
  have tB : time Rules.mark (ones W) (fun j => j.elim0) ≤ W + 7 := by
    have := time_le Rules.mark (ones W) (fun j => j.elim0) 0 (fun j => j.elim0)
    have b1 : Rules.mark.B = 2 := rfl
    rw [length_ones, b1] at this; omega
  have s1 := runs_ticksFrom (show ι qR ≠ ι qT by decide) τ hR hT
  set τ₁ := Function.update τ (ι qT) ⟨[], List.replicate r []⟩
  have s2 := runs_emit (a := 0) [[]] kO τ₁ (by tsimp [τ₁, hO, emp])
  set τ₂ := Function.update τ₁ kO ⟨[[]].reverse ++ (τ₁ kO).left, []⟩
  have s3 := runs_repeatLoop Rules.mark (src := kW) (dst := kO) (by decide) (by decide) (by decide) (by decide)
    (by decide) hb (W + 7) tB r τ₂ [] [] [] (by tsimp [τ₂, τ₁, hK]) (by tsimp [τ₂, τ₁, hO, emp])
    (by tsimp [τ₂, τ₁]) (by tsimp [τ₂, τ₁, hJ])
  set τ₃ := Function.update (Function.update τ₂ kO ⟨([] ++ (List.replicate r b).flatten) :: [], []⟩)
    (ι qT) ⟨List.replicate r [] ++ [], []⟩
  have s4 := runs_clear (a := 0) (ι qT) τ₃
  set τ₄ := Function.update τ₃ (ι qT) ⟨[], []⟩
  have s5 := runs_op0 (a := 0) (Rules.fill false) true (show ι c1 ≠ kO by decide) τ₄ (by tsimp [τ₄, τ₃, τ₂, τ₁, h1])
    (by tsimp [τ₄, τ₃]) [[false]] (by tsimp [τ₄, τ₃, τ₂, τ₁, h1, Rules.output_fill])
    (fun _ => ⟨by tsimp [τ₄, τ₃], by simp⟩)
  set τ₅ := Function.update (Function.update τ₄ (ι c1) (τ₄ (ι c1)).next) kO ((τ₄ kO).put true [[false]])
  have s6 := runs_rewind (a := 0) (ι c1) τ₅
  set τ₆ := Function.update τ₅ (ι c1) ⟨[], (τ₅ (ι c1)).left.reverse ++ (τ₅ (ι c1)).right⟩
  have s7 := runs_rewind (a := 0) kO τ₆
  have ew : rwd (W * r) (wsum W (List.replicate r (2 ^ (W - 1)))) = (List.replicate r b).flatten ++ [false] := by
    rw [← offset_word b r, hbl, hbv]
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 s7)))))).mono
    (fun τ' h => ?_) ?_
  · rw [h, ew]; funext x
    simp only [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [h1, hO, hT, emp, reg] at *
  · have tF : time (Rules.fill false) [true] (fun j => j.elim0) ≤ 7 := by
      have := time_le (Rules.fill false) [true] (fun j => j.elim0) 0 (fun j => j.elim0)
      have b2 : (Rules.fill false).B = 1 := rfl
      rw [b2] at this; simpa using this
    have cf : clen [(List.replicate r b).flatten ++ [false]] ≤ W * r + 2 := by
      simp [clen, List.length_flatten, List.sum_replicate, hbl]; ring_nf; omega
    tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, h1, hO, emp, reg, WTape.words, clen_replicate_nil, clen_reverse]
    rw [hbl]
    nlinarith [tF]

/-- The block of `2^(w-1)` in `W` bits, in `tU`. -/
noncomputable def constE2a : Cmd 0 𝕌 :=
  .seq (op0 Rules.mark false iW (ι tU) (by decide)) <| .seq (rewind iW) <|
  .seq (op1 Rules.drop false kW iW (ι sT2) (by decide) (by decide) (by decide)) <| .seq (rewind kW) <|
  .seq (rewind iW) <| .seq (rewind (ι sT2)) <|
  .seq (op0 (Rules.fill false) true (ι sT2) (ι tU) (by decide)) <| .seq (clear (ι sT2)) (rewind (ι tU))

set_option maxHeartbeats 4000000 in
theorem runs_constE2a {W w : ℕ} (hw : 1 ≤ w) (hwW : w ≤ W) (τ : Fin 𝕌 → WTape) (hI : τ iW = reg (ones w))
    (hK : τ kW = reg (ones W)) (hU : τ (ι tU) = emp) (hS : τ (ι sT2) = emp) :
    Runs constE2a τ (· = Function.update τ (ι tU)
      (reg (List.replicate (w - 1) false ++ [true] ++ List.replicate (W - w) false))) (10 * W + 80) := by
  have hne : ones w ≠ [] := by simp [ones]; omega
  apply Runs.of_wp
  simp only [constE2a, WP, wp_op0, wp_op1, wp_rewind, wp_clear]
  tsimp [hI, hK, hU, hS, emp, reg, Rules.output_mark _ _ hne, Rules.output_drop, Rules.output_fill]
  have t1 := time_le Rules.mark (ones w) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t2 := time_le Rules.drop (ones W) (fun _ => ones w) w (fun _ => by simp)
  have t3 := time_le (Rules.fill false) (ones (W - w)) (fun j => j.elim0) 0 (fun j => j.elim0)
  have b1 : Rules.mark.B = 2 := rfl
  have b2 : (Rules.fill false).B = 1 := rfl
  have b3 : Rules.drop.B = 1 := rfl
  rw [length_ones, b1] at t1; rw [length_ones, b3] at t2; rw [length_ones, b2] at t3
  generalize time Rules.mark (ones w) (fun j => j.elim0) = T1 at t1 ⊢
  generalize time Rules.drop (ones W) (fun _ => ones w) = T2 at t2 ⊢
  generalize time (Rules.fill false) (ones (W - w)) (fun j => j.elim0) = T3 at t3 ⊢
  refine ⟨?_, ?_⟩
  · funext x
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [hI, hK, hU, hS, emp, reg, ones, List.append_assoc] at *
  · simp only [WTape.words, clen_cons, clen_nil, List.reverse_nil, List.nil_append, List.length_replicate,
      List.length_append, List.length_cons, List.length_nil, length_ones, List.reverse_cons]
    have e : clen ([ones (W - w)] ++ []) = W - w + 1 := by simp [clen]
    simp only [e] at *
    have := hwW
    omega

/-- `kI`: `r` copies of the block in `tU` and a zero bit; `tU` cleared. -/
noncomputable def constE2b : Cmd 0 𝕌 :=
  .seq (ticksFrom (ι qR) (by decide)) <| .seq (emit [[]] kI) <|
  .seq (repeatLoop Rules.copy (ι tU) kI (by decide) (by decide)) <| .seq (clear (ι qT)) <|
  .seq (op0 (Rules.fill false) true (ι c1) kI (by decide)) <| .seq (rewind (ι c1)) <| .seq (rewind kI) (clear (ι tU))

set_option maxHeartbeats 4000000 in
theorem runs_constE2b {W r : ℕ} {b : List Bool} (hbl : b.length = W) (τ : Fin 𝕌 → WTape)
    (hR : τ (ι qR) = reg (ones r)) (h1 : τ (ι c1) = reg [true]) (hU : τ (ι tU) = reg b) (hT : τ (ι qT) = emp)
    (hJ : τ (ι tJ) = emp) (hI : τ kI = emp) :
    Runs constE2b τ (· = Function.update (Function.update τ kI
      (reg ((List.replicate r b).flatten ++ [false]))) (ι tU) emp)
      (r * (2 * W + 30) + 6 * W * r + 6 * r + 2 * W + 90) := by
  have hb : output Rules.copy b (fun j => j.elim0) = syms [b] := Rules.output_copy b _
  have tB : time Rules.copy b (fun j => j.elim0) ≤ W + 7 := by rw [time_copy, hbl]; omega
  have s1 := runs_ticksFrom (show ι qR ≠ ι qT by decide) τ hR hT
  set τ₁ := Function.update τ (ι qT) ⟨[], List.replicate r []⟩
  have s2 := runs_emit (a := 0) [[]] kI τ₁ (by tsimp [τ₁, hI, emp])
  set τ₂ := Function.update τ₁ kI ⟨[[]].reverse ++ (τ₁ kI).left, []⟩
  have s3 := runs_repeatLoop Rules.copy (src := ι tU) (dst := kI) (by decide) (by decide) (by decide) (by decide)
    (by decide) hb (W + 7) tB r τ₂ [] [] [] (by tsimp [τ₂, τ₁, hU]) (by tsimp [τ₂, τ₁, hI, emp])
    (by tsimp [τ₂, τ₁]) (by tsimp [τ₂, τ₁, hJ])
  set τ₃ := Function.update (Function.update τ₂ kI ⟨([] ++ (List.replicate r b).flatten) :: [], []⟩)
    (ι qT) ⟨List.replicate r [] ++ [], []⟩
  have s4 := runs_clear (a := 0) (ι qT) τ₃
  set τ₄ := Function.update τ₃ (ι qT) ⟨[], []⟩
  have s5 := runs_op0 (a := 0) (Rules.fill false) true (show ι c1 ≠ kI by decide) τ₄ (by tsimp [τ₄, τ₃, τ₂, τ₁, h1])
    (by tsimp [τ₄, τ₃]) [[false]] (by tsimp [τ₄, τ₃, τ₂, τ₁, h1, Rules.output_fill])
    (fun _ => ⟨by tsimp [τ₄, τ₃], by simp⟩)
  set τ₅ := Function.update (Function.update τ₄ (ι c1) (τ₄ (ι c1)).next) kI ((τ₄ kI).put true [[false]])
  have s6 := runs_rewind (a := 0) (ι c1) τ₅
  set τ₆ := Function.update τ₅ (ι c1) ⟨[], (τ₅ (ι c1)).left.reverse ++ (τ₅ (ι c1)).right⟩
  have s7 := runs_rewind (a := 0) kI τ₆
  set τ₇ := Function.update τ₆ kI ⟨[], (τ₆ kI).left.reverse ++ (τ₆ kI).right⟩
  have s8 := runs_clear (a := 0) (ι tU) τ₇
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6
    (Runs.then s7 s8))))))).mono (fun τ' h => ?_) ?_
  · rw [h]; funext x
    simp only [τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [h1, hI, hT, hU, emp, reg] at *
  · have tF : time (Rules.fill false) [true] (fun j => j.elim0) ≤ 7 := by
      have := time_le (Rules.fill false) [true] (fun j => j.elim0) 0 (fun j => j.elim0)
      have b2 : (Rules.fill false).B = 1 := rfl
      rw [b2] at this; simpa using this
    tsimp [τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, h1, hI, hU, emp, reg, WTape.words, clen_replicate_nil, clen_reverse]
    simp only [clen, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_append,
      List.length_flatten, List.map_replicate, List.sum_replicate, hbl, List.length_singleton, smul_eq_mul]
    nlinarith [tF]

/-! ### All constants -/

/-- Every constant of the ring product from `p`, `ℓ`, `w` in unary. -/
noncomputable def constAll : Cmd 0 𝕌 :=
  .seq constA <| .seq constB <| .seq constC <| .seq constD <| .seq constE1 <| .seq constE2a <|
  .seq constE2b <| .seq (clear (ι qR)) (clear (ι c1))

/-- The constants' registers after `constAll`. -/
def constBank (p l w : ℕ) (τ : Fin 𝕌 → WTape) : Fin 𝕌 → WTape :=
  let W := wOf p l w
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update τ
    kS (reg (ones (p + l)))) kw (reg (ones w))) kW (reg (ones W))) kN (reg (ones (W * 2 ^ l))))
    kR (reg (Rules.ruler W (W + 1) (2 ^ l)))) kH (reg (bits (W + 1) (2 ^ (W - 1)))))
    kC (reg (bits (W + 1) (2 ^ (p + l) - 1))))
    kO (reg (rwd (W * 2 ^ l) (wsum W (List.replicate (2 ^ l) (2 ^ (W - 1)))))))
    kI (reg (rwd (W * 2 ^ l) (wsum W (List.replicate (2 ^ l) (2 ^ (w - 1))))))

theorem mW_lt_wOf (p l w : ℕ) : mW p l w < wOf p l w := Nat.lt_size_self _

/-- A bound on the constants' steps. -/
def constCost (p l w : ℕ) : ℕ := 2000 * (wOf p l w * 2 ^ l) + 1000 * wOf p l w + 1000 * l + 5000

set_option maxHeartbeats 8000000 in
theorem runs_constAll {p l w : ℕ} (hw : 1 ≤ w) (τ : Fin 𝕌 → WTape) (hc : Clean τ)
    (hP : τ iP = reg (ones p)) (hL : τ iL = reg (ones l)) (hWi : τ iW = reg (ones w))
    (hS : τ kS = emp) (hw' : τ kw = emp) (hW : τ kW = emp) (hN : τ kN = emp) (hR : τ kR = emp)
    (hH : τ kH = emp) (hC : τ kC = emp) (hO : τ kO = emp) (hI : τ kI = emp) :
    Runs constAll τ (· = constBank p l w τ) (constCost p l w) := by
  have hz : ∀ i : Fin 𝕋, τ (ι i) = emp := fun i => congrFun hc i
  set W := wOf p l w
  have hMW := mW_lt_wOf p l w
  have hW1 : 1 ≤ W := by unfold mW at hMW; omega
  have hr : 1 ≤ 2 ^ l := Nat.one_le_two_pow
  have s1 := runs_constA τ hc hP hL hWi hS hw'
  set τ₁ := Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update τ kS (reg (ones (p + l)))) kw (reg (ones w))) (ι qR) (reg (ones (mW p l w))))
      (ι c1) (reg [true])) (ι qT) ⟨[], List.replicate (mW p l w) []⟩) (ι qB) (reg [])
  have s2 := runs_constB (p := p) (l := l) (w := w) τ₁ (by tsimp [τ₁, hL]) (by tsimp [τ₁]) (by tsimp [τ₁])
    (by tsimp [τ₁]) (by tsimp [τ₁]) (by tsimp [τ₁, hz]) (by tsimp [τ₁, hz]) (by tsimp [τ₁, hW]) (by tsimp [τ₁, hN])
  set τ₂ := Function.update (Function.update (Function.update (Function.update (Function.update τ₁
      (ι qT) emp) (ι qB) emp) kW (reg (ones W))) kN (reg (ones (W * 2 ^ l)))) (ι qR) (reg (ones (2 ^ l)))
  have s3 := runs_constC hr τ₂ (W := W) (by tsimp [τ₂]) (by tsimp [τ₂, τ₁]) (by tsimp [τ₂]) (by tsimp [τ₂, τ₁, hz])
    (by tsimp [τ₂]) (by tsimp [τ₂, τ₁, hz]) (by tsimp [τ₂, τ₁, hz]) (by tsimp [τ₂, τ₁, hz]) (by tsimp [τ₂, τ₁, hz])
    (by tsimp [τ₂, τ₁, hz]) (by tsimp [τ₂, τ₁, hz]) (by tsimp [τ₂, τ₁, hz]) (by tsimp [τ₂, τ₁, hR])
  set τ₃ := Function.update τ₂ kR (reg (Rules.ruler W (W + 1) (2 ^ l)))
  have s4 := runs_constD (W := W) (s := p + l) hW1 (by unfold mW at hMW; omega) τ₃ (by tsimp [τ₃, τ₂])
    (by tsimp [τ₃, τ₂, τ₁]) (by tsimp [τ₃, τ₂, τ₁]) (by tsimp [τ₃, τ₂, τ₁, hz]) (by tsimp [τ₃, τ₂, τ₁, hH])
    (by tsimp [τ₃, τ₂, τ₁, hC])
  set τ₄ := Function.update (Function.update τ₃ kH (reg (bits (W + 1) (2 ^ (W - 1)))))
    kC (reg (bits (W + 1) (2 ^ (p + l) - 1)))
  have s5 := runs_constE1 (W := W) (r := 2 ^ l) hW1 τ₄ (by tsimp [τ₄, τ₃, τ₂]) (by tsimp [τ₄, τ₃, τ₂, τ₁])
    (by tsimp [τ₄, τ₃, τ₂]) (by tsimp [τ₄, τ₃, τ₂]) (by tsimp [τ₄, τ₃, τ₂, τ₁, hz]) (by tsimp [τ₄, τ₃, τ₂, τ₁, hO])
  set τ₅ := Function.update τ₄ kO (reg (rwd (W * 2 ^ l) (wsum W (List.replicate (2 ^ l) (2 ^ (W - 1))))))
  have s6 := runs_constE2a (W := W) (w := w) hw (by unfold mW at hMW; omega) τ₅
    (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, hWi]) (by tsimp [τ₅, τ₄, τ₃, τ₂]) (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, hz])
    (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, hz])
  set blk := List.replicate (w - 1) false ++ [true] ++ List.replicate (W - w) false
  have hbl : blk.length = W := by simp [blk]; unfold mW at hMW; omega
  set τ₆ := Function.update τ₅ (ι tU) (reg blk)
  have s7 := runs_constE2b (W := W) (r := 2 ^ l) hbl τ₆ (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂])
    (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁]) (by tsimp [τ₆]) (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂])
    (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hz]) (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hI])
  set τ₇ := Function.update (Function.update τ₆ kI (reg ((List.replicate (2 ^ l) blk).flatten ++ [false])))
    (ι tU) emp
  have s8 := runs_clear (a := 0) (ι qR) τ₇
  have s9 := runs_clear (a := 0) (ι c1) (Function.update τ₇ (ι qR) ⟨[], []⟩)
  have eI : (List.replicate (2 ^ l) blk).flatten ++ [false] =
      rwd (W * 2 ^ l) (wsum W (List.replicate (2 ^ l) (2 ^ (w - 1)))) := by
    rw [← hbl, ← show bval blk = 2 ^ (w - 1) from bval_unitBlock _ _, offset_word]
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6
    (Runs.then s7 (Runs.then s8 s9)))))))).mono (fun τ' h => ?_) ?_
  · clear s1 s2 s3 s4 s5 s6 s7 s8 s9
    rw [h]; simp only [τ₇, eI]; funext x
    by_cases hm : x ∈ [kS, kw, kW, kN, kR, kH, kC, kO, kI, ι qR, ι c1, ι tU, ι qT, ι qB]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [constBank, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁] <;> tsimp [hz, emp] <;> rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14⟩ := hm
      simp only [constBank, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8,
        n9, n10, n11, n12, n13, n14, if_false]
  · clear s1 s2 s3 s4 s5 s6 s7 s8 s9
    tsimp [τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, reg, emp, WTape.words, clen_cons, clen_nil, length_ones]
    have hW' : wOf p l w = W := rfl
    rw [hW']
    unfold constCost
    rw [hW']
    have hM : p + l + w ≤ mW p l w := by unfold mW; omega
    set R := 2 ^ l
    nlinarith [hMW, hW1, hr, Nat.mul_le_mul_right W hr]

end IntegerMultBounds.Schoenhage
