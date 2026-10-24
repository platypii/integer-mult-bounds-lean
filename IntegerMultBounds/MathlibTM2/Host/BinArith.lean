module
public import IntegerMultBounds.MathlibTM2.Host.BinArithZip
public import IntegerMultBounds.MathlibTM2.Host.EachSymPrice


/-!
# Exact binary integer arithmetic on host registers

A natural number `a` held in width `L` is the register contents `binSyms L a` (`a < 2 ^ L`),
least significant bit on top (`Host/Index.lean`). The library runs on the host registers `S.R i`
with spare registers that start and end empty; operands of one operation share their width
unless stated otherwise. Every `_exec` theorem gives the final register file exactly (every other
register ends as it started), `v'.user = v.user`, and an exact step count or an explicit step
bound.

* `Host/BinArithBits.lean`: bit-serial transducers (`addF`, `subF`, `ltF`, `eqF`) and numeral
  lemmas.
* `Host/BinArithZip.lean`: `zipPass`; `bclear`, `bcopy`, `bzero`, `bpad`, `bpad1`, `bwiden`,
  `bmoveLow`, `bshift`; `badd`, `baddTo`, `bsub` (`8 L + 8` steps, carry or borrow into a scan
  slot); `blt`, `beq`, `bcmp` (comparison results into scan slots); the symbol loop `eachSym`.
* `Host/BinArithMul.lean`: schoolbook `bmul` into width `La + Lb`, `O(La (La + Lb))` steps.
* `Host/BinArithDiv.lean`: restoring `bdivmod` (`O(La Lb)` steps) and `bmodmul`.
* This file: conversions between unary and binary registers.
  * `toBinary u wR c t tmp cy`: the empty `c` ends holding `binSyms |wR| |u|`, counting up once
    per symbol of `u` (`incrField`), in at most `k (4 W + 10) + 4 W + 8` steps for `k = |u|`,
    `W = |wR|` (`toBinary_exec`).
  * `toUnary a z w t t₂`: `z` gains `x` ticks on top for `a` holding `binSyms L x`, by Horner's
    rule from the most significant bit on the work register `w` (doubling with `udbl`), in at
    most `6 x + 11 L + 6` steps (`toUnary_exec_linear`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node


variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-! ### Unary to binary -/

/-- One count: set the carry in slot `cy` and add it to the binary register `c` through `tmp`. -/
def countIter (c tmp cy : Fin T) : Pr P T Q A U :=
  .seq (.act (setCarry cy)) (incrField c tmp cy)

/-- `countIter`: `c := binSyms W (j + 1)` from `binSyms W j`, in `4 W + 5` steps. -/
theorem countIter_exec {c tmp : Fin T} (hct : c ≠ tmp) (cy : Fin T) {W j : ℕ} (v : HS T Q A U)
    (S : Stacks T A) (hc : S.R c = binSyms W j) (ht : S.R tmp = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (countIter c tmp cy) (mk v S) (4 * W + 5)
        (mk v' { S with R := Function.update S.R c (binSyms W (j + 1)) }) := by
  have he₁ := Exec.act (body := body) (setCarry cy) (mk v S)
  obtain ⟨v₂, hu₂, -, he₂⟩ := incrField_exec body c tmp cy hct (binBits W j) true
    { v with scan := Function.update v.scan cy (bitSymbol true) } S (by rw [hc, binSyms_eq]) ht
    (by simp)
  rw [incBits_binBits, ← binSyms_eq, length_binBits] at he₂
  exact ⟨v₂, hu₂, Exec.cast (Exec.seq he₁ he₂) (by ring) (by simp)⟩

/-- Unary to binary: `c := binSyms |wR| 0`, then one count per symbol of `u` (kept on `t`). -/
def toBinary (u wR c t tmp cy : Fin T) : Pr P T Q A U :=
  .seq (bzero wR c t) (.seq (eachSym u t (countIter c tmp cy)) (moveR t u id))

/-- `toBinary`: with `k = |u|` and `W = |wR|`, the empty `c` ends holding `binSyms W k` (the
value `k` when `k < 2 ^ W`) and every other register as it started, in at most
`k (4 W + 10) + 4 W + 8` steps. -/
theorem toBinary_exec {u wR c t tmp : Fin T} (hreg : [u, wR, c, t, tmp].Nodup) (cy : Fin T)
    (v : HS T Q A U) (S : Stacks T A) (hc : S.R c = []) (ht : S.R t = []) (htmp : S.R tmp = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ (S.R u).length * (4 * (S.R wR).length + 10) + 4 * (S.R wR).length + 8 ∧
      Exec body (toBinary u wR c t tmp cy) (mk v S) m
        (mk v' { S with
          R := Function.update S.R c (binSyms (S.R wR).length (S.R u).length) }) := by
  have hreg' := hreg
  regs_ne hreg'
  set W := (S.R wR).length with hW
  obtain ⟨v₁, hu₁, he₁⟩ := bzero_exec body (wR := wR) (c := c) (t := t) (by regs_nodup) v S ht
  rw [hc, List.append_nil] at he₁
  set R₁ := Function.update S.R c (binSyms W 0) with hR₁
  let Ψ : ℕ → Regs T A := fun j => Function.update R₁ c (binSyms W j)
  have hp : SymSpec body (countIter c tmp cy) u t (R₁ u) Ψ (4 * W + 5) := by
    intro j _ w S' _ hS'
    obtain ⟨w', hw', he⟩ := countIter_exec body ‹c ≠ tmp› cy (W := W) (j := j) w S'
      (by rw [hS' c ‹u ≠ c›.symm ‹c ≠ t›]; simp [Ψ])
      (by rw [hS' tmp ‹u ≠ tmp›.symm ‹t ≠ tmp›.symm]
          simp [Ψ, hR₁, Function.update_of_ne ‹c ≠ tmp›.symm, htmp])
    refine ⟨w', _, _, hw', le_refl _, he, ?_, ?_, fun k hku hkt => ?_⟩
    · simp [Function.update_of_ne ‹u ≠ c›]
    · simp [Function.update_of_ne ‹c ≠ t›.symm]
    · by_cases hkc : k = c
      · subst hkc; simp [Ψ]
      rw [Function.update_of_ne hkc, hS' k hku hkt]
      simp [Ψ, Function.update_of_ne hkc]
  have h1u : R₁ u = S.R u := by simp [hR₁, Function.update_of_ne ‹u ≠ c›]
  have h1t : R₁ t = [] := by simp [hR₁, Function.update_of_ne ‹c ≠ t›.symm, ht]
  obtain ⟨v₂, R₂, m₂, hu₂, hm₂, he₂, hu₂', ht₂, hΨ₂⟩ := eachSym_exec body ‹u ≠ t› v₁
    { S with R := R₁ } hp (fun k _ _ => by simp [Ψ, hR₁])
  dsimp only at hm₂ hu₂' ht₂ hΨ₂
  rw [h1u] at hm₂ hΨ₂ ht₂
  rw [h1t, List.append_nil] at ht₂
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body t u ‹u ≠ t›.symm id v₂ { S with R := R₂ }
  refine ⟨v₃, _, by rw [hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) rfl ?_⟩
  · dsimp only
    rw [ht₂, List.length_reverse]
    nlinarith [hm₂]
  · congr 2
    funext k
    dsimp only
    simp only [movedR, List.map_id, ht₂, hu₂', List.reverse_reverse, List.append_nil]
    by_cases hku : k = u
    · subst hku; simp [Function.update_of_ne ‹k ≠ c›]
    rw [Function.update_of_ne hku]
    by_cases hkt : k = t
    · subst hkt; simp [Function.update_of_ne ‹c ≠ k›.symm, ht]
    rw [Function.update_of_ne hkt, hΨ₂ k hku hkt]
    by_cases hkc : k = c
    · subst hkc; simp [Ψ]
    simp [Ψ, hR₁, Function.update_of_ne hkc]

/-! ### Binary to unary -/

/-- One Horner step on the unary work register `w`, with a bit in `sym`: `w := 2 w + bit`. -/
def hornerIter (w t₂ : Fin T) : Pr P T Q A U :=
  .cond (fun v => symBit (v.sym.getD blank))
    (.seq (udbl w t₂) (.act (.push (.rt w) (fun _ => tick) .done))) (udbl w t₂)

/-- `hornerIter`: `w := 2 n + bit` ticks from `n` ticks, in at most `4 n + 6` steps. -/
theorem hornerIter_exec {w t₂ : Fin T} (hwt : w ≠ t₂) {n : ℕ} (bit : Bool) (v : HS T Q A U)
    (S : Stacks T A) (hsym : v.sym = some (bitSymbol bit)) (hw : S.R w = List.replicate n tick)
    (ht : S.R t₂ = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 4 * n + 6 ∧
      Exec body (hornerIter w t₂) (mk v S) m
        (mk v' { S with
          R := Function.update S.R w (List.replicate (2 * n + bit.toNat) tick) }) := by
  have hsym' : symBit ((mk v S).var.sym.getD blank) = bit := by simp [hsym]
  obtain ⟨v₁, hu₁, he₁⟩ := udbl_exec body hwt v S ht
  rw [hw, flatMap_replicate_of_replicate, List.length_replicate] at he₁
  cases bit with
  | true =>
      have he₂ := Exec.act (body := body) (.push (.rt w) (fun _ => tick) .done)
        (mk v₁ { S with R := Function.update S.R w (List.replicate (n * 2) tick) })
      simp only [Action.run, mk_var, mk_stk, get_rt, update_rt, store_mk] at he₂
      refine ⟨v₁, _, hu₁, ?_, Exec.cast (Exec.cond_true hsym' (Exec.seq he₁ he₂)) rfl ?_⟩
      · omega
      · congr 2
        simp only [Function.update_idem, Function.update_self, Bool.toNat_true]
        rw [← List.replicate_succ, show n * 2 + 1 = 2 * n + 1 by ring]
  | false =>
      refine ⟨v₁, _, hu₁, ?_, Exec.cast (Exec.cond_false hsym' he₁) rfl ?_⟩
      · omega
      · rw [show 2 * n + false.toNat = n * 2 by simp only [Bool.toNat_false]; ring]

/-- Binary to unary: move `a` reversed onto `t` (most significant bit on top), run one Horner
step per bit on the empty work register `w` while moving the bits back onto `a`, then move the
ticks of `w` onto `z`. -/
def toUnary (a z w t t₂ : Fin T) : Pr P T Q A U :=
  .seq (moveR a t id) (.seq (eachSym t a (hornerIter w t₂)) (moveR w z id))

/-- `toUnary`: `a` holding `binSyms L x` with `x < 2 ^ L`; `z` gains `x` ticks on top and every
other register ends as it started, in at most `6 x + 11 L + 6` steps. -/
theorem toUnary_exec_linear {a z w t t₂ : Fin T} (hreg : [a, z, w, t, t₂].Nodup) {L x : ℕ}
    (hx : x < 2 ^ L) (v : HS T Q A U) (S : Stacks T A) (ha : S.R a = binSyms L x)
    (hw : S.R w = []) (ht : S.R t = []) (ht₂ : S.R t₂ = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 6 * x + 11 * L + 6 ∧
      Exec body (toUnary a z w t t₂) (mk v S) m
        (mk v' { S with R := Function.update S.R z (List.replicate x tick ++ S.R z) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := moveR_exec body a t ‹a ≠ t› id v S
  have hl : (S.R a).length = L := by rw [ha, length_binSyms]
  rw [hl] at he₁
  set R₁ := movedR S.R a t id (S.R a) with hR₁
  have h1t : R₁ t = (binSyms L x).reverse := by simp [hR₁, movedR, ht, ha]
  have h1a : R₁ a = [] := by simp [hR₁, movedR, Function.update_of_ne ‹a ≠ t›]
  have h1 : ∀ k, k ≠ a → k ≠ t → R₁ k = S.R k := by
    intro k h1 h2; simp [hR₁, movedR, Function.update_of_ne h1, Function.update_of_ne h2]
  let hi : ℕ → ℕ := fun j => x / 2 ^ (L - j)
  let Ψ : ℕ → Regs T A := fun j => Function.update R₁ w (List.replicate (hi j) tick)
  have hp : PricedSymSpec body (hornerIter w t₂) t a (R₁ t) Ψ (fun j => 4 * hi j + 6) := by
    intro j hj u S' hsym hS'
    rw [h1t, List.length_reverse, length_binSyms] at hj
    have hbit : (R₁ t)[j] = bitSymbol (x.testBit (L - 1 - j)) := by
      simp only [h1t, getElem_reverse_binSyms]
    have hhi : hi (j + 1) = 2 * hi j + (x.testBit (L - 1 - j)).toNat := by
      simp only [hi]
      rw [show L - (j + 1) = L - 1 - j by omega, div_two_pow_eq x (L - 1 - j),
        show L - 1 - j + 1 = L - j by omega]
    obtain ⟨u', m, hu', hm, he⟩ := hornerIter_exec body ‹w ≠ t₂› (n := hi j)
      (x.testBit (L - 1 - j)) u S' (by rw [hsym, hbit])
      (by rw [hS' w ‹w ≠ t› ‹a ≠ w›.symm]; simp [Ψ])
      (by rw [hS' t₂ ‹t ≠ t₂›.symm ‹a ≠ t₂›.symm]
          simp [Ψ, Function.update_of_ne ‹w ≠ t₂›.symm, h1 t₂ ‹a ≠ t₂›.symm ‹t ≠ t₂›.symm, ht₂])
    refine ⟨u', _, m, hu', ?_, he, ?_, ?_, fun k hkt hka => ?_⟩
    · exact hm
    · simp [Function.update_of_ne ‹w ≠ t›.symm]
    · simp [Function.update_of_ne ‹a ≠ w›]
    · by_cases hkw : k = w
      · subst hkw; simp [Ψ, hhi]
      rw [Function.update_of_ne hkw, hS' k hkt hka]
      simp [Ψ, Function.update_of_ne hkw]
  obtain ⟨v₂, R₂, m₂, hu₂, hm₂, he₂, ht₂', ha₂, hΨ₂⟩ := eachSym_priced_exec body ‹a ≠ t›.symm v₁
    { S with R := R₁ } hp (fun k hkt hka => by
      dsimp only
      by_cases hkw : k = w
      · subst hkw
        simp [Ψ, hi, Nat.div_eq_of_lt hx, h1 k ‹a ≠ k›.symm ‹k ≠ t›, hw]
      simp [Ψ, Function.update_of_ne hkw])
  dsimp only at hm₂ ht₂' ha₂ hΨ₂
  rw [h1t, List.length_reverse, length_binSyms] at hm₂ hΨ₂
  rw [h1t, h1a, List.reverse_reverse, List.append_nil] at ha₂
  have h2w : R₂ w = List.replicate x tick := by
    rw [hΨ₂ w ‹w ≠ t› ‹a ≠ w›.symm]; simp [Ψ, hi]
  have hgrowth : ∀ j, 0 ≤ j → j < 0 + L → 2 * hi j ≤ hi (j + 1) := by
    intro j _ hj
    have hd := div_two_pow_eq x (L - 1 - j)
    have he : L - 1 - j + 1 = L - j := by omega
    rw [he] at hd
    dsimp only [hi]
    rw [show L - (j + 1) = L - 1 - j by omega]
    omega
  have hprice := symLoopPrice_le_doubling hi L 0 hgrowth
  have hend : hi (0 + L) = x := by simp [hi]
  rw [hend] at hprice
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body w z ‹z ≠ w›.symm id v₂ { S with R := R₂ }
  refine ⟨v₃, _, by rw [hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) rfl ?_⟩
  · dsimp only
    rw [h2w, List.length_replicate]
    omega
  · congr 2
    funext k
    dsimp only
    simp only [movedR, List.map_id, h2w, List.reverse_replicate]
    by_cases hkz : k = z
    · subst hkz
      simp [Function.update_of_ne ‹k ≠ w›, hΨ₂ k ‹k ≠ t› ‹a ≠ k›.symm, Ψ,
        h1 k ‹a ≠ k›.symm ‹k ≠ t›]
    rw [Function.update_of_ne hkz, Function.update_of_ne hkz]
    by_cases hkw : k = w
    · subst hkw; rw [Function.update_self, hw]
    rw [Function.update_of_ne hkw]
    by_cases hka : k = a
    · subst hka; rw [ha₂, ha]
    by_cases hkt : k = t
    · subst hkt; rw [ht₂', ht]
    rw [hΨ₂ k hkt hka]
    simp [Ψ, Function.update_of_ne hkw, h1 k hka hkt]


/-- Compatibility with the former coarse conversion budget. -/
theorem toUnary_exec {a z w t t₂ : Fin T} (hreg : [a, z, w, t, t₂].Nodup) {L x : ℕ}
    (hx : x < 2 ^ L) (v : HS T Q A U) (S : Stacks T A) (ha : S.R a = binSyms L x)
    (hw : S.R w = []) (ht : S.R t = []) (ht₂ : S.R t₂ = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ L * (4 * x + 11) + 2 * x + 6 ∧
      Exec body (toUnary a z w t t₂) (mk v S) m
        (mk v' { S with R := Function.update S.R z (List.replicate x tick ++ S.R z) }) := by
  obtain ⟨v', m, hu, hm, he⟩ := toUnary_exec_linear body hreg hx v S ha hw ht ht₂
  have hbound : 6 * x + 11 * L + 6 ≤ L * (4 * x + 11) + 2 * x + 6 := by
    cases L with
    | zero =>
      simp only [pow_zero] at hx
      have hx0 : x = 0 := by omega
      simp [hx0]
    | succ L => nlinarith
  exact ⟨v', m, hu, hm.trans hbound, he⟩

end IntegerMultBounds.MathlibTM2.Host
