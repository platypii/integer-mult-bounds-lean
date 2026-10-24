module

public import IntegerMultBounds.MathlibTM2.Routing.SelectiveKeyTarget
public import IntegerMultBounds.MathlibTM2.Routing.SelectiveKeyLayout
public import IntegerMultBounds.MathlibTM2.Routing.PatternCode
public import IntegerMultBounds.MathlibTM2.Routing.KeyEmission

/-! Executed emission of every digit of a full selective destination key. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable {T Q A : ℕ} {P U : Type}
variable (p : Par) (X rb : ℕ) (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

def keyPatternStatic : PatternReg 6 → List (Fin (A + 4))
  | .desc k => if k = 0 then (patternTable (selectiveKeyPattern p X active s)).flatten.map bitSymbol
      else binSyms p.wy (maskVal p.wy id)
  | _ => []

def KeyPatternInv (ι : PatternReg 6 → Fin T) (R : Fin T → List (Fin (A + 4))) (i : ℕ) : Prop :=
  ∀ r : PatternReg 6, r ≠ .st → R (ι r) = match r with
    | .fld f => binSyms (selectiveKeyLen p X rb f) (digit (selectiveKeyLen p X rb) f i)
    | _ => keyPatternStatic p X active s r

variable {p X rb active s}

/-- Updating the accumulator never changes live key counters or metadata. -/
theorem KeyPatternInv.update {ι : PatternReg 6 → Fin T} {acc : Fin T}
    (ha : ∀ r, ι r ≠ acc) {R : Fin T → List (Fin (A + 4))} {i : ℕ}
    (hI : KeyPatternInv p X rb active s ι R i) (w : List (Fin (A + 4))) :
    KeyPatternInv p X rb active s ι (Function.update R acc w) i := by
  intro r hr
  rw [Function.update_of_ne (ha r)]
  exact hI r hr

variable (p X rb)

def selectiveKeyField (ι : PatternReg 6 → Fin T) (acc : Fin T) (f : Fin 6) : Pr P T Q A U :=
  if f = 1 then patternKey ((higherFields (0 : Fin 5)).map fun g => ι (.fld g.castSucc))
    (ι (.word 0)) (ι (.desc 0)) (ι .ts) (ι .tm) (ι .dst) (ι (.word 1))
    (ι (.fld 1)) (ι (.desc 1)) (ι (.spare 0)) (ι (.spare 1)) (ι (.spare 2)) acc (ι .st)
  else copyF (ι (.fld f)) (ι (.spare 0)) acc (ι .st)

def selectiveKeyFieldCost (f : Fin 6) : ℕ :=
  if f = 1 then selectiveKeyTargetCost p X else 5 * selectiveKeyLen p X rb f + 4

variable (active s)

/-- Each actual field emitter restores every register except the accumulator. -/
theorem selectiveKeyField_exec (hK : 0 < p.K) (body : P → Pr P T Q A U)
    (ι : PatternReg 6 → Fin T) (hι : Function.Injective ι) (acc : Fin T) (ha : ∀ r, ι r ≠ acc)
    (f : Fin 6) (i : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hI : KeyPatternInv p X rb active s ι S.R i) :
    ∃ v', v'.user = v.user ∧
      Exec body (selectiveKeyField ι acc f) (mk v S) (selectiveKeyFieldCost p X rb f)
        (mk v' { S with R := Function.update S.R acc ((binSyms (selectiveKeyLen p X rb f) (selectiveKeyDig p X rb active s i f)).reverse ++ S.R acc) }) := by
  have hfields (g : Fin 6) : S.R (ι (.fld g)) =
      binSyms (selectiveKeyLen p X rb g) (digit (selectiveKeyLen p X rb) g i) := hI (.fld g) (by simp)
  by_cases hf : f = 1
  · subst f
    have hlen (g : Fin 5) : selectiveKeyLen p X rb g.castSucc = selectiveLen p X g := by
      fin_cases g <;> rfl
    obtain ⟨v', hu, he⟩ := selectiveKeyTarget_exec p X hK active s body
      (fun g => ι (.fld g.castSucc))
      (header := ι (.word 0)) (desc := ι (.desc 0)) (ts := ι .ts) (tm := ι .tm)
      (dst := ι .dst) (word := ι (.word 1)) (mask := ι (.desc 1))
      (t0 := ι (.spare 0)) (t1 := ι (.spare 1)) (t2 := ι (.spare 2)) (acc := acc) (st := ι .st)
      (by simp [hι.eq_iff, ha]) (by simp [hι.eq_iff])
      (fun g _ => by simp [hι.eq_iff]) i v S
      (fun g => by
        rw [hfields g.castSucc, hlen, selectiveKey_digit])
      (hI (.word 0) (by simp)) (hI (.word 1) (by simp))
      (by simpa [keyPatternStatic] using hI (.desc 0) (by simp))
      (by simpa [keyPatternStatic] using hI (.desc 1) (by simp))
      (hI .ts (by simp)) (hI .tm (by simp)) (hI .dst (by simp))
      (hI (.spare 0) (by simp)) (hI (.spare 1) (by simp)) (hI (.spare 2) (by simp))
    exact ⟨v', hu, by simpa [selectiveKeyField, selectiveKeyFieldCost, selectiveKeyDig, selectiveKeyLen] using he⟩
  · obtain ⟨v', hu, he⟩ := copyF_exec body (ι (.fld f)) (ι (.spare 0)) acc (ι .st)
      (hι.ne (by simp)) (ha _) (ha _) (hι.ne (by simp)) v S (hI (.spare 0) (by simp))
    rw [hfields f] at he
    exact ⟨v', hu, by simpa [selectiveKeyField, selectiveKeyFieldCost, selectiveKeyDig, hf] using he⟩

/-- A structural list of concrete field emitters, with exact summed cost. -/
theorem selectiveKeyFields_exec (hK : 0 < p.K) (body : P → Pr P T Q A U)
    (ι : PatternReg 6 → Fin T) (hι : Function.Injective ι) (acc : Fin T) (ha : ∀ r, ι r ≠ acc)
    (fields : List (Fin 6)) (i : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hI : KeyPatternInv p X rb active s ι S.R i) :
    ∃ v', v'.user = v.user ∧
      Exec body (Prog.seqList (fields.map (selectiveKeyField ι acc))) (mk v S)
        ((fields.map (selectiveKeyFieldCost p X rb)).sum + 1)
        (mk v' { S with R := Function.update S.R acc ((fields.flatMap fun f => binSyms (selectiveKeyLen p X rb f)
            (selectiveKeyDig p X rb active s i f)).reverse ++ S.R acc) }) := by
  induction fields generalizing v S with
  | nil =>
    exact ⟨v, rfl, Exec.cast (Exec.act (body := body) .done (mk v S)) rfl (by simp)⟩
  | cons f fs ih =>
    obtain ⟨v₁, hu₁, he₁⟩ := selectiveKeyField_exec p X rb active s hK body ι hι acc ha f i v S hI
    let R₁ := Function.update S.R acc
      ((binSyms (selectiveKeyLen p X rb f) (selectiveKeyDig p X rb active s i f)).reverse ++ S.R acc)
    obtain ⟨v₂, hu₂, he₂⟩ := ih v₁ { S with R := R₁ } (KeyPatternInv.update ha hI _)
    refine ⟨v₂, hu₂.trans hu₁, Exec.cast (Exec.seq he₁ he₂) ?_ ?_⟩
    · simp; omega
    · simp [R₁, List.flatMap_cons, List.reverse_append, List.append_assoc]

def selectiveKeyEmitter (ι : PatternReg 6 → Fin T) (acc : Fin T) : Pr P T Q A U :=
  Prog.seqList ((List.finRange 6).map (selectiveKeyField ι acc))

def selectiveKeyEmitterCost : ℕ := ((List.finRange 6).map (selectiveKeyFieldCost p X rb)).sum + 1

theorem selectiveKeyEmitterCost_eq :
    selectiveKeyEmitterCost p X rb = selectiveKeyTargetCost p X + 5 * (3 * p.wc + X + rb) + 21 := by
  simp [selectiveKeyEmitterCost, List.finRange_succ, selectiveKeyFieldCost, selectiveKeyLen]
  omega

/-- Complete-rank key emission is quadratic in address width and linear in row-key width. -/
theorem selectiveKeyEmitterCost_le (n : ℕ) (hfields : fieldsLen (selectiveLen p X) = n) :
    selectiveKeyEmitterCost p X rb ≤ n * (6 * n + 25) + 13 * n + 5 * rb + 66 := by
  have htotal : p.wc + (p.wy + 2 * p.wc + X) = n := by
    simp only [fieldsLen, selectiveLen, Fin.sum_univ_succ] at hfields
    simp at hfields
    omega
  have hy : p.wy ≤ n := by omega
  have hs : p.wy + 2 * p.wc + X ≤ n := by omega
  have ht : selectiveKeyTargetCost p X ≤ n * (6 * n + 25) + 8 * n + 45 := by
    unfold selectiveKeyTargetCost
    gcongr
  rw [selectiveKeyEmitterCost_eq]
  omega

/-- The concrete emitter meets the executed full-stream driver's interface. -/
theorem selectiveKeyEmitter_spec (hK : 0 < p.K) (body : P → Pr P T Q A U)
    (ι : PatternReg 6 → Fin T) (hι : Function.Injective ι) (src acc : Fin T)
    (hs : ∀ r, ι r ≠ src) (ha : ∀ r, ι r ≠ acc) :
    KeyEmissionSpec body (selectiveKeyEmitter ι acc) (fun f => ι (.fld f))
      (selectiveKeyLen p X rb) src acc (KeyPatternInv p X rb active s ι)
      (selectiveKeyBits p X rb active s) (selectiveKeyEmitterCost p X rb) where
  runs i v S hI := selectiveKeyFields_exec p X rb active s hK body ι hι acc ha (List.finRange 6) i v S hI
  digits R i hI f := hI (.fld f) (by simp)
  reidx := by
    intro R R' i j hI hfields hother r hr
    cases r <;> first
      | exact hfields _
      | contradiction
      | (rw [hother _ (hs _) (ha _) (fun f => hι.ne (by simp))]; exact hI _ (by simp))

end IntegerMultBounds.MathlibTM2.Routing
