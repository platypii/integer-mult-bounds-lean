module

public import IntegerMultBounds.MathlibTM2.Routing.SelectivePatterns

/-!
# Concrete host rotations of the selective schedule

Each rotation uses the actual five-field bank and its own static descriptor bank.
Both live-header callbacks are executed and priced; the resulting record-rank map
is precisely the corresponding instruction of `selectiveRunIdx`.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node (moveRecs)
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable (p : Par) (X : ℕ)

def selectiveRotOp (off : Off) (neg : Bool) : Op :=
  match off with
  | .A | .Z => .rotY neg off
  | _ => .rotB neg off

theorem selectiveRotation_idx (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (off : Off) (neg : Bool) (i : ℕ) :
    selectiveIdx p X active (fun y x => slotPhysicalRead s y x) (selectiveRotOp off neg) i =
      rotIdx (selectiveLen p X) (selectiveTgt off) neg (selectiveOffset p X active s off) i := by
  cases off <;> rfl

theorem selectiveOffset_high (hG : 0 < p.G) (hK : 0 < p.K) (hGK : p.G < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (off : Off) :
    OffHigh (selectiveLen p X) (selectiveTgt off) (selectiveOffset p X active s off) := by
  have heq := funext (selectivePatterns_offset p X hG hK hGK active s off)
  rw [← heq]
  exact headerOffset_high _ _ le_rfl _ _

theorem selectiveOffset_lt (hG : 0 < p.G) (hK : 0 < p.K) (hGK : p.G < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (off : Off) (i : ℕ) :
    selectiveOffset p X active s off i < 2 ^ selectiveLen p X (selectiveTgt off) := by
  rw [← selectivePatterns_offset p X hG hK hGK active s off i, selectiveTarget_len]
  exact patternGateValue_lt _ _ _

def selectiveRotationCost (off : Off) : ℕ :=
  headerCodeCost (selectiveTargetWidth p off) (selectiveSourceWidth p X off)
    (higherFields (selectiveTgt off)).length

/-- Every selective rotation has a common quadratic header-generation budget. -/
theorem selectiveRotationCost_le (n : ℕ) (hfields : fieldsLen (selectiveLen p X) = n) (off : Off) :
    selectiveRotationCost p X off ≤ headerCodeCost n n 5 := by
  have htotal : p.wc + (p.wy + 2 * p.wc + X) = n := by
    simp only [fieldsLen, selectiveLen, Fin.sum_univ_succ] at hfields
    simp at hfields
    omega
  have ht : selectiveTargetWidth p off ≤ n := by cases off <;> simp only [selectiveTargetWidth] <;> omega
  have hs : selectiveSourceWidth p X off ≤ n := by cases off <;> simp only [selectiveSourceWidth] <;> omega
  have hf : (higherFields (selectiveTgt off)).length ≤ 5 := by rw [higherFields_length]; omega
  unfold selectiveRotationCost headerCodeCost patternCodeCost
  gcongr

def selectiveUniformRotationCost (n M B : ℕ) : ℕ :=
  M * (2 * headerCodeCost n n 5 + 12 * B + 8 * n + 60) + 8 * n + 55

/-- Long records absorb descriptor computation and both complete rotation scans. -/
theorem selectiveUniformRotationCost_amortized (n rb M B : ℕ)
    (hM : 1 ≤ M) (hB : (n + rb + 1) ^ 2 ≤ B) :
    selectiveUniformRotationCost n M (n + rb + B) ≤ 400 * (M * B) := by
  have hlinear : n + rb + 1 ≤ B := by nlinarith
  have hi : 2 * headerCodeCost n n 5 + 12 * (n + rb + B) + 8 * n + 60 ≤ 334 * B := by
    unfold headerCodeCost patternCodeCost
    nlinarith
  have hm := Nat.mul_le_mul_left M hi
  have hc : 8 * n + 55 ≤ 63 * B := by omega
  have hv : B ≤ M * B := by simpa using Nat.mul_le_mul_right B hM
  unfold selectiveUniformRotationCost
  nlinarith only [hm, hc, hv]

/-- Both class scans, forward-order restoration and counter cleanup are included. -/
theorem selectiveRotationPassCost_le (n R B : ℕ) (hfields : fieldsLen (selectiveLen p X) = n) (off : Off) :
    classMoveCost (nd := 2) (selectiveRotationCost p X off) (selectiveRotationCost p X off)
      (R * 2 ^ fieldsLen (selectiveLen p X)) B (selectiveLen p X) ≤
      selectiveUniformRotationCost n (R * 2 ^ n) B := by
  have hr := selectiveRotationCost_le p X n hfields off
  have hsum : (∑ f, selectiveLen p X f) = n := hfields
  calc
    _ ≤ classMoveCost (nd := 2) (headerCodeCost n n 5) (headerCodeCost n n 5)
        (R * 2 ^ fieldsLen (selectiveLen p X)) B (selectiveLen p X) := by
      unfold classMoveCost idxStepCost
      gcongr
    _ = _ := by
      unfold classMoveCost idxStepCost selectiveUniformRotationCost
      rw [hfields, hsum]
      ring

variable {T Q A : ℕ} {P U : Type}

/-- Actual execution of one complete selective rotation, including both header
constructions, all descriptor scans and all scratch cleanup. -/
theorem selectiveRotate_exec (body : P → Pr P T Q A U)
    (hG : 0 < p.G) (hK : 0 < p.K) (hGK : p.G < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (off : Off) (neg : Bool)
    {cf : Fin 5 → Fin T} {ι : PatternReg 2 → Fin T}
    (bank : HeaderBank cf ι (selectiveTgt off))
    {src out ctr tmp cnt ctmp : Fin T} {dst aux : Fin 2 → Fin T}
    (hr : MoveRegs (fun k => (∃ f, cf f = k) ∨ (∃ r, ι r = k)) src dst aux out ctr tmp cnt ctmp)
    {R B : ℕ} (hB : 1 ≤ B)
    {l : List (List (Fin (A + 4)))} (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p X))
    (hlB : ∀ r ∈ l, r.length = B)
    {cc kk : List (Fin (A + 4))} (hcB : cc.length = B)
    (hkk : kk.length = R * 2 ^ fieldsLen (selectiveLen p X))
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = l.flatten) (hctr : S.R ctr = cc) (hcnt : S.R cnt = kk)
    (htmp : S.R tmp = []) (hctmp : S.R ctmp = []) (hout : S.R out = [])
    (hdst : ∀ d, S.R (dst d) = []) (haux : ∀ d, S.R (aux d) = [])
    (hI : HeaderInv (selectiveLen p X) cf ι (selectivePatterns p X hG hK active s off) S.R 0) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ classMoveCost (nd := 2) (selectiveRotationCost p X off) (selectiveRotationCost p X off)
        (R * 2 ^ fieldsLen (selectiveLen p X)) B (selectiveLen p X) ∧
      Exec body (headerRotate cf ι (higherFields (selectiveTgt off)) (selectiveGate off) neg
        src dst aux out ctr tmp cnt ctmp) (mk v S) m
        (mk v' { S with
          R := Function.update S.R src (moveRecs
            (rotPerm (R := R) neg (selectiveOffset_high p X hG hK hGK active s off)
              (fieldOff_add_le_total (selectiveLen p X) (selectiveTgt off))) l).flatten }) := by
  have he := headerRotate_exec body bank (higherFields (selectiveTgt off))
    (selectiveStart p X off) (higherFields_chain (selectiveLen p X) (selectiveTgt off))
    (selectiveHeader_width p X off) (selectiveTarget_len p X off) le_rfl
    (selectiveGate off) (selectivePatterns p X hG hK active s off) neg hr
    (fieldOff_add_le_total (selectiveLen p X) (selectiveTgt off)) hB hl hlB hcB hkk v S
    hsrc hctr hcnt htmp hctmp hout hdst haux hI
  have heq := funext (selectivePatterns_offset p X hG hK hGK active s off)
  have hπ : rotPerm (R := R) neg
      (headerOffset_high (len := selectiveLen p X) (selectiveTgt off) (selectiveStart p X off)
        le_rfl (selectiveGate off) (selectivePatterns p X hG hK active s off))
      (fieldOff_add_le_total (selectiveLen p X) (selectiveTgt off)) =
      rotPerm (R := R) neg (selectiveOffset_high p X hG hK hGK active s off)
        (fieldOff_add_le_total (selectiveLen p X) (selectiveTgt off)) := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    change rotIdx (selectiveLen p X) (selectiveTgt off) neg
      (headerOffset (selectiveStart p X off) (selectiveGate off)
        (selectivePatterns p X hG hK active s off)) i = _
    rw [heq]
    rfl
  rw [hπ] at he
  exact he

end IntegerMultBounds.MathlibTM2.Routing
