module

public import IntegerMultBounds.MathlibTM2.M6.BitHelperParentSeeds
public import IntegerMultBounds.MathlibTM2.Cover.FallbackFiberBank

/-! Compute the width, row and block counters for a restored PR589 target scan. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)
variable {T Q : ℕ} {P U : Type}

/-- Slots 0–2 receive the three headers. Each power reads its own seed in
slots 3–5, with a common radix in slot 6 and common scratch in slots 7–13. -/
def stagePowerPorts (i : Fin 3) : Fin 10 ↪ Fin 14 :=
  ⟨![6,(i.natAdd 3).castAdd 8,i.castAdd 11,7,8,9,10,11,12,13],(by decide : ∀ i : Fin 3,
    Function.Injective (![6,(i.natAdd 3).castAdd 8,i.castAdd 11,7,8,9,10,11,12,13] : Fin 10 → Fin 14)) i⟩

def stageDegrees : Fin 3 → ℕ := ![112,4096,16]

def stagePowerTime (M seed d : ℕ) :=
  dimensionTime M.size seed.size d + (4*(d*M.size+seed.size)+6)

theorem stagePower_exec (body : P → Pr P T Q prime U) (r : Fin 14 ↪ Fin T) (i : Fin 3)
    (M seed : ℕ) (u : HS T Q prime U) (S : Stacks T prime)
    (base : S.R (r 6) = binSyms M.size M)
    (word : S.R (r ((i.natAdd 3).castAdd 8)) = binSyms seed.size seed)
    (empty : S.R (r (i.castAdd 11)) = [])
    (scratch : ∀ j : Fin 14, 7 ≤ j.val → S.R (r j) = []) :
    let dst := r (i.castAdd 11)
    let value := M^(stageDegrees i)*seed
    ∃ v t, v.user = u.user ∧ t ≤ stagePowerTime M seed (stageDegrees i) ∧
      Exec body (swapPrefix ((stagePowerPorts i).trans r) (stageDegrees i))
        (mk u S) t (mk v {S with R := Function.update S.R dst (binSyms value.size value)}) := by
  intro dst value
  obtain ⟨v,t,user,paid,run⟩ := scaledPrefix_exec body ((stagePowerPorts i).trans r)
    (stageDegrees i) M.size seed.size M seed (Nat.lt_size_self _) (Nat.lt_size_self _)
    u S base word (fun j lo hi => by
      by_cases h : j = 2
      · subst j; exact empty
      · apply scratch
        exact (by decide : ∀ i : Fin 3, ∀ j : Fin 10, 2 ≤ j → j < 9 → j ≠ 2 →
          7 ≤ (stagePowerPorts i j).val) i j lo hi h)
  rw [canonicalBits_symbols] at run
  exact ⟨v,t,user,paid,run⟩

theorem stagePowerValues (w B W : ℕ) (i : Fin 3) :
    (prime^w)^(stageDegrees i)*(![W,1,B] i) =
      ![(prime^w)^112*W,prime^(64*(w*64)),(prime^w)^16*B] i := by
  fin_cases i
  · rfl
  · change (prime^w)^4096*1 = prime^(64*(w*64))
    rw [Nat.mul_one,← pow_mul]
    congr 1
    omega
  · rfl

/-- All three fixed powers cost at most a constant times the volume.
Two radix factors suffice to pay for binary multiplication. -/
theorem stageDimensionsTime_le (M B W : ℕ) (hm : 0 < M) (hb : 0 < B) (hw : 0 < W) :
    let seed := (![W,1,B] : Fin 3 → ℕ)
    ((List.finRange 3).map (fun i => stagePowerTime M (seed i) (stageDegrees i))).sum+2 ≤
      1530000002*(M^2*(B*W)) := by
  intro seed
  let V := M^2*(B*W)
  have pos := Nat.mul_pos hb hw
  have radix : M ≤ M^2 := by simpa [pow_two] using Nat.le_mul_of_pos_right M hm
  have digits : M.size ≤ M := Nat.size_le.mpr Nat.lt_two_pow_self
  have scale : M^2 ≤ V := Nat.le_mul_of_pos_right _ pos
  have h := digits.trans (radix.trans scale)
  have square : M.size*M.size ≤ V := (Nat.mul_le_mul digits digits).trans (by simpa [pow_two] using scale)
  have vpos : 0 < V := Nat.mul_pos (pow_pos hm 2) pos
  have each (i : Fin 3) : stagePowerTime M (seed i) (stageDegrees i) ≤ 510000000*V := by
    have small : seed i ≤ B*W := by
      fin_cases i
      · exact Nat.le_mul_of_pos_left _ hb
      · exact pos
      · exact Nat.le_mul_of_pos_right _ hw
    have width : (seed i).size ≤ B*W := (Nat.size_le.mpr Nat.lt_two_pow_self).trans small
    have tail := width.trans (Nat.le_mul_of_pos_left _ (pow_pos hm 2))
    have cross : M.size*(seed i).size ≤ V := Nat.mul_le_mul (digits.trans radix) width
    have degree : stageDegrees i ≤ 4096 := (by decide : ∀ i, stageDegrees i ≤ 4096) i
    calc
      _ ≤ 6*(seed i).size+6+4096*((12*M.size+18)*(4096*M.size+(seed i).size)+20*M.size+26)+
          (4*(4096*M.size+(seed i).size)+6) := by
            unfold stagePowerTime
            grw [dimensionTime_le,degree]
      _ ≤ _ := by change (seed i).size ≤ V at tail; nlinarith only [tail,h,square,cross,vpos]
  have total := List.sum_le_length_nsmul ((List.finRange 3).map (fun i => stagePowerTime M (seed i) (stageDegrees i)))
    (510000000*V) (fun _ hx => by obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx; exact each i)
  simp only [List.length_map,List.length_finRange,nsmul_eq_mul] at total
  change _ ≤ 1530000002*V
  omega

-- The version requiring a caller-supplied block count is in ee1e2f78.

end IntegerMultBounds.MathlibTM2.M6.BitNode
