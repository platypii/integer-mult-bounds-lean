module

public import IntegerMultBounds.MathlibTM2.Cover.LabelSplit
public import IntegerMultBounds.Machine.RadixCounterData

/-! Full label addresses in the directories of the two child streams. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelDirectory
noncomputable section

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open RadixCounterData RadixDigits Host Node

/-- The current label counts cyclically, once through the box for each spectator prefix. -/
def digits (m w j : ℕ) : List (Fin prime) :=
  advance prime_prime.two_le j (zeros prime_prime.two_le (w*(m*m)))

local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos w).ne'⟩

theorem value_at (m w p : ℕ) (g : LabelPadding.Label m w) :
    value (digits m w (p*(prime^w)^(m*m)+(LabelAddress.address g).val)) =
      (LabelAddress.address g).val := by
  unfold digits
  rw [advance_value,zeros_length,zeros_value,Nat.zero_add,pow_mul prime w (m*m),Nat.mul_add_mod_self_right,
    Nat.mod_eq_of_lt (LabelAddress.address g).isLt]

/-- Reading a whole atom from the directory recovers the original matrix coefficient. -/
theorem coefficient_at (m w p : ℕ) (g : LabelPadding.Label m w) (r c : Fin m) :
    value (digits m w (p*(prime^w)^(m*m)+(LabelAddress.address g).val)) /
      (prime^w)^FlatCoordinateLayout.suffixFields (finProdFinEquiv (c,r)) % (prime^w) =
        (g r c).val := by
  rw [value_at, LabelAddress.entry]

/-- Keep the frozen ancestor labels in front of the new label. -/
def entry (ancestor : ℕ → List (Fin (prime+4))) (m w j : ℕ) :=
  ancestor j ++ (digits m w j).map digitSymbol

theorem entry_length (ancestor : ℕ → List (Fin (prime+4))) (m w j : ℕ) :
    (entry ancestor m w j).length = (ancestor j).length+w*(m*m) := by simp [entry,digits]

variable {T Q : ℕ} {P U : Type} {body : P → Pr P T Q prime U}

/-- The retained class mask orders full prefix entries exactly as it orders the child payloads. -/
theorem split_exec {src mask width symbols ts tm acc out : Fin T}
    (hr : [src,mask,width,symbols,ts,tm,acc,out].Nodup)
    (xs : List ℕ) (m w a : ℕ) (branch : Matrix (Fin m) (Fin m) (ZMod prime) → Bool)
    (ancestor : ℕ → List (Fin (prime+4))) (ha : ∀ j ∈ xs, (ancestor j).length = a)
    (u : HS T Q prime U) (S : Stacks T prime) (tail : List (Fin (prime+4))) :
    let keep := fun j => branch (LabelStock.residue m w 1 j)
    let word := entry ancestor m w
    let W := a+w*(m*m)
    S.R src = xs.flatMap word ++ tail → S.R mask = (xs.map keep).map bitSymbol →
    (S.R width).length = W → (∀ k ∈ [symbols,ts,tm,acc], S.R k = []) →
    ∃ u' n, u'.user = u.user ∧ n ≤ 2*(xs.length*(16*W+10)+16) ∧
      Exec body (LabelSplit.program src mask width symbols ts tm acc out) (mk u S) n
        (mk u' {S with R := Function.update S.R out ((xs.filter keep).flatMap word ++
          (xs.filter (fun j => !(keep j))).flatMap word ++ S.R out)}) := by
  intro keep word W hs hm hw hf
  exact LabelSplit.split_exec hr xs keep word W
    (fun j hj => by simp [word,W,entry_length,ha j hj]) u S tail hs hm hw hf

end
end IntegerMultBounds.MathlibTM2.Cover.LabelDirectory
