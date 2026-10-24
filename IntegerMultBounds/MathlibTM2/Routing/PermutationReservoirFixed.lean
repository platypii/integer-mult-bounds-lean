module

public import IntegerMultBounds.MathlibTM2.Routing.PermutationReservoirTable

/-! A concrete bank for permutation decomposition and reservoir localization.
Only dimension, reservoir width, borrowed span and the original permutation table
are inputs; both carry tapes may be arbitrary. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
variable {Q A : ℕ} {P U : Type}

def permutationReservoirFixedSlot (j : Fin 10) : Fin 98 := ⟨78 + j.val, by have := j.isLt; omega⟩
def permutationReservoirProducerSlot : Fin 78 → Fin 98 := Fin.castLE (by decide)
theorem permutationReservoirFixedSlot_injective : Function.Injective permutationReservoirFixedSlot := by
  intro i j h
  apply Fin.ext
  have := congrArg (fun k : Fin 98 => k.val) h
  dsimp only [permutationReservoirFixedSlot] at this
  omega
theorem permutationReservoirProducerSlot_injective : Function.Injective permutationReservoirProducerSlot := by decide +kernel

def permutationReservoirFixedProgram (second : Bool) (k : Fin 3) : Pr P 98 Q A U :=
  permutationReservoirTableProgram second permutationReservoirFixedSlot 57
    88 89 90 91 92 93 94 52 95 96 97 permutationReservoirProducerSlot k

theorem permutationReservoirFixed_exec (body : P → Pr P 98 Q A U)
    (n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3)
    (second : Bool) (L : ℕ) (hn : n < 2 ^ L) (f : Equiv.Perm (Fin n))
    (v : HS 98 Q A U) (S : Stacks 98 A)
    (hdimension : S.R 57 = binSyms L n) (hreservoir : S.R 58 = binSyms L H)
    (hspan : S.R 59 = binSyms L w)
    (htable : S.R 85 = matchingEntryWords L (matchingTableEntries n (matchingMateCoordinate f)))
    (hblank : ∀ j : Fin 98, j ≠ 57 → j ≠ 58 → j ≠ 59 → j ≠ 70 → j ≠ 85 → j ≠ 84 → S.R j = []) :
    let mate := reservoirClassLocalMatching n H hfit w hw k (permutationMatchingCoordinate second f)
      (permutationMatchingCoordinate_involutive second f)
    ∃ (v' : HS 98 Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ permutationMatchingTableBinaryCost n L + reservoirClassLocalTableCost n w L +
        682 * L + 765 + 2 * (n * (2 * L + 2)) + 2 ∧
      Exec body (permutationReservoirFixedProgram second k) (mk v S) m
        (mk v' { S with R := (Function.update S.R 34
          (matchingEntryWords L (matchingTableEntries (n - 3 * w) (matchingMateCoordinate mate)))) }) := by
  apply permutationReservoirTable_exec body n second permutationReservoirFixedSlot
    permutationReservoirFixedSlot_injective 57 88 89 90 91 92 93 94 52 95 96 97
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    L hn f v S hdimension
    (hblank 80 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by intro j hj; fin_cases j <;> simp_all [permutationReservoirFixedSlot])
    htable
    (hblank 91 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hblank 96 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hblank 89 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hblank 90 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hblank 86 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hblank 88 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hblank 92 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hblank 93 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hblank 94 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hblank 52 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hblank 95 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hblank 97 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    permutationReservoirProducerSlot permutationReservoirProducerSlot_injective rfl H hfit w hw k
    hdimension hreservoir hspan
  intro j h57 h58 h59 h70 h52
  apply hblank
  · exact fun h => h57 (Fin.ext (congrArg (fun x : Fin 98 => x.val) h))
  · exact fun h => h58 (Fin.ext (congrArg (fun x : Fin 98 => x.val) h))
  · exact fun h => h59 (Fin.ext (congrArg (fun x : Fin 98 => x.val) h))
  · exact fun h => h70 (Fin.ext (congrArg (fun x : Fin 98 => x.val) h))
  · intro h; have := j.isLt; have := congrArg (fun x : Fin 98 => x.val) h; simp [permutationReservoirProducerSlot] at this; omega
  · intro h; have := j.isLt; have := congrArg (fun x : Fin 98 => x.val) h; simp [permutationReservoirProducerSlot] at this; omega

end IntegerMultBounds.MathlibTM2.Routing
