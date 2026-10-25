module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateOriginControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchInputBank

/-! Ordinary natural-group input has no origin packets or batch-count header.
The controller constructs the exact closed-batch input, preserving raw RHS and
borrowed suffixes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- The empty packet/count fields of the ordinary parameter bank. -/
def naturalGroupInputBank {A : ℕ} (P N q l s t u band L : ℕ)
    (rhs borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 117 A :=
  batchInputBank P N q l s t u band L 0 (fun _ => 0) rhs borrowed outTail inp out

theorem naturalGroupInputBank_controls {A s : ℕ} [NeZero s] (P N q l t u band L : ℕ)
    (rhs borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let S := naturalGroupInputBank P N q l s t u band L rhs borrowed outTail inp out
    { S with R := originControlsR A (weightWorkspaceWidth P q (2*q+8) t u) s t band L S.R } =
      batchInputBank P N q l s t u band L (naturalLengthGroup s t band L).length
        (fun n => (naturalGroupOrigin s t band L n).val) rhs borrowed outTail inp out := by
  dsimp only
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases h109 : k = 109
    · subst k
      simp [originControlsR, naturalGroupInputBank, batchInputBank, naturalOriginPackets_eq_rows]
    by_cases h116 : k = 116
    · subst k; simp [originControlsR, batchInputBank]
    simp [originControlsR, h109, h116, naturalGroupInputBank, batchInputBank,
      show k.val ≠ 109 from fun he => h109 (Fin.ext he),
      show k.val ≠ 116 from fun he => h116 (Fin.ext he)]

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem naturalGroupInputBank_exec (P N q l s t u band L : ℕ) [NeZero s]
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hband : band ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (rhs borrowed outTail : List (Fin (A+4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    ∃ v' m, v'.user = v.user ∧ m ≤ generateOriginControlsCost P q s t u band L ∧
      Exec body generateOriginControls
        (mk v (naturalGroupInputBank P N q l s t u band L rhs borrowed outTail inp out)) m
        (mk v' (batchInputBank P N q l s t u band L (naturalLengthGroup s t band L).length
          (fun n => (naturalGroupOrigin s t band L n).val) rhs borrowed outTail inp out)) := by
  obtain ⟨v', m, hu', hm, he⟩ := generateOriginControls_exec (body := body) P q s t u band L
    hP hs hst hu hband hL hLs hA v (naturalGroupInputBank P N q l s t u band L rhs borrowed outTail inp out)
    (by simp [naturalGroupInputBank, batchInputBank]) (by simp [naturalGroupInputBank, batchInputBank])
    (by simp [naturalGroupInputBank, batchInputBank]) (by simp [naturalGroupInputBank, batchInputBank])
    (by simp [naturalGroupInputBank, batchInputBank]) (by simp [naturalGroupInputBank, batchInputBank])
    (by simp [naturalGroupInputBank, batchInputBank]) (by
      intro k hk
      have hn (n : ℕ) (hn : 31 ≤ n) : k.val ≠ n := by omega
      simp [naturalGroupInputBank, batchInputBank, hn 101 (by decide), hn 102 (by decide),
        hn 103 (by decide), hn 97 (by decide), hn 98 (by decide), hn 99 (by decide),
        hn 100 (by decide), hn 109 (by decide), hn 112 (by decide), hn 114 (by decide),
        hn 116 (by decide), hn 110 (by decide), hn 93 (by decide)]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp [naturalGroupInputBank, batchInputBank])
  exact ⟨v', m, hu', hm, by simpa only [naturalGroupInputBank_controls] using he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
