module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryZeroTest
public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactPattern

/-! A live row-count test skips empty descriptor tables. The positive-width
backend is supplied as a proved program contract; its scratch bank is unchanged
by the test. Shared-bank jobs can therefore use the same backend readiness. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable {T Q A : ℕ} {P U : Type}

noncomputable section

theorem repairDescriptorWord_nil (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (key : RepairDescriptorKey)
    (hrows : repairCompactRows p key = 0) : repairDescriptorWord (A := A) p X hG hK active s key = [] := by
  have hi : List.ofFn (patternIndex (repairCompactPattern p X hG hK active s key)) = [] :=
    List.length_eq_zero_iff.mp (by simpa only [List.length_ofFn] using hrows)
  rw [← repairCompactPattern_word p X hG hK active s key, patternTable, sourceTable, hi]
  rfl

def repairDescriptorGuardProgram (rows zero tx ty tz cy : Fin T) (compile : Pr P T Q A U) : Pr P T Q A U :=
  .seq (binaryZeroTestProgram rows zero tx ty tz cy)
    (.cond (fun v => symBit (v.scan cy)) (.act .done) compile)

theorem repairDescriptorGuard_exec (body : P → Pr P T Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (key : RepairDescriptorKey)
    (rows zero tx ty tz cy out : Fin T) (hregs : [rows, zero, tx, ty, tz].Nodup)
    (hcrows : cy ≠ rows) (hczero : cy ≠ zero)
    (L budget : ℕ) (hfit : repairCompactRows p key < 2 ^ L)
    (compile : Pr P T Q A U) (v : HS T Q A U) (S : Stacks T A)
    (hrows : S.R rows = binSyms L (repairCompactRows p key))
    (hzero : S.R zero = []) (htx : S.R tx = []) (hty : S.R ty = []) (htz : S.R tz = [])
    (hcompile : ∀ w : HS T Q A U, 0 < repairCompactRows p key →
      ∃ (w' : HS T Q A U) (steps : ℕ), w'.user = w.user ∧ steps ≤ budget ∧
        Exec body compile (mk w S) steps (mk w' { S with R := Function.update S.R out (repairDescriptorWord p X hG hK active s key ++ S.R out) })) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ 14 * L + 16 + budget ∧
      Exec body (repairDescriptorGuardProgram rows zero tx ty tz cy compile) (mk v S) steps
        (mk v' { S with R := Function.update S.R out (repairDescriptorWord p X hG hK active s key ++ S.R out) }) := by
  obtain ⟨v₁, hu₁, hc₁, he₁⟩ := binaryZeroTest_exec body rows zero tx ty tz cy hregs hcrows hczero
    L (repairCompactRows p key) hfit v S hrows hzero htx hty htz
  by_cases hz : repairCompactRows p key = 0
  · have hw := repairDescriptorWord_nil (A := A) p X hG hK active s key hz
    have hf : Function.update S.R out (repairDescriptorWord p X hG hK active s key ++ S.R out) = S.R := by
      rw [hw, List.nil_append]
      funext r
      by_cases hr : r = out <;> simp_all
    refine ⟨v₁, (14 * L + 14) + (1 + 1), hu₁, by omega, ?_⟩
    rw [hf]
    exact Exec.seq he₁ (Exec.cond_true (f := fun v => symBit (v.scan cy))
      (by simp [hc₁, hz]) (Exec.act (body := body) .done (mk v₁ S)))
  · obtain ⟨v₂, n₂, hu₂, ht₂, he₂⟩ := hcompile v₁ (by omega)
    refine ⟨v₂, (14 * L + 14) + (n₂ + 1), hu₂.trans hu₁, by omega, ?_⟩
    exact Exec.seq he₁ (Exec.cond_false (f := fun v => symBit (v.scan cy)) (by simp [hc₁, hz]) he₂)

end
end IntegerMultBounds.MathlibTM2.Routing
