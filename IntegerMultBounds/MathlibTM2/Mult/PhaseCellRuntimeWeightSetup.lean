module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedWeightSetup

/-! Generate the runtime word width, build ordered weights and release the owned
coordinate header and width source before inverse-generator setup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def runtimeWeightSetup : Pr P₀ 117 Q A U :=
  .seq (umul 2 112 94 104) (.seq (.act (pushN 94 (fun _ => tick) 8 .done))
    (.seq packedWeightSetup (.seq (uclear 94) (uclear 111))))

def runtimeWeightSetupCost (P s t u q L lo : ℕ) : ℕ :=
  (4 * q + 5) + packedWeightSetupCost P s t u q L lo (2 * q + 8) +
    (2 * (2 * q + 8) + 2) + (2 * lo + 2)

def runtimeWeightBank {A : ℕ} (S : Stacks 117 A) (P s t u q L lo : ℕ) : Stacks 117 A :=
  { S with R := (fun k => if k.val < 63 then [] else if k = 110 then
    weightPage A (2 * q + 8) q P s t u lo L ++ S.R 110 else if k = 111 then [] else S.R k) }

theorem runtimeWeightSetup_exec (P s t u q L lo : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hP' : (S.R 114).length = P) (hs' : (S.R 97).length = s) (ht' : (S.R 98).length = t)
    (hu' : (S.R 99).length = u) (hq : (S.R 112).length = q)
    (hL' : (S.R 102).length = L) (hcount : (S.R 103).length = L) (hlo' : (S.R 111).length = lo)
    (hblank : ∀ r, S.R (coefficientReg r) = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 96, 104, 105, 106, 108, 115], S.R k = [])
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hlo : lo < s) (hL : L ≤ s) :
    ∃ v' m, v'.user = v.user ∧ m ≤ runtimeWeightSetupCost P s t u q L lo ∧
      Exec body runtimeWeightSetup (mk v S) m (mk v' (runtimeWeightBank S P s t u q L lo)) := by
  let w := 2 * q + 8
  obtain ⟨v₁, hu₁, he₁⟩ := umul_exec (body := body) 2 (a := 112) (b := 94) (t := 104)
    (by decide) (by decide) (by decide) v S (hfresh 104 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 94 (List.replicate (2 * q) tick) }
  have he₁' : Exec body (umul 2 112 94 104) (mk v S) (4 * q + 4) (mk v₁ S₁) := by
    simpa [S₁, hq, hfresh 94 (by simp)] using he₁
  let S₂ : Stacks 117 A := { S with R := Function.update S.R 94 (List.replicate w tick) }
  have he₂ : Exec body (.act (pushN 94 (fun _ => tick) 8 .done)) (mk v₁ S₁) 1 (mk v₁ S₂) := by
    have he := Exec.act (body := body) (pushN 94 (fun _ => tick) 8 .done) (mk v₁ S₁)
    rw [pushN_run] at he
    simpa only [S₂, S₁, Action.run, Function.update_self, Function.update_idem, List.replicate_append_replicate,
      show 8 + 2 * q = w by dsimp [w]; omega] using he
  have hblank₂ : ∀ r, S₂.R (coefficientReg r) = [] := by
    intro r
    have hn : coefficientReg r ≠ (94 : Fin 117) := by
      intro he; have hr := coefficientReg_range r; rw [he] at hr; omega
    simpa [S₂, hn] using hblank r
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := packedWeightSetup_exec (body := body) P s t u q L lo w v₁ S₂
    (by simpa [S₂] using hP') (by simpa [S₂] using hs') (by simpa [S₂] using ht')
    (by simpa [S₂] using hu') (by simpa [S₂] using hq) (by simpa [S₂] using hL')
    (by simpa [S₂] using hcount) (by simpa [S₂] using hlo') (by simp [S₂]) hblank₂ (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [S₂] using hfresh _ (by simp))
    hP hs hst hu hlo hL
  let B : Stacks 117 A := { S₂ with R := (fun k => if k.val < 63 then [] else if k = 110 then
    weightPage A w q P s t u lo L ++ S₂.R 110 else S₂.R k) }
  obtain ⟨v₄, hu₄, he₄⟩ := uclear_exec body 94 v₃ B
  let C : Stacks 117 A := { B with R := Function.update B.R 94 [] }
  obtain ⟨v₅, hu₅, he₅⟩ := uclear_exec body 111 v₄ C
  have h94 : (B.R 94).length = w := by simp [B, S₂]
  have h111 : (C.R 111).length = lo := by simpa [C, B, S₂] using hlo'
  refine ⟨v₅, (4 * q + 4) + (1 + (m₃ + ((2 * w + 2) + (2 * lo + 2)))),
    hu₅.trans (hu₄.trans (hu₃.trans hu₁)), by unfold runtimeWeightSetupCost; dsimp only [w] at *; omega,
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast (by rw [h94, h111]) ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases hk94 : k = 94
    · subst k; simp [runtimeWeightBank, C, B, S₂, hfresh 94 (by simp)]
    by_cases hk111 : k = 111
    · subst k; simp [runtimeWeightBank, C, B, S₂]
    simp [runtimeWeightBank, C, B, S₂, hk94, hk111, w]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
