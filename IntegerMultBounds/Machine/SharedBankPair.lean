import IntegerMultBounds.Machine.SharedBank

/-! Two concrete stages share a fixed common bank and retain separate private
metadata. The complete common bank is handed off on the same physical tapes. -/
namespace IntegerMultBounds.Machine.SharedBankPair
variable {k t u q r a : ℕ}

/-- Keep all k common tapes fixed while selecting the second metadata bank. -/
def placement (k t u : ℕ) : Fin ((k+u)+t) ≃ Fin ((k+t)+u) where
  toFun := Fin.addCases
    (Fin.addCases (fun i => Fin.castAdd u (Fin.castAdd t i)) (Fin.natAdd (k+t)))
    (fun i => Fin.castAdd u (Fin.natAdd k i))
  invFun := Fin.addCases
    (Fin.addCases (fun i => Fin.castAdd t (Fin.castAdd u i)) (Fin.natAdd (k+u)))
    (fun i => Fin.castAdd t (Fin.natAdd k i))
  left_inv := by
    intro i; induction i using Fin.addCases with
    | left i => induction i using Fin.addCases <;> simp
    | right i => simp
  right_inv := by
    intro i; induction i using Fin.addCases with
    | left i => induction i using Fin.addCases <;> simp
    | right i => simp

theorem active_bank (common : Tapes k a) (left : Tapes t a) (right : Tapes u a) :
    Placement.active (placement k t u) ((common.append left).append right) = common.append right := by
  unfold Placement.active placement Tapes.append
  congr 1 <;> funext i <;> induction i using Fin.addCases <;> simp

theorem extra_bank (common : Tapes k a) (left : Tapes t a) (right : Tapes u a) :
    Placement.extra (placement k t u) ((common.append left).append right) = left := by
  unfold Placement.extra placement Tapes.append
  congr 1 <;> funext i <;> simp

theorem combine_bank (common : Tapes k a) (left : Tapes t a) (right : Tapes u a) :
    Placement.combine (placement k t u) (common.append right) left = (common.append left).append right := by
  simpa only [active_bank,extra_bank] using Placement.view (placement k t u) ((common.append left).append right)

noncomputable def input (v : Tapes t a) (x : Tapes u a) (slots : Fin k → Fin t) (slots' : Fin k → Fin u) :=
  (SharedBank.bank v slots).append (SharedBank.strip x slots')

noncomputable def output (v : Tapes t a) (x : Tapes u a) (slots : Fin k → Fin t) (slots' : Fin k → Fin u) :=
  ((SharedBank.payload x slots').append (SharedBank.strip v slots)).append (SharedBank.strip x slots')

noncomputable def program (M : Program t q a) (N : Program u r a)
    (slots : Fin k → Fin t) (slots' : Fin k → Fin u) :=
  seq (extend (Placement.placed M (SharedBank.placement slots)) u)
    (Placement.placed (Placement.placed N (SharedBank.placement slots')) (placement k t u))

/-- Actual physical composition; the only extra transition is the real join. -/
theorem pair_hoare {M : Program t q a} {N : Program u r a} {v w : Tapes t a} {x y : Tapes u a}
    {m n : ℕ} (hM : HoareTime M (fun z => z = v) (fun z => z = w) m)
    (hN : HoareTime N (fun z => z = x) (fun z => z = y) n)
    (slots : Fin k → Fin t) (hinj : Function.Injective slots)
    (slots' : Fin k → Fin u) (hinj' : Function.Injective slots')
    (hcommon : SharedBank.payload w slots = SharedBank.payload x slots') :
    HoareTime (program M N slots slots')
      (fun z => z = input v x slots slots') (fun z => z = output w y slots slots') (m+n+1) := by
  have hm := FamilyPlacementAlphabet.extend_hoare (SharedBank.stage_hoare hM slots hinj) (SharedBank.strip x slots')
  have hn := SharedBank.stage_hoare hN slots' hinj'
  have ha : Placement.active (placement k t u) ((SharedBank.bank w slots).append (SharedBank.strip x slots')) =
      SharedBank.bank x slots' := by
    rw [SharedBank.bank,active_bank,hcommon]
    rfl
  have hh := Placement.hoare_at hn (placement k t u) ((SharedBank.bank w slots).append (SharedBank.strip x slots')) ha
  have hh' : HoareTime (Placement.placed (Placement.placed N (SharedBank.placement slots')) (placement k t u))
      (fun z => z = (SharedBank.bank w slots).append (SharedBank.strip x slots'))
      (fun z => z = output w y slots slots') n := by
    apply hh.consequence (fun _ h => h) ?_ le_rfl
    rintro z ⟨small,hsmall,rfl⟩
    subst small
    simp only [Placement.replace,SharedBank.bank,extra_bank,combine_bank,output]
  exact (hm.seq hh').consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.SharedBankPair
