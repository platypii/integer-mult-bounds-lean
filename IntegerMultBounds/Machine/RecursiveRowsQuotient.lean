import IntegerMultBounds.Machine.RecursiveChildQuotientsBound

/-! One fixed-role row quotient from the original six headers. The constant
is physically written and erased; the clean divider resets every private tape. -/
namespace IntegerMultBounds.Machine.RecursiveRowsQuotient
open RecursiveChildQuotients
variable {a : ℕ}
noncomputable section

private theorem placed_exact {s u t r cost : ℕ} {M : Program s r a}
    (e : Fin (s+u) ≃ Fin t) (v w : Tapes t a) (small small' : Tapes s a)
    (ha : Placement.active e v = small) (hf : Placement.active e w = small')
    (he : Placement.extra e v = Placement.extra e w)
    (hh : HoareTime M (fun x => x = small) (fun x => x = small') cost) :
    HoareTime (Placement.placed M e) (fun x => x = v) (fun x => x = w) cost := by
  apply (Placement.hoare_at hh e v ha).consequence (fun _ h => h) _ le_rfl
  rintro x ⟨y,rfl,rfl⟩
  rw [Placement.replace,he,← hf]
  exact Placement.view _ _

private theorem rows_hoare (hs : Fin 6 → List Bool) (ds rs : List Bool)
    (hh : HoareTime (BinaryDescriptorDivision.program a)
      (fun v => v = BinaryDescriptorDivision.input (hs 1) ds)
      (fun v => v = BinaryDescriptorDivision.output (hs 1) ds rs)
      (BinaryDescriptorDivision.cost (hs 1) ds)) :
    HoareTime (Placement.placed (BinaryDescriptorDivision.program a) rowsPlacement)
      (fun v => v = bank hs none none (some ds)) (fun v => v = bank hs none (some rs) (some ds))
      (BinaryDescriptorDivision.cost (hs 1) ds) := by
  apply placed_exact rowsPlacement _ _ _ _ _ _ _ hh
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def initializeProgram (n : ℕ) :=
  Placement.placed (RecursiveChildQuotientsConstant.program (a := a) n) (FiniteReturnStackAt.placement (0 : Fin 38))

private theorem initialize_hoare (n : ℕ) (hs : Fin 6 → List Bool) (bs rs : Option (List Bool)) :
    HoareTime (initializeProgram (a := a) n) (fun v => v = bank hs bs rs none)
      (fun v => v = bank hs bs rs (some (RecursiveChildQuotientsConstant.bits n))) (RecursiveChildQuotientsConstant.cost n) := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) n)
    (FiniteReturnStackAt.placement (0 : Fin 38)) (bank hs bs rs none) (by rw [FiniteReturnStackAt.active_bank]; rfl)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [bank,headerHead,headerTape]

private theorem erase_hoare (ds : List Bool) (hs : Fin 6 → List Bool) (bs rs : Option (List Bool)) :
    HoareTime (BinaryDescriptorCleanupList.oneProgram (a := a) (0 : Fin 38))
      (fun v => v = bank hs bs rs (some ds)) (fun v => v = bank hs bs rs none) (2*ds.length+4) := by
  have h := BinaryDescriptorCleanupList.one_hoare (a := a) (0 : Fin 38) (bank hs bs rs (some ds)) ds rfl rfl
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [bank,headerHead,headerTape]

def program (roles : ℕ) :=
  seq (seq (initializeProgram (a := a) roles)
    (Placement.placed (BinaryDescriptorDivision.program a) rowsPlacement))
    (BinaryDescriptorCleanupList.oneProgram (0 : Fin 38))

def cost (roles : ℕ) (hs : Fin 6 → List Bool) :=
  BinaryDescriptorDivision.cost (hs 1) (RecursiveChildQuotientsConstant.bits roles)+
  5*(RecursiveChildQuotientsConstant.bits roles).length+12

theorem quotient_hoare (roles : ℕ) (hr : 0 < roles) (hs : Fin 6 → List Bool) :
    ∃ rs : List Bool, GrowingCounterData.Canonical rs ∧
      Counter.value rs = Counter.value (hs 1)/roles ∧ rs.length ≤ (hs 1).length ∧
      HoareTime (program (a := a) roles) (fun v => v = RecursiveChildQuotients.input hs)
        (fun v => v = bank hs none (some rs) none) (cost roles hs) := by
  obtain ⟨rs,hrc,hrv,hrlen,hr'⟩ := BinaryDescriptorDivision.divide_hoare (a := a) (hs 1)
    (RecursiveChildQuotientsConstant.bits roles)
    (by rw [RecursiveChildQuotientsConstant.bits_value]; exact hr)
  rw [RecursiveChildQuotientsConstant.bits_value] at hrv
  have h := ((initialize_hoare roles hs none none).seq (rows_hoare hs _ rs hr')).seq
    (erase_hoare _ hs none (some rs))
  refine ⟨rs,hrc,hrv,hrlen,h.consequence (fun _ h => h) (fun _ h => h) ?_⟩
  unfold cost RecursiveChildQuotientsConstant.cost
  omega

def constant (roles : ℕ) := 389*(RecursiveChildQuotientsConstant.bits roles).length+3154

theorem cost_linear (roles : ℕ) (hs : Fin 6 → List Bool) (V : ℕ) (hV : 0 < V)
    (hcanon : GrowingCounterData.Canonical (hs 1)) (hrows : Counter.value (hs 1) ≤ V) :
    cost roles hs ≤ constant roles*V := by
  have hlen : (hs 1).length ≤ 1*(Nat.log2 V+1) := by
    have hw := GrowingCounterData.canonical_width _ hcanon
    have hl : Nat.log2 (Counter.value (hs 1)) ≤ Nat.log2 V := by
      simpa only [Nat.log2_eq_log_two] using (Nat.log_mono_right (b := 2) hrows)
    omega
  have hd := RecursiveChildQuotientsBound.fixed_divisor_cost (hs 1)
    (RecursiveChildQuotientsConstant.bits roles) 1 V hV hlen
  have hc := Nat.le_mul_of_pos_right (5*(RecursiveChildQuotientsConstant.bits roles).length+12) hV
  unfold cost constant
  nlinarith

end
end IntegerMultBounds.Machine.RecursiveRowsQuotient
