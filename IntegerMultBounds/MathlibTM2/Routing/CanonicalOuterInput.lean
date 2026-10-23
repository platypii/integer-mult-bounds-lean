module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalLiveInput
public import IntegerMultBounds.MathlibTM2.Routing.InactiveClassifierBank

/-! Construct the header, width and classifier extensions of the canonical live
bank. Only dimension operands are supplied; all generator scratch starts empty. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {N A : ℕ}

def canonicalHeaderOperands (Lrow Lwidth R wc : ℕ) : HeaderWorkRole → List (Fin (A + 4))
  | .binary i => if i = 0 then binSyms Lrow R else binSyms Lwidth wc
  | _ => []

def canonicalHeaderInputBank (core : Fin N → List (Fin (A + 4))) (Lrow Lwidth R wc : ℕ) :
    Fin (sharedHeaderT N) → List (Fin (A + 4)) :=
  Fin.addCases core (fun i => canonicalHeaderOperands Lrow Lwidth R wc ((Fintype.equivFin HeaderWorkRole).symm i))

theorem canonicalHeaderInputBank_core (core : Fin N → List (Fin (A + 4))) (Lrow Lwidth R wc : ℕ) (j : Fin N) :
    canonicalHeaderInputBank core Lrow Lwidth R wc (sharedHeaderCore j) = core j := by
  change Fin.addCases (motive := fun _ => List (Fin (A + 4))) core
    (fun i : Fin (Fintype.card HeaderWorkRole) => canonicalHeaderOperands Lrow Lwidth R wc ((Fintype.equivFin HeaderWorkRole).symm i))
    (Fin.castAdd _ j) = core j
  rw [Fin.addCases_left]

theorem canonicalHeaderInputBank_work (core : Fin N → List (Fin (A + 4))) (Lrow Lwidth R wc : ℕ) (r : HeaderWorkRole) :
    canonicalHeaderInputBank core Lrow Lwidth R wc (sharedHeaderWork r) = canonicalHeaderOperands Lrow Lwidth R wc r := by
  change Fin.addCases (motive := fun _ => List (Fin (A + 4))) core
    (fun i : Fin (Fintype.card HeaderWorkRole) => canonicalHeaderOperands Lrow Lwidth R wc ((Fintype.equivFin HeaderWorkRole).symm i))
    (Fin.natAdd N (Fintype.equivFin HeaderWorkRole r)) = _
  rw [Fin.addCases_right, Equiv.symm_apply_apply]

theorem canonicalHeaderInputBank_blank (core : Fin N → List (Fin (A + 4))) (Lrow Lwidth R wc : ℕ)
    (r : HeaderWorkRole) (hr : ∀ i, r ≠ .binary i) :
    canonicalHeaderInputBank core Lrow Lwidth R wc (sharedHeaderWork r) = [] := by
  rw [canonicalHeaderInputBank_work]
  cases r <;> first | rfl | exact (hr _ rfl).elim

def canonicalWidthInputBank (core : Fin N → List (Fin (A + 4))) (Lr Lm rb wy : ℕ) :
    Fin (N + 6) → List (Fin (A + 4)) :=
  Fin.addCases core (fun i => if i = 0 then binSyms Lr rb else if i = 1 then binSyms Lm wy else [])

theorem canonicalWidthInputBank_core (core : Fin N → List (Fin (A + 4))) (Lr Lm rb wy : ℕ) (j : Fin N) :
    canonicalWidthInputBank core Lr Lm rb wy (fieldCore j) = core j := by
  change Fin.addCases (motive := fun _ => List (Fin (A + 4))) core (fun i : Fin 6 => if i = 0 then binSyms Lr rb else if i = 1 then binSyms Lm wy else [])
    (Fin.castAdd 6 j) = core j
  rw [Fin.addCases_left]

theorem canonicalWidthInputBank_aux (core : Fin N → List (Fin (A + 4))) (Lr Lm rb wy : ℕ) (j : Fin 6) :
    canonicalWidthInputBank core Lr Lm rb wy (fieldAux j) =
      if j = 0 then binSyms Lr rb else if j = 1 then binSyms Lm wy else [] := by
  change Fin.addCases (motive := fun _ => List (Fin (A + 4))) core (fun i : Fin 6 => if i = 0 then binSyms Lr rb else if i = 1 then binSyms Lm wy else [])
    (Fin.natAdd N j) = _
  rw [Fin.addCases_right]

def canonicalClassifierOperands (p : Par) (LK Ln Lo Lt : ℕ) (j : Fin 16) : List (Fin (A + 4)) :=
  if j = 0 then binSyms LK p.K
  else if j = 1 then binSyms LK p.G
  else if j = 10 then binSyms Ln p.n
  else if j = 13 then binSyms Lo (p.ρ + 1)
  else if j = 14 then binSyms Lo p.ρ
  else if j = 15 then binSyms Lt p.m
  else []

def canonicalClassifierInputBank (core : Fin N → List (Fin (A + 4))) (p : Par) (LK Ln Lo Lt : ℕ) :
    Fin (N + 16) → List (Fin (A + 4)) := Fin.addCases core (canonicalClassifierOperands p LK Ln Lo Lt)

theorem canonicalClassifierInputBank_core (core : Fin N → List (Fin (A + 4))) (p : Par) (LK Ln Lo Lt : ℕ) (j : Fin N) :
    canonicalClassifierInputBank core p LK Ln Lo Lt (classifierCore j) = core j := by
  change Fin.addCases (motive := fun _ => List (Fin (A + 4))) core (canonicalClassifierOperands p LK Ln Lo Lt) (Fin.castAdd 16 j) = core j
  rw [Fin.addCases_left]

theorem canonicalClassifierInputBank_aux (core : Fin N → List (Fin (A + 4))) (p : Par) (LK Ln Lo Lt : ℕ) (j : Fin 16) :
    canonicalClassifierInputBank core p LK Ln Lo Lt (classifierAux j) = canonicalClassifierOperands p LK Ln Lo Lt j := by
  change Fin.addCases (motive := fun _ => List (Fin (A + 4))) core (canonicalClassifierOperands p LK Ln Lo Lt) (Fin.natAdd N j) = _
  rw [Fin.addCases_right]

theorem canonicalClassifierInputBank_scratch (core : Fin N → List (Fin (A + 4))) (p : Par) (LK Ln Lo Lt : ℕ)
    (j : Fin 16) (hlo : 2 ≤ j.val) (h10 : j.val ≠ 10) (hhi : j.val < 13) :
    canonicalClassifierInputBank core p LK Ln Lo Lt (classifierAux j) = [] := by
  rw [canonicalClassifierInputBank_aux]
  have h0 : j ≠ 0 := by intro h; subst j; norm_num at hlo
  have h1 : j ≠ 1 := by intro h; subst j; norm_num at hlo
  have hn10 : j ≠ 10 := by intro h; subst j; exact h10 rfl
  have h13 : j ≠ 13 := by intro h; subst j; norm_num at hhi
  have h14 : j ≠ 14 := by intro h; subst j; norm_num at hhi
  have h15 : j ≠ 15 := by intro h; subst j; norm_num at hhi
  simp only [canonicalClassifierOperands, ite_eq_right h0, ite_eq_right h1,
    ite_eq_right hn10, ite_eq_right h13, ite_eq_right h14, ite_eq_right h15]

def canonicalHeaderInputStack (S : Stacks N A) (Lrow Lwidth R wc : ℕ) : Stacks (sharedHeaderT N) A :=
  ⟨S.inp, S.out, Fin.addCases S.L (fun _ => []), canonicalHeaderInputBank S.R Lrow Lwidth R wc⟩

theorem canonicalHeaderInputStack_project (S : Stacks N A) (Lrow Lwidth R wc : ℕ) :
    embStk sharedHeaderCore (canonicalHeaderInputStack S Lrow Lwidth R wc) = S := by
  have hL : (embStk sharedHeaderCore (canonicalHeaderInputStack S Lrow Lwidth R wc)).L = S.L := by
    funext j
    change Fin.addCases (motive := fun _ => List (Fin (A + 4))) S.L
      (fun _ : Fin (Fintype.card HeaderWorkRole) => []) (Fin.castAdd _ j) = S.L j
    rw [Fin.addCases_left]
  have hR : (embStk sharedHeaderCore (canonicalHeaderInputStack S Lrow Lwidth R wc)).R = S.R := by
    funext j
    exact canonicalHeaderInputBank_core S.R Lrow Lwidth R wc j
  exact congrArg₂ (fun L R => (⟨S.inp, S.out, L, R⟩ : Stacks N A)) hL hR

def canonicalWidthInputStack (S : Stacks N A) (Lr Lm rb wy : ℕ) : Stacks (N + 6) A :=
  ⟨S.inp, S.out, Fin.addCases S.L (fun _ => []), canonicalWidthInputBank S.R Lr Lm rb wy⟩

theorem canonicalWidthInputStack_project (S : Stacks N A) (Lr Lm rb wy : ℕ) :
    embStk fieldCore (canonicalWidthInputStack S Lr Lm rb wy) = S := by
  have hL : (embStk fieldCore (canonicalWidthInputStack S Lr Lm rb wy)).L = S.L := by
    funext j
    change Fin.addCases (motive := fun _ => List (Fin (A + 4))) S.L
      (fun _ : Fin 6 => []) (Fin.castAdd 6 j) = S.L j
    rw [Fin.addCases_left]
  have hR : (embStk fieldCore (canonicalWidthInputStack S Lr Lm rb wy)).R = S.R := by
    funext j
    exact canonicalWidthInputBank_core S.R Lr Lm rb wy j
  exact congrArg₂ (fun L R => (⟨S.inp, S.out, L, R⟩ : Stacks N A)) hL hR

def canonicalClassifierInputStack (S : Stacks N A) (p : Par) (LK Ln Lo Lt : ℕ) : Stacks (N + 16) A :=
  ⟨S.inp, S.out, Fin.addCases S.L (fun _ => []), canonicalClassifierInputBank S.R p LK Ln Lo Lt⟩

theorem canonicalClassifierInputStack_project (S : Stacks N A) (p : Par) (LK Ln Lo Lt : ℕ) :
    embStk classifierCore (canonicalClassifierInputStack S p LK Ln Lo Lt) = S := by
  have hL : (embStk classifierCore (canonicalClassifierInputStack S p LK Ln Lo Lt)).L = S.L := by
    funext j
    change Fin.addCases (motive := fun _ => List (Fin (A + 4))) S.L
      (fun _ : Fin 16 => []) (Fin.castAdd 16 j) = S.L j
    rw [Fin.addCases_left]
  have hR : (embStk classifierCore (canonicalClassifierInputStack S p LK Ln Lo Lt)).R = S.R := by
    funext j
    exact canonicalClassifierInputBank_core S.R p LK Ln Lo Lt j
  exact congrArg₂ (fun L R => (⟨S.inp, S.out, L, R⟩ : Stacks N A)) hL hR

theorem canonicalHeaderInputStack_left (S : Stacks N A) (Lrow Lwidth R wc : ℕ)
    (hL : ∀ j, S.L j = []) : ∀ j, (canonicalHeaderInputStack S Lrow Lwidth R wc).L j = [] := by
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · change Fin.addCases S.L (fun _ : Fin (Fintype.card HeaderWorkRole) => []) (Fin.castAdd _ i) = []
    rw [Fin.addCases_left]
    exact hL i
  · change Fin.addCases S.L (fun _ : Fin (Fintype.card HeaderWorkRole) => []) (Fin.natAdd N i) = []
    rw [Fin.addCases_right]

theorem canonicalWidthInputStack_left (S : Stacks N A) (Lr Lm rb wy : ℕ)
    (hL : ∀ j, S.L j = []) : ∀ j, (canonicalWidthInputStack S Lr Lm rb wy).L j = [] := by
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · change Fin.addCases S.L (fun _ : Fin 6 => []) (Fin.castAdd 6 i) = []
    rw [Fin.addCases_left]
    exact hL i
  · change Fin.addCases S.L (fun _ : Fin 6 => []) (Fin.natAdd N i) = []
    rw [Fin.addCases_right]

theorem canonicalClassifierInputStack_left (S : Stacks N A) (p : Par) (LK Ln Lo Lt : ℕ)
    (hL : ∀ j, S.L j = []) : ∀ j, (canonicalClassifierInputStack S p LK Ln Lo Lt).L j = [] := by
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · change Fin.addCases S.L (fun _ : Fin 16 => []) (Fin.castAdd 16 i) = []
    rw [Fin.addCases_left]
    exact hL i
  · change Fin.addCases S.L (fun _ : Fin 16 => []) (Fin.natAdd N i) = []
    rw [Fin.addCases_right]


/-- Canonical scalar operands leave room for the framing delimiter. -/
theorem canonicalScalarWord_small (L v : ℕ) :
    ∀ x ∈ (binSyms L v : List (Fin (A + 4))), x.val < 8 := by
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  simp only [bitSymbol]
  split <;> omega

theorem canonicalHeaderInputBank_small (core : Fin N → List (Fin (A + 4)))
    (Lrow Lwidth R wc : ℕ) (hcore : ∀ j, ∀ x ∈ core j, x.val < 8) :
    ∀ j, ∀ x ∈ canonicalHeaderInputBank core Lrow Lwidth R wc j, x.val < 8 := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simpa only [canonicalHeaderInputBank, Fin.addCases_left] using hcore i
  · intro i
    simp only [canonicalHeaderInputBank, Fin.addCases_right]
    generalize (Fintype.equivFin HeaderWorkRole).symm i = r
    cases r <;> simp only [canonicalHeaderOperands]
    all_goals first | (split <;> exact canonicalScalarWord_small _ _) | simp

theorem canonicalWidthInputBank_small (core : Fin N → List (Fin (A + 4)))
    (Lr Lm rb wy : ℕ) (hcore : ∀ j, ∀ x ∈ core j, x.val < 8) :
    ∀ j, ∀ x ∈ canonicalWidthInputBank core Lr Lm rb wy j, x.val < 8 := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simpa only [canonicalWidthInputBank, Fin.addCases_left] using hcore i
  · intro i
    simp only [canonicalWidthInputBank, Fin.addCases_right]
    change ∀ x ∈ (if i = 0 then binSyms Lr rb else if i = 1 then binSyms Lm wy else []), x.val < 8
    split
    · exact canonicalScalarWord_small _ _
    · split
      · exact canonicalScalarWord_small _ _
      · simp


theorem canonicalClassifierInputBank_small (core : Fin N → List (Fin (A + 4)))
    (p : Par) (LK Ln Lo Lt : ℕ) (hcore : ∀ j, ∀ x ∈ core j, x.val < 8) :
    ∀ j, ∀ x ∈ canonicalClassifierInputBank core p LK Ln Lo Lt j, x.val < 8 := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simpa only [canonicalClassifierInputBank, Fin.addCases_left] using hcore i
  · intro i
    simp only [canonicalClassifierInputBank, Fin.addCases_right, canonicalClassifierOperands]
    repeat' first | (split) | exact canonicalScalarWord_small _ _ | simp


theorem canonicalDescriptorOperands_small (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (source : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)
    (r : LiveDescriptorRole 11) :
    ∀ x ∈ (canonicalDescriptorOperands p X hG hK active source w r : List (Fin (A + 4))), x.val < 8 := by
  cases r <;> simp only [canonicalDescriptorOperands, liveDescriptorData]
  all_goals first
    | exact canonicalScalarWord_small _ _
    | simp
    | skip
  case profile r =>
    cases r
    all_goals first | exact canonicalScalarWord_small _ _ | simp | skip
    case coordinate r =>
      cases r
      all_goals first | exact canonicalScalarWord_small _ _ | simp | skip
      case arithmetic r =>
        cases r
        all_goals first | exact canonicalScalarWord_small _ _ | simp
  case coordinate r =>
    cases r
    all_goals first | exact canonicalScalarWord_small _ _ | simp

theorem canonicalLiveInputBank_small (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (source : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)
    (core : Fin repairT → List (Fin (A + 4))) (hcore : ∀ j, ∀ x ∈ core j, x.val < 8) :
    ∀ j, ∀ x ∈ canonicalLiveInputBank p X hG hK active source w core j, x.val < 8 := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp only [canonicalLiveInputBank, Fin.addCases_left]
    refine Fin.addCases ?_ ?_ i
    · intro q
      simpa only [liveDescriptorBank, Fin.addCases_left] using hcore q
    · intro q
      simp only [liveDescriptorBank, Fin.addCases_right]
      exact canonicalDescriptorOperands_small p X hG hK active source w _
  · intro i
    simp only [canonicalLiveInputBank, Fin.addCases_right]
    split
    · exact canonicalScalarWord_small _ _
    · simp


theorem canonicalRepairPayload_small (p : Par) (X rb wb wm wp wk R B : ℕ)
    (key : RepairSetupKey) :
    ∀ x ∈ (canonicalRepairPayload p X rb wb wm wp wk R B key : List (Fin (A + 4))), x.val < 8 := by
  cases key with
  | inl key =>
    cases key <;> simp only [canonicalRepairPayload]
    all_goals first | exact canonicalScalarWord_small _ _ | simp
  | inr key =>
    cases key <;> simp only [canonicalRepairPayload]
    all_goals first | exact canonicalScalarWord_small _ _ | simp

theorem canonicalRepairInput_small (p : Par) (X rb wb wm wp wk R B : ℕ)
    (records : List (Fin (A + 4))) (hrecords : ∀ x ∈ records, x.val < 8) :
    ∀ j, ∀ x ∈ canonicalRepairInput p X rb wb wm wp wk R B records j, x.val < 8 := by
  intro j
  by_cases hs : ∃ key, repairSetupSource key = j
  · obtain ⟨key, rfl⟩ := hs
    rw [canonicalRepairInput_source]
    exact canonicalRepairPayload_small p X rb wb wm wp wk R B key
  · unfold canonicalRepairInput
    rw [Function.extend_apply' _ _ _ hs]
    split
    · exact hrecords
    · simp

theorem canonicalProfileCoreBank_small (p : Par) (X rb wb wm wp wk R B : ℕ)
    (records coordinates : List (Fin (A + 4)))
    (hrecords : ∀ x ∈ records, x.val < 8) (hcoordinates : ∀ x ∈ coordinates, x.val < 8) :
    ∀ j, ∀ x ∈ canonicalProfileCoreBank p X rb wb wm wp wk R B records coordinates j, x.val < 8 := by
  intro j
  unfold canonicalProfileCoreBank
  by_cases hj : j = canonicalProfileKey
  · subst j
    rw [Function.update_self]
    exact hcoordinates
  · rw [Function.update_of_ne hj]
    exact canonicalRepairInput_small p X rb wb wm wp wk R B records hrecords j

end
end IntegerMultBounds.MathlibTM2.Routing
