module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalPlacementInput
public import IntegerMultBounds.MathlibTM2.Routing.GeneratedPlacedInput

/-! Build a complete generated/placed input from arithmetic bounds and records.
Every stack and readiness proof is constructed; there is no input bank premise
and no execution field. The procedure type is empty. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

structure CanonicalStageArithmetic (p : Par) where
  w : LiveDescriptorWidths
  rb : ℕ
  wb : ℕ
  wm : ℕ
  wp : ℕ
  wk : ℕ
  R : ℕ
  B : ℕ
  scale : ℕ
  Lrow : ℕ
  Lwidth : ℕ
  Lr : ℕ
  Lm : ℕ
  LK : ℕ
  Ln : ℕ
  Lo : ℕ
  Lt : ℕ
  Lcp : ℕ
  Lp : ℕ
  rowBits : List Bool
  hG : 0 < p.G
  hK : 0 < p.K
  hguard : p.G + 1 < p.K
  hscale : (0 : ℝ) < scale
  hn : (p.n : ℝ) ≤ scale
  hradix : 64 * (scale : ℝ) ^ 4 ≤ (2 : ℝ) ^ p.G
  hgap : 1024 * (scale : ℝ) ^ 4 ≤ (2 : ℝ) ^ (p.K - 1 - p.G)
  hwidth : w.selectorBits = w.coordinateBits
  hselectorWidthFit : w.coordinateBits < 2 ^ w.widthBits
  hkfit : p.K < 2 ^ w.strideBits
  hnfit : p.n < 2 ^ w.indexBits
  hwfit : p.wy + 2 * p.wc + 0 < 2 ^ w.coordinateBits
  hR : 0 < R
  hB : 1 ≤ B
  hrb : R ≤ 2 ^ rb
  hblock : fieldsLen (selectiveKeyLen p 0 rb) + B < 2 ^ wb
  hrecords : R * 2 ^ fieldsLen (selectiveLen p 0) < 2 ^ wm
  hpayload : B < 2 ^ wp
  hkey : fieldsLen (selectiveKeyLen p 0 rb) < 2 ^ wk
  hfit : ∀ j, LiveDescriptorBounds p 0 w (repairLiveMode j)
  hRfit : R < 2 ^ Lrow
  hwidthFit : p.wc < 2 ^ Lwidth
  hr : rb < 2 ^ Lr
  hm : p.wy < 2 ^ Lm
  hsegment : p.K < 2 ^ LK
  hcountFit : p.n < 2 ^ Ln
  hoffset : p.ρ + 1 < 2 ^ Lo
  htop : p.m < 2 ^ Lt
  hwidthPlacement : fieldsLen (selectiveLen p 0) < 2 ^ Lcp
  hBin : B < 2 ^ Lp
  hrowCanonical : GrowingCounterData.Canonical rowBits
  hrowNe : rowBits ≠ []
  hrowValue : Counter.value rowBits = R

def canonicalGeneratedInput {Q K : ℕ} (p : Par) (a : CanonicalStageArithmetic p)
    (targets : Finset (Fin p.wy)) (source : Fin p.wy → Fin p.wy)
    (hsource : ∀ q ∈ targets, source q ∉ targets)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (H : ℕ) (hplacementFit : 9 * H ≤ fieldsLen (selectiveLen p 0)) (hw : p.wc ≤ H) (reservoir : Fin 3)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = a.R * 2 ^ fieldsLen (selectiveLen p 0))
    (hlen : ∀ r ∈ l, r.length = a.B ∧ ∀ x ∈ r, x.val < 8) :
    GeneratedPlacedInput 6 Q K Empty Empty Unit := by
  let active := profileActive p a.hK targets
  let s : Fin p.n → SlotSource p 0 := profileSources p a.hK targets source
  let coordinates := sourceCoordinateInputWords (A := prime + K) a.w.indexBits a.w.strideBits
    (profileCoordinateInputs p a.hK targets source)
  let core := canonicalProfileCoreBank p 0 a.rb a.wb a.wm a.wp a.wk a.R a.B l.flatten coordinates
  let S : Stacks (liveInactiveProfileT repairT 11) (prime + K) :=
    ⟨[], [], fun _ => [], canonicalLiveInputBank p 0 a.hG a.hK active s a.w core⟩
  let D : Stacks inactiveProfileHeaderT (prime + K) := canonicalHeaderInputStack (N := repairInactiveProfileT) S a.Lrow a.Lwidth a.R p.wc
  let E : Stacks inactiveProfileConfigurationT (prime + K) := canonicalWidthInputStack (N := inactiveProfileHeaderT) D a.Lr a.Lm a.rb p.wy
  let F : Stacks inactiveClassifierT (prime + K) := canonicalClassifierInputStack (N := inactiveProfileConfigurationT) E p a.LK a.Ln a.Lo a.Lt
  let spec := reservoirExchangeSpecs (fieldsLen (selectiveLen p 0)) H hplacementFit p.wc hw reservoir
  let M : Stacks (inactiveClassifierPlacementT 6) (prime + K) := canonicalPlacementInputStack (N := inactiveClassifierT) (t₀ := 6)
    (classifierCore (inactiveConfigurationCore repairHost.src)) F spec a.Lcp a.Lp a.B a.rowBits l.flatten
  have hSL : ∀ j, S.L j = [] := fun _ => rfl
  have hDL := canonicalHeaderInputStack_left (N := repairInactiveProfileT) S a.Lrow a.Lwidth a.R p.wc hSL
  have hEL := canonicalWidthInputStack_left (N := inactiveProfileHeaderT) D a.Lr a.Lm a.rb p.wy hDL
  have hFL := canonicalClassifierInputStack_left (N := inactiveProfileConfigurationT) E p a.LK a.Ln a.Lo a.Lt hEL
  refine {
    p := p, X := 0, rb := a.rb, hG := a.hG, hK := a.hK, hguard := a.hguard
    scale := a.scale, hscale := a.hscale, hn := a.hn, hradix := a.hradix, hgap := a.hgap
    active := active, s := s, targets := targets, source := source, hactive := rfl, hsources := rfl
    body := Empty.elim, liveBody := Empty.elim, hlive := by intro f; exact f.elim
    outerBody := Empty.elim, houter := by intro f; exact f.elim
    keySrc := canonicalProfileKey, raw := canonicalProfileRaw, activity := canonicalProfileActivity
    hreg := canonicalProfile_registers
    hkeyHeader := fun c k => (canonicalProfileKey_source (.inl (.header c k))).symm
    hrawHeader := fun c k => (canonicalProfileRaw_source (.inl (.header c k))).symm
    hactivityHeader := ?hactivityHeader
    hkeyRow := (canonicalProfileKey_source (.inr .row)).symm
    hkeyMask := (canonicalProfileKey_source (.inr .keyMask)).symm
    hrawRow := (canonicalProfileRaw_source (.inr .row)).symm
    hrawMask := (canonicalProfileRaw_source (.inr .keyMask)).symm
    hactivityRow := ?hactivityRow, hactivityMask := ?hactivityMask
    hkeyBadMask := (canonicalProfileKey_source (.inr .badMask)).symm
    hkeyBadPhase := (canonicalProfileKey_source (.inr .badPhase)).symm
    hrawBadMask := (canonicalProfileRaw_source (.inr .badMask)).symm
    hrawBadPhase := (canonicalProfileRaw_source (.inr .badPhase)).symm
    hactivityBadMask := ?hactivityBadMask, hactivityBadPhase := ?hactivityBadPhase
    hkeySrc := ?hkeySrc, hrawSrc := ?hrawSrc, hactivitySrc := ?hactivitySrc
    w := a.w, hwidth := a.hwidth, hselectorWidthFit := a.hselectorWidthFit
    hkfit := a.hkfit, hnfit := a.hnfit, hwfit := a.hwfit, hQ := hQ, hA := hA
    wb := a.wb, wm := a.wm, wp := a.wp, wk := a.wk, R := a.R, B := a.B
    hR := a.hR, hB := a.hB, hrb := a.hrb, hs := profileSources_allowed p a.hK targets source hsource
    S := S, data := ?data, hempty := ?hempty, hL := by intro j; rfl, hblank := ?hblank, hfit := a.hfit
    hbank := ?hbank, hdesc := ?hdesc, hinput := ?hinput, hkey := ?hkey, hrawBlank := ?hrawBlank, hactivity := ?hactivity
    hcount := ?hcount, hscratch := ?hscratch, l := l, hl := hl, hlen := hlen, hsrc := ?hsrc
    D := D, hproject := canonicalHeaderInputStack_project (N := repairInactiveProfileT) S a.Lrow a.Lwidth a.R p.wc
    headerBody := Empty.elim, hheader := by intro f; exact f.elim
    Lrow := a.Lrow, Lwidth := a.Lwidth, hRfit := a.hRfit, hwidthFit := a.hwidthFit
    hrowInput := ?hrowInput, hwidthInput := ?hwidthInput, hwork := ?hwork
    E := E, hE := canonicalWidthInputStack_project (N := inactiveProfileHeaderT) D a.Lr a.Lm a.rb p.wy
    widthBody := Empty.elim, hwidthBody := by intro f; exact f.elim
    Lr := a.Lr, Lm := a.Lm, hr := a.hr, hm := a.hm
    hrowWidth := ?hrowWidth, hmaskWidth := ?hmaskWidth, hwidthScratch := ?hwidthScratch, hrow := ?hrow, hmask := ?hmask
    classifierBody := Empty.elim, hclassifier := by intro f; exact f.elim
    F := F, hF := canonicalClassifierInputStack_project (N := inactiveProfileConfigurationT) E p a.LK a.Ln a.Lo a.Lt
    LK := a.LK, Ln := a.Ln, Lo := a.Lo, Lt := a.Lt
    hsegment := a.hsegment, hcountFit := a.hcountFit, hoffset := a.hoffset, htop := a.htop
    hsegmentInput := ?hsegmentInput, hrunInput := ?hrunInput, hcountInput := ?hcountInput, hoffsetInput := ?hoffsetInput, hphaseOffsetInput := ?hphaseOffsetInput, htopInput := ?htopInput
    hclassifierScratch := ?hclassifierScratch, htemporary := ?htemporary, hphase := ?hphase
    ι := Empty.elim, placementBody := Empty.elim, hplacementBody := by intro f; exact f.elim
    M := M, houterProject := canonicalPlacementInputStack_project (N := inactiveClassifierT) (t₀ := 6) _ F spec a.Lcp a.Lp a.B a.rowBits l.flatten
    Hslot := H, hplacementFit := hplacementFit, slotWidth := p.wc, hslotWidth := hw, reservoir := reservoir
    hd := selectiveSwapHd, pay := selectiveSwapPay, hhd := selectiveSwapHd_inj, hpay := ?hpay
    hQplacement := hQ, hT := ?hT, rowBits := a.rowBits, Lcp := a.Lcp, Lp := a.Lp
    hwidthPlacement := a.hwidthPlacement, hBin := a.hBin
    hrowCanonical := a.hrowCanonical, hrowNe := a.hrowNe, hrowValue := a.hrowValue
    bankWords := fun _ => [], hpay0 := rfl, hpriv := by intro j hj; rfl, hhdr0 := by intro k; rfl
    hother := by intro i hi hh x hx; cases hx
    hleft := canonicalPlacementInputStack_left (N := inactiveClassifierT) (t₀ := 6) _ F spec a.Lcp a.Lp a.B a.rowBits l.flatten hFL
    hplacementBank := by dsimp only [M, canonicalPlacementInputStack, spec] }
  case hactivityHeader =>
    intro c k
    simp [canonicalProfileActivity, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  case hactivityRow | hactivityMask | hactivityBadMask | hactivityBadPhase =>
    simp [canonicalProfileActivity, repairSetupSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  case hkeySrc | hrawSrc | hactivitySrc =>
    simp [canonicalProfileKey, canonicalProfileRaw, canonicalProfileActivity, repairKey, repairBad,
      repairRoutingConfig, placedSelectiveConfig, repairHost, SelectiveHost.map, placedSelectiveHost, repairRoutingRole]
  case data =>
    simpa only [S, canonicalLiveInputBank_core] using
      canonicalProfileCoreBank_data p 0 a.rb a.wb a.wm a.wp a.wk a.R a.B l.flatten coordinates a.hblock a.hrecords a.hpayload a.hkey
  case hempty =>
    intro j
    dsimp only [S]
    rw [canonicalLiveInputBank_core]
    exact canonicalProfileCoreBank_targets p 0 a.rb a.wb a.wm a.wp a.wk a.R a.B l.flatten coordinates j
  case hblank =>
    intro j hj
    dsimp only [S]
    rw [canonicalLiveInputBank_core]
    exact canonicalProfileCoreBank_scratch p 0 a.rb a.wb a.wm a.wp a.wk a.R a.B l.flatten coordinates j hj
  case hbank =>
    intro r hr
    exact canonicalLiveInputBank_operands p 0 a.hG a.hK active s a.w core r hr
  case hdesc =>
    intro d
    dsimp only [S]
    rw [canonicalLiveInputBank_core]
    exact canonicalProfileCoreBank_descriptors p 0 a.rb a.wb a.wm a.wp a.wk a.R a.B l.flatten coordinates d
  case hinput =>
    intro j
    exact canonicalLiveInputBank_inputs p 0 a.hG a.hK active s a.w core j
  case hkey =>
    dsimp only [S]
    rw [show liveZSourceActivity canonicalProfileKey = liveInactiveProfileCore (liveDescriptorCore canonicalProfileKey) from rfl,
      canonicalLiveInputBank_core]
    exact canonicalProfileCoreBank_key p 0 a.rb a.wb a.wm a.wp a.wk a.R a.B l.flatten coordinates
  case hrawBlank =>
    dsimp only [S]
    rw [show liveZSourceActivity canonicalProfileRaw = liveInactiveProfileCore (liveDescriptorCore canonicalProfileRaw) from rfl,
      canonicalLiveInputBank_core]
    exact canonicalProfileCoreBank_raw p 0 a.rb a.wb a.wm a.wp a.wk a.R a.B l.flatten coordinates
  case hactivity =>
    dsimp only [S]
    rw [show liveZSourceActivity canonicalProfileActivity = liveInactiveProfileCore (liveDescriptorCore canonicalProfileActivity) from rfl,
      canonicalLiveInputBank_core]
    exact canonicalProfileCoreBank_activity p a.rb a.wb a.wm a.wp a.wk a.R a.B l.flatten coordinates
  case hsrc =>
    dsimp only [S]
    rw [canonicalLiveInputBank_core]
    exact canonicalProfileCoreBank_stream p 0 a.rb a.wb a.wm a.wp a.wk a.R a.B l.flatten coordinates
  case hcount => simp [S, canonicalLiveInputBank_aux]
  case hscratch => intro j hj; simp [S, canonicalLiveInputBank_aux, hj]
  case hrowInput | hwidthInput =>
    simp [D, canonicalHeaderInputStack, sharedHeaderBinary, canonicalHeaderInputBank_work, canonicalHeaderOperands]
  case hwork =>
    intro r hr
    dsimp only [D, canonicalHeaderInputStack]
    exact canonicalHeaderInputBank_blank (N := repairInactiveProfileT) S.R a.Lrow a.Lwidth a.R p.wc r hr
  case hrowWidth | hmaskWidth => simp [E, canonicalWidthInputStack, canonicalWidthInputBank_aux]
  case hwidthScratch =>
    intro j hj
    dsimp only [E, canonicalWidthInputStack]
    rw [canonicalWidthInputBank_aux]
    have h0 : j ≠ 0 := by intro h; subst j; norm_num at hj
    have h1 : j ≠ 1 := by intro h; subst j; norm_num at hj
    simp [h0, h1]
  case hrow | hmask =>
    simp only [E, D, S, canonicalWidthInputStack, canonicalHeaderInputStack, canonicalWidthInputBank_core,
      canonicalHeaderInputBank_core, canonicalLiveInputBank_core, inactiveProfileHeaderRaw, embeddedRepairHeaderRaw,
      inactiveProfileRaw, core, canonicalProfileCoreBank_source, canonicalRepairPayload]
  case hsegmentInput | hrunInput | hcountInput | hoffsetInput | hphaseOffsetInput | htopInput =>
    simp [F, canonicalClassifierInputStack, canonicalClassifierInputBank_aux, canonicalClassifierOperands]
  case hclassifierScratch =>
    intro j h2 h10 h13
    dsimp only [F, canonicalClassifierInputStack]
    exact canonicalClassifierInputBank_scratch (N := inactiveProfileConfigurationT) E.R p a.LK a.Ln a.Lo a.Lt j h2 h10 h13
  case htemporary | hphase =>
    simp only [F, E, D, S, canonicalClassifierInputStack, canonicalWidthInputStack, canonicalHeaderInputStack,
      canonicalClassifierInputBank_core, canonicalWidthInputBank_core, canonicalHeaderInputBank_core,
      canonicalLiveInputBank_core, inactiveClassifierTemporary, inactiveClassifierPhase, inactiveConfigurationCore,
      inactiveProfileHeaderRaw, embeddedRepairHeaderRaw, inactiveProfileRaw, core,
      canonicalProfileCoreBank_source, canonicalRepairPayload]
  case hpay =>
    intro k h
    have hv := congrArg (fun x : Fin 6 => x.val) h
    change k.val = 5 at hv
    have hk := k.isLt
    omega
  case hT => unfold inactiveClassifierPlacementT sharedScheduleT; omega

def canonicalGeneratedProgram {Q K : ℕ}
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K) :
    Pr Empty (inactiveClassifierPlacementT 6) Q (prime + K) Unit :=
  allSourcePlacedFixedProgram canonicalProfileKey canonicalProfileRaw canonicalProfileActivity hQ hA
    selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj hQ
    (by unfold inactiveClassifierPlacementT sharedScheduleT; omega) Empty.elim

/-- The constructed input introduces no geometry-dependent program code. -/
theorem canonicalGeneratedInput_program {Q K : ℕ} (p : Par) (a : CanonicalStageArithmetic p)
    (targets : Finset (Fin p.wy)) (source : Fin p.wy → Fin p.wy)
    (hsource : ∀ q ∈ targets, source q ∉ targets)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (H : ℕ) (hplacementFit : 9 * H ≤ fieldsLen (selectiveLen p 0)) (hw : p.wc ≤ H) (reservoir : Fin 3)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = a.R * 2 ^ fieldsLen (selectiveLen p 0))
    (hlen : ∀ r ∈ l, r.length = a.B ∧ ∀ x ∈ r, x.val < 8) :
    let input := canonicalGeneratedInput p a targets source hsource hQ hA H hplacementFit hw reservoir l hl hlen
    allSourcePlacedFixedProgram input.keySrc input.raw input.activity input.hQ input.hA input.hd input.pay
      input.hhd input.hQplacement input.hT input.ι = canonicalGeneratedProgram hQ hA := by
  rfl


theorem sourceCoordinateInputWords_small {A : ℕ} (Li Lk : ℕ) (entries : List (ℕ × Bool)) :
    ∀ x ∈ (sourceCoordinateInputWords Li Lk entries : List (Fin (A + 4))), x.val < 8 := by
  induction entries with
  | nil => simp [sourceCoordinateInputWords]
  | cons entry entries ih =>
    intro x hx
    simp only [sourceCoordinateInputWords, sourceCoordinateInputRecord, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with (hx | (rfl | (hx | rfl))) | hx
    · exact canonicalScalarWord_small _ _ x hx
    · change 3 < 8
      omega
    · exact canonicalScalarWord_small _ _ x hx
    · change 3 < 8
      omega
    · exact ih x hx

theorem canonicalGeneratedInput_small {Q K : ℕ} (p : Par) (a : CanonicalStageArithmetic p)
    (targets : Finset (Fin p.wy)) (source : Fin p.wy → Fin p.wy)
    (hsource : ∀ q ∈ targets, source q ∉ targets)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (H : ℕ) (hplacementFit : 9 * H ≤ fieldsLen (selectiveLen p 0)) (hw : p.wc ≤ H) (reservoir : Fin 3)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = a.R * 2 ^ fieldsLen (selectiveLen p 0))
    (hlen : ∀ r ∈ l, r.length = a.B ∧ ∀ x ∈ r, x.val < 8) :
    ∀ j, ∀ x ∈ (canonicalGeneratedInput p a targets source hsource hQ hA H hplacementFit hw reservoir l hl hlen).M.R j,
      x.val < 8 := by
  have hrecords : ∀ x ∈ l.flatten, x.val < 8 := by
    intro x hx
    obtain ⟨row, hr, hx⟩ := List.mem_flatten.mp hx
    exact (hlen row hr).2 x hx
  dsimp only [canonicalGeneratedInput]
  apply canonicalPlacementInputStack_small (N := inactiveClassifierT)
  · dsimp only [canonicalClassifierInputStack]
    apply canonicalClassifierInputBank_small (N := inactiveProfileConfigurationT)
    dsimp only [canonicalWidthInputStack]
    apply canonicalWidthInputBank_small (N := inactiveProfileHeaderT)
    dsimp only [canonicalHeaderInputStack]
    apply canonicalHeaderInputBank_small (N := repairInactiveProfileT)
    apply canonicalLiveInputBank_small
    apply canonicalProfileCoreBank_small
    · exact hrecords
    · exact sourceCoordinateInputWords_small _ _ _
  · exact hrecords

end
end IntegerMultBounds.MathlibTM2.Routing
