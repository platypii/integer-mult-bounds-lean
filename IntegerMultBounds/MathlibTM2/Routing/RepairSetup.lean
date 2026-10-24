module

public import IntegerMultBounds.MathlibTM2.Routing.RepairSetupData
public import IntegerMultBounds.MathlibTM2.Routing.RepairSetupBlank

/-! Executed metadata setup establishing every shared key/route/repair invariant. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable section

variable {Q K : ℕ} {P U : Type}
variable (p : Par) (X rb : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

def repairJobs (wb wm wp wk R B : ℕ) : List (MetadataJob repairT) :=
  repairSetupJobs wb wm wp wk (fieldsLen (selectiveKeyLen p X rb) + B)
    (R * 2 ^ fieldsLen (selectiveLen p X)) B (fieldsLen (selectiveKeyLen p X rb))

theorem repairJobs_nodup (wb wm wp wk R B : ℕ) :
    ((repairJobs p X rb wb wm wp wk R B).map MetadataJob.dst).Nodup := by
  simpa only [repairJobs, repairSetupJobs, List.map_map, Function.comp_def, repairSetupJob_dst] using
    repairSetupKeys_nodup.map repairSetupTarget_injective

theorem repairSetup_at {wb wm wp wk R B : ℕ} {headers : Fin 2 → Fin 5 → List Bool}
    {bank : Fin repairT → List (Fin (prime + K + 4))}
    (data : RepairSetupData p X rb hG hK active s wb wm wp wk R B headers bank)
    (key : RepairSetupKey) :
    metadataInstalled bank (repairJobs p X rb wb wm wp wk R B) (repairSetupTarget key) =
      repairSetupPayload p X rb hG hK active s R B headers key := by
  have he := metadataInstalled_at bank (repairJobs p X rb wb wm wp wk R B)
    (repairJobs_nodup p X rb wb wm wp wk R B)
    (repairSetupJob wb wm wp wk (fieldsLen (selectiveKeyLen p X rb) + B)
      (R * 2 ^ fieldsLen (selectiveLen p X)) B (fieldsLen (selectiveKeyLen p X rb)) key)
    (List.mem_map.mpr ⟨key, repairSetupKeys_mem key, rfl⟩)
  rw [repairSetupJob_dst, RepairSetupData.contents p X rb hG hK active s data key] at he
  exact he

theorem repairSetup_blank (wb wm wp wk R B : ℕ)
    (bank : Fin repairT → List (Fin (prime + K + 4))) (j : Fin repairT) (hj : RepairBlank j) :
    metadataInstalled bank (repairJobs p X rb wb wm wp wk R B) j = bank j := by
  apply metadataInstalled_keep
  intro hm
  obtain ⟨job, hjob, he⟩ := List.mem_map.mp hm
  obtain ⟨key, _, rfl⟩ := List.mem_map.mp hjob
  rw [repairSetupJob_dst] at he
  exact repairSetup_target_blank key j hj he

/-- All shared prepared conditions follow from the actual installed words. -/
theorem repairSetup_prepared {wb wm wp wk R B : ℕ} {headers : Fin 2 → Fin 5 → List Bool}
    (S : Stacks repairT (prime + K))
    (data : RepairSetupData p X rb hG hK active s wb wm wp wk R B headers S.R)
    (hL : ∀ j, S.L j = []) (hblank : ∀ j, RepairBlank j → S.R j = []) :
    RepairPrepared p X rb hG hK active s R B headers
      { S with R := metadataInstalled S.R (repairJobs p X rb wb wm wp wk R B) } := by
  let bank := metadataInstalled S.R (repairJobs p X rb wb wm wp wk R B)
  have hat := repairSetup_at p X rb hG hK active s data
  have hb (j : Fin repairT) (hj : RepairBlank j) : bank j = [] := by
    change metadataInstalled S.R (repairJobs p X rb wb wm wp wk R B) j = []
    rw [repairSetup_blank p X rb wb wm wp wk R B S.R j hj, hblank j hj]
  have hlen (f : Fin 5) : selectiveKeyLen p X rb f.castSucc = selectiveLen p X f := by
    fin_cases f <;> rfl
  constructor
  · apply selectivePrepared_of_words p X hG hK active s repairHost { S with R := bank }
      (fun key => hat (.inl key)) hL
    exact fun j hj => hb j (Or.inl hj)
  · intro r hr
    cases r with
    | fld f =>
      refine Fin.lastCases ?_ (fun g => ?_) f
      · simpa [repairSetupTarget, repairExtraTarget, repairSetupPayload, repairExtraPayload,
          repairKey, selectiveKeyLen, digit] using hat (.inr .row)
      · have he := hat (.inl (.field g))
        change bank (repairKey (.fld g.castSucc)) =
          binSyms (selectiveKeyLen p X rb g.castSucc) (digit (selectiveKeyLen p X rb) g.castSucc 0)
        rw [repairKey_cf, hlen]
        simpa [repairSetupTarget, SetupKey.target, repairSetupPayload, setupPayload, digit] using he
    | desc k =>
      fin_cases k
      · simpa [repairSetupTarget, repairExtraTarget, repairSetupPayload, repairExtraPayload,
          keyPatternStatic] using hat (.inr .keyDescriptor)
      · simpa [repairSetupTarget, repairExtraTarget, repairSetupPayload, repairExtraPayload,
          keyPatternStatic] using hat (.inr .keyMask)
    | st => exact (hr rfl).elim
    | word k | spare k =>
      exact hb _ (Or.inr (Or.inr (Or.inl ⟨_, by simp, by simp, by simp, rfl⟩)))
    | ts | tm | dst =>
      exact hb _ (Or.inr (Or.inr (Or.inl ⟨_, by simp, by simp, by simp, rfl⟩)))
  · intro r hr
    cases r with
    | fld f =>
      simpa [repairSetupTarget, SetupKey.target, repairSetupPayload, setupPayload, digit]
        using hat (.inl (.field f))
    | mask =>
      exact hat (.inr .badMask)
    | phase =>
      exact hat (.inr .badPhase)
    | st => exact (hr rfl).elim
    | word k | spare k =>
      exact hb _ (Or.inr (Or.inr (Or.inr ⟨_, by simp, by simp, by simp, by simp, rfl⟩)))
    | ts | tm | dst =>
      exact hb _ (Or.inr (Or.inr (Or.inr ⟨_, by simp, by simp, by simp, by simp, rfl⟩)))
  · simpa [repairSetupTarget, repairExtraTarget, repairSetupPayload, repairExtraPayload] using
      congrArg List.length (hat (.inr .payload))
  · simpa [repairSetupTarget, repairExtraTarget, repairSetupPayload, repairExtraPayload] using
      congrArg List.length (hat (.inr .keyLength))
  · exact hb _ (Or.inr (Or.inl rfl))

/-- Actual metadata installation discharges the swap-bank bound from header widths. -/
theorem repairSetup_swapBank_length_le {wb wm wp wk R B : ℕ} {headers : Fin 2 → Fin 5 → List Bool}
    (S : Stacks repairT (prime + K))
    (data : RepairSetupData p X rb hG hK active s wb wm wp wk R B headers S.R)
    (hL : ∀ j, S.L j = []) (hblank : ∀ j, RepairBlank j → S.R j = [])
    (width : ℕ) (hheaders : ∀ c k, (headers c k).length ≤ width) (c : Fin 2) :
    (∑ j, (metadataInstalled S.R (repairJobs p X rb wb wm wp wk R B) (repairHost.swaps c j)).length) ≤
      swapT 6 * (width + 1) := by
  have h := (repairSetup_prepared p X rb hG hK active s S data hL hblank).routing
  exact h.swapBank_length_le p X repairHost hG hK active s width hheaders c

/-- Actual installation of every shared word, with raw inputs and scratch restored. -/
theorem repairSetup_exec (body : P → Pr P repairT Q (prime + K) U)
    {wb wm wp wk R B : ℕ} {headers : Fin 2 → Fin 5 → List Bool}
    (v : HS repairT Q (prime + K) U) (S : Stacks repairT (prime + K))
    (data : RepairSetupData p X rb hG hK active s wb wm wp wk R B headers S.R)
    (hempty : ∀ key, S.R (repairSetupTarget key) = [])
    (hL : ∀ j, S.L j = []) (hblank : ∀ j, RepairBlank j → S.R j = []) :
    ∃ (v' : HS repairT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ metadataInstallCost S.R (repairJobs p X rb wb wm wp wk R B) ∧
      Exec body repairSetup (mk v S) steps
        (mk v' { S with R := metadataInstalled S.R (repairJobs p X rb wb wm wp wk R B) }) ∧
      RepairPrepared p X rb hG hK active s R B headers
        { S with R := metadataInstalled S.R (repairJobs p X rb wb wm wp wk R B) } := by
  have hregs : ∀ job ∈ repairJobs p X rb wb wm wp wk R B,
      [job.src, job.dst, repairHost.out, repairHost.tmp, repairHost.ctmp].Nodup := by
    intro job hj
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
    simpa only [repairSetupJob_src, repairSetupJob_dst] using repairSetup_regs key
  have hsource : ∀ job ∈ repairJobs p X rb wb wm wp wk R B,
      ∀ other ∈ repairJobs p X rb wb wm wp wk R B, job.src ≠ other.dst := by
    intro job hj other ho
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
    obtain ⟨key', _, rfl⟩ := List.mem_map.mp ho
    simpa only [repairSetupJob_src, repairSetupJob_dst] using repairSetup_sources key key'
  obtain ⟨v', steps, hu, hm, he⟩ := metadataInstall_exec body
    (repairJobs p X rb wb wm wp wk R B) repairHost.out repairHost.tmp repairHost.ctmp
    (repairJobs_nodup p X rb wb wm wp wk R B) hregs hsource v S
    (fun job hj => by
      obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
      exact RepairSetupData.jobData p X rb hG hK active s data key)
    (fun job hj => by
      obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
      simpa only [repairSetupJob_dst] using hempty key)
    (hblank _ (Or.inl (Or.inl (by simp))))
    (hblank _ (Or.inl (Or.inl (by simp)))) (hblank _ (Or.inl (Or.inl (by simp))))
  have hprogram : (repairSetup : Pr P repairT Q (prime + K) U) =
      metadataInstall repairHost.out repairHost.tmp repairHost.ctmp (repairJobs p X rb wb wm wp wk R B) :=
    repairSetup_eq wb wm wp wk _ _ _ _
  rw [← hprogram] at he
  exact ⟨v', steps, hu, hm, he, repairSetup_prepared p X rb hG hK active s S data hL hblank⟩

end
end IntegerMultBounds.MathlibTM2.Routing
