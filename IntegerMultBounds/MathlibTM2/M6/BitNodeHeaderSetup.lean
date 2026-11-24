module

public import IntegerMultBounds.MathlibTM2.M6.BitNodeSeedWords

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback Node M8.RevMachine
open Shared50ModularControl (prime)

def nodeHeaderSources {T : ℕ} (fields : Fin 6 → Fin T) (clock : Fin 7 ↪ Fin T)
    (power : Fin 10 ↪ Fin T) (cut idle : Fin T) (i : Fin 12) : Fin T :=
  Fin.addCases (motive := fun _ => Fin T)
    (Fin.cons cut (descriptorArchiveSources fields clock power)) (![idle,clock 1] : Fin 2 → Fin T) i

def nodeHeaderSetupRate : ℕ := 2000366

/-- Derive both unary clocks, the modulus, and the unit from the descriptor width.
Measure a payload lane to obtain the idle width. Only the cutoff and descriptor fields enter on header tapes. -/
theorem nodeHeaderSetup {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (fields : Fin 6 → Fin T) (clock : Fin 7 ↪ Fin T) (power : Fin 10 ↪ Fin T)
    (cut row : Fin T) (division : Fin 11 ↪ Fin T) (width : clock 0 = fields 3) (long : power 0 = clock 1)
    (short : ∀ j, clock 2 ≠ power j)
    (frame : ∀ i, outsideArchiveOutputs clock power (fields i))
    (cutFrame : outsideArchiveOutputs clock power cut) (rowFrame : outsideArchiveOutputs clock power row)
    (divFrame : ∀ i, outsideArchiveOutputs clock power (division i))
    (rowOff : ∀ i, row ≠ division i) (cutOff : cut ≠ division 2)
    (fieldsOff : ∀ i, fields i ≠ division 2) :
    let source := nodeHeaderSources fields clock power cut (division 2)
    ∃ code, ∀ (c : CutoffNodeInput) u (S : Stacks T prime),
      (∀ i, S.R (fields i) = (Routines.hdr c.node i).map bitSymbol) →
      S.R cut = binSyms c.root.width.size c.cutoff → (S.R row).length = c.cells →
      (∀ j : Fin 7, j ≠ 0 → S.R (clock j) = []) → (∀ j : Fin 10, j ≠ 0 → S.R (power j) = []) →
      (∀ i, S.R (division i) = []) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (nodeHeaderSetupRate*c.cells) ∧ (∀ i, F.R (source i) = nodeSeedWords c i) ∧
        ∀ j, outsideArchiveOutputs clock power j → j ≠ division 2 → F.L j = S.L j ∧ F.R j = S.R j := by
  intro source
  obtain ⟨code,run⟩ := descriptorArchiveWords body fields clock power width long short frame
  obtain ⟨measure,divide⟩ := spectatorFromLane body division row (power 3) rowOff (fun i => (divFrame i).2.2.2) false
  refine ⟨code.seq measure,?_⟩
  intro c u S digits cutoff length clocks powers vacant
  obtain ⟨z,F,t,exec,user,paid,ticks,archive,off⟩ := run c.node c.w c.width u S digits clocks powers
  have kept j (h : outsideArchiveOutputs clock power j) := off j h.1 h.2.1 h.2.2.1 h.2.2.2
  have radix := archive (6 : Fin 9)
  change F.R (power 3) = binSyms (prime^(c.w+1)).size (prime^(c.w+1)) at radix
  obtain ⟨v,m,scan,same,charge⟩ := divide c z F ((congrArg List.length (kept _ rowFrame).2).trans length)
    radix (fun i => (kept _ (divFrame i)).2.trans (vacant i))
  refine ⟨v,_,_,exec.seq scan,same.trans user,?_,?_,?_⟩
  · intro js nd
    apply ((paid.seq charge) js nd).trans
    apply Nat.add_le_add_left
    have mass : prime^(c.w+1) ≤ c.cells := (Nat.le_self_pow (by decide : 128 ≠ 0) _).trans
      (Nat.le_mul_of_pos_right _ (Nat.mul_pos c.idlePositive (by decide)))
    have positive : 0 < prime^(c.w+1) := pow_pos Shared50ModularControl.prime_prime.pos _
    have setup := c.remainderSetup_le 0
    simp only [Nat.zero_mul] at setup
    unfold nodeHeaderSetupRate
    omega
  · intro i
    induction i using Fin.addCases (m := 10) (n := 2) with
    | left j =>
      simp only [source,nodeHeaderSources,nodeSeedWords,Fin.addCases_left]
      induction j using Fin.cases with
      | zero => simpa only [sweepSeedWords,Fin.cons_zero,Function.update_of_ne cutOff] using (kept _ cutFrame).2.trans cutoff
      | succ j =>
        have apart : descriptorArchiveSources fields clock power j ≠ division 2 := by
          induction j using Fin.addCases (m := 6) (n := 3) with
          | left i => simpa [descriptorArchiveSources] using fieldsOff i
          | right i =>
            fin_cases i
            · exact (divFrame 2).2.2.2.symm
            · exact (divFrame 2).2.2.1.symm
            · exact (divFrame 2).2.1.symm
        simpa only [sweepSeedWords,Fin.cons_succ,Function.update_of_ne apart] using archive j
    | right j =>
      fin_cases j
      · exact Function.update_self ..
      · exact (Function.update_of_ne (divFrame 2).1.symm ..).trans ticks
  · intro j outside offDiv
    exact ⟨(kept j outside).1,(Function.update_of_ne offDiv ..).trans (kept j outside).2⟩

/-- Initialize a private node bank from the six descriptor fields, cutoff, and
one live lane. The payload row is preserved. -/
def LoadsNodeSeedFromRecord {Config : Type} {N : ℕ} (input : Config → CutoffNodeInput)
    (seed : Config → Stacks N prime) : Prop :=
  ∃ rate : ℕ, ∀ {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U) (bank : Fin N ↪ Fin T)
    (fields : Fin 6 → Fin T) (clock : Fin 7 ↪ Fin T) (power : Fin 10 ↪ Fin T)
    (cut row : Fin T) (div : Fin 11 ↪ Fin T),
    clock 0 = fields 3 → power 0 = clock 1 → (∀ j, clock 2 ≠ power j) →
    (∀ i, outsideArchiveOutputs clock power (fields i)) → outsideArchiveOutputs clock power cut →
    outsideArchiveOutputs clock power row → (∀ i, outsideArchiveOutputs clock power (div i)) →
    (∀ i, row ≠ div i) → cut ≠ div 2 → (∀ i, fields i ≠ div 2) →
    (∀ i j, bank i ≠ nodeHeaderSources fields clock power cut (div 2) j) →
    (∀ i, bank i ≠ row) →
    ∃ code, ∀ x u (S : Stacks T prime), let c := input x
      (∀ i, S.R (fields i) = (Routines.hdr c.node i).map bitSymbol) →
      S.R cut = binSyms c.root.width.size c.cutoff → (S.R row).length = c.cells →
      (∀ j : Fin 7, j ≠ 0 → S.R (clock j) = []) → (∀ j : Fin 10, j ≠ 0 → S.R (power j) = []) →
      (∀ i, S.R (div i) = []) → (∀ i, S.L (bank i) = [] ∧ S.R (bank i) = []) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (rate*c.cells) ∧
        (∀ i, F.L (bank i) = (seed x).L i ∧ F.R (bank i) = (seed x).R i) ∧
        F.R row = S.R row ∧
        ∀ j, (∀ i, bank i ≠ j) → outsideArchiveOutputs clock power j → j ≠ div 2 →
          F.L j = S.L j ∧ F.R j = S.R j

private theorem headerBankFrame {T N : ℕ} {bank : Fin N ↪ Fin T} {fields : Fin 6 → Fin T}
    {clock : Fin 7 ↪ Fin T} {power : Fin 10 ↪ Fin T} {cut idle : Fin T}
    (apart : ∀ i j, bank i ≠ nodeHeaderSources fields clock power cut idle j) (i : Fin N) :
    outsideArchiveOutputs clock power (bank i) ∧ bank i ≠ idle :=
  ⟨⟨apart i 11,apart i 9,apart i 8,apart i 7⟩,apart i 10⟩

private theorem combineSetupCharge {A B : Type} {T : ℕ} {S D F : Stacks T prime}
    {n m a b : ℕ} (V : A → ℕ) (input : B → A) (x : B)
    (setup : CleanupBound S D n (a*V (input x)))
    (load : CleanupBound D F m (b*(V ∘ input) x)) :
    CleanupBound S F (n+m) ((a+b)*V (input x)) := by
  rw [Nat.add_mul]
  exact setup.seq load

theorem LoadsPackedSeed.fromNodeRecord {Config : Type} {N : ℕ} {input : Config → CutoffNodeInput}
    {seed : Config → Stacks N prime}
    (loader : LoadsPackedSeed (nodeSeedWords ∘ input) (CutoffNodeInput.cells ∘ input) seed) :
    LoadsNodeSeedFromRecord input seed := by
  obtain ⟨rate,load⟩ := loader
  refine ⟨nodeHeaderSetupRate+rate,?_⟩
  intro P U T Q body bank fields clock power cut row div width long short frame cutFrame rowFrame divFrame rowOff cutOff fieldsOff apart rowAway
  obtain ⟨headers,setup⟩ := nodeHeaderSetup body fields clock power cut row div width long short frame cutFrame rowFrame divFrame rowOff cutOff fieldsOff
  obtain ⟨code,install⟩ := load body bank _ apart
  refine ⟨headers.seq code,?_⟩
  intro x u S c digits cutoff length clocks powers vacant empty
  obtain ⟨v,D,n,start,same,paid,ready,kept⟩ := setup c u S digits cutoff length clocks powers vacant
  obtain ⟨z,F,m,finish,user,charge,stored,off⟩ := install x v D ready (fun i =>
    let free := headerBankFrame apart i
    let h := kept (bank i) free.1 free.2
    ⟨h.1.trans (empty i).1,h.2.trans (empty i).2⟩)
  refine ⟨z,F,_,start.seq finish,user.trans same,?_,stored,?_,?_⟩
  · exact combineSetupCharge CutoffNodeInput.cells input x paid charge
  · exact (off row rowAway).2.trans (kept row rowFrame (rowOff 2)).2
  · intro j away frame h
    exact ⟨(off j away).1.trans (kept j frame h).1,(off j away).2.trans (kept j frame h).2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
