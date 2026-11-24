module

public import IntegerMultBounds.MathlibTM2.M6.BitDigitPermutationSeed
public import IntegerMultBounds.MathlibTM2.M6.BitDispatchedPackedStage

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Cover RecursiveInterchangeLayout M8.RevMachine
open Shared50ModularControl (prime)

/-- Load both basis banks and the permutation bank with one program. The
permutation borrows its scratch tapes only while installing the swap headers. -/
theorem loadChartBanks {P U : Type} {T Q d spare : ℕ} (degree : 2 ≤ d) (room : 35 ≤ spare)
    (left right : List (FlatCoordinateSchedule.Op d))
    (pairs : List {p : Fin d × Fin d // p.1 < p.2})
    (machine : {p : Fin d × Fin d // p.1 < p.2} → SharedBankSkeleton.Skeleton 1 prime)
    (fits : ∀ p, 25 ≤ (machine p).tapes) (body : P → Pr P T Q prime U)
    (basis : Fin (FlatCoordinateCleanSchedule.tapeCount left+FlatCoordinateCleanSchedule.tapeCount right) ↪ Fin T)
    (perm : Fin ((digitSwapSkeleton machine pairs).tapes+spare) ↪ Fin T)
    (disjoint : ∀ i j, basis i ≠ perm j) (source : Fin 4 → Fin T) (precision : Fin T)
    (basisOff : ∀ i j, basis i ≠ source j) (precisionOff : ∀ i, basis i ≠ precision)
    (permOff : ∀ i j, perm i ≠ source j) :
    let place := (Fin.castAddEmb spare).trans perm
    ∃ rate : ℕ, ∃ code, ∀ w W, 0 < W → ∀ u (S : Stacks T prime),
      let M := prime^(w+1)
      let view := payloadView prime d (w+1) W
      let bank := fun (p : {p : Fin d × Fin d // p.1 < p.2}) => SharedBankStageInput.raw
        (LabelCall.bank (SharedBank.empty 1 prime) view (LabelPrepare.input view d p.val.1 p.val.2 (w+1))) (machine p).tapes
      let seed := adjacentStageStacks (basisHeaderStacks left (w+1) W) (basisHeaderStacks right (w+1) W)
      S.R precision = binSyms (w+1).size (w+1) →
      S.R (source 0) = binSyms M.size M → S.R (source 1) = binSyms 1 1 →
      S.R (source 2) = binSyms W.size W → (S.R (source 3)).length = w →
      (∀ i, S.L (basis i) = [] ∧ S.R (basis i) = []) →
      (∀ i, S.L (perm i) = [] ∧ S.R (perm i) = []) →
      ∃ z F n, Exec body code (mk u S) n (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F n (rate*(M^d*W)) ∧
        (∀ i, F.L (basis i) = seed.L i ∧ F.R (basis i) = seed.R i) ∧
        RepT (digitPermutationMetadata machine bank pairs) (F.L ∘ place) (F.R ∘ place) ∧
        ∀ j, (∀ i, basis i ≠ j) → (∀ i, place i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro place
  let load ops := basisPortLoader ops (by omega : 0 < d)
    (fun c : ℕ × {W : ℕ // 0 < W} => c.1+1) (fun c => c.2.val) (fun c => c.2.property)
  obtain ⟨a,both⟩ := (load left).join (load right)
  let words : Fin 2 → Fin T := ![precision,source 2]
  obtain ⟨x,start⟩ := both body basis words (by
    intro i j
    fin_cases j
    · exact precisionOff i
    · exact basisOff i 2)
  obtain ⟨b,y,finish⟩ := loadDigitPermutation_rep degree room pairs machine fits body perm source permOff
  refine ⟨a+b,x.seq y,?_⟩
  intro w W pos u S M view bank seed prec base unit width clock free vacant
  obtain ⟨v,D,t,ex,user,charge,set,off⟩ := start (w,⟨W,pos⟩) u S (by
    intro i
    fin_cases i
    · exact prec
    · exact width) free
  have keep j := (off (source j) (fun i => basisOff i j)).2
  obtain ⟨z,F,s,ey,same,paid,rep,frame⟩ := finish w W pos v D
    ((keep 0).trans base) ((keep 1).trans unit) ((keep 2).trans width)
    ((congrArg List.length (keep 3)).trans clock) (by
      intro j
      have eq := off (perm j) (fun i => disjoint i j)
      exact ⟨eq.1.trans (vacant j).1,eq.2.trans (vacant j).2⟩)
  refine ⟨z,F,t+s,ex.seq ey,same.trans user,?_,?_,rep,?_⟩
  · simpa only [Nat.add_mul] using charge.seq paid
  · intro i
    have eq := frame (basis i) (fun j => (disjoint i _).symm)
    exact ⟨eq.1.trans (set i).1,eq.2.trans (set i).2⟩
  · intro j outside away
    have f := frame j away
    have e := off j outside
    exact ⟨f.1.trans e.1,f.2.trans e.2⟩

/-- Two nested stage compositions, followed by the caller's spare tapes. -/
abbrev chartTapeCount (a b p spare : ℕ) := (1+((1+b)+p)+a)+spare

def chartSlice {n total : ℕ} (offset : ℕ) (fits : offset+n ≤ total) : Fin n ↪ Fin total where
  toFun i := ⟨offset+i.val,by have := i.isLt; omega⟩
  inj' := fun _ _ eq => Fin.ext (Nat.add_left_cancel (congrArg Fin.val eq))

/-- The left basis is the last stage executed and follows the permutation.
The right basis starts just after the two shared owner slots. -/
def chartBasisPorts (a b p spare : ℕ) : Fin (a+b) ↪ Fin (chartTapeCount a b p spare) :=
  appendPorts (chartSlice (1+((1+b)+p)) (by unfold chartTapeCount; omega))
    (chartSlice 2 (by unfold chartTapeCount; omega)) (by
      intro i j eq
      have h := congrArg Fin.val eq
      change 1+((1+b)+p)+i.val = 2+j.val at h
      omega)

/-- The permutation uses its own bank and borrows the trailing spare tapes. -/
def chartPermutationPorts (a b p spare : ℕ) : Fin (p+spare) ↪ Fin (chartTapeCount a b p spare) :=
  appendPorts (chartSlice (2+b) (by unfold chartTapeCount; omega))
    (chartSlice (1+((1+b)+p)+a) (by unfold chartTapeCount; omega)) (by
      intro i j eq
      have h := congrArg Fin.val eq
      change 2+b+i.val = 1+((1+b)+p)+a+j.val at h
      omega)

theorem chartPorts_disjoint (a b p spare : ℕ) (i j) :
    chartBasisPorts a b p spare i ≠ chartPermutationPorts a b p spare j := by
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      intro eq
      have h := congrArg Fin.val eq
      simp only [chartBasisPorts,chartPermutationPorts,appendPorts,Function.Embedding.coeFn_mk,Fin.addCases_left] at h
      change 1+((1+b)+p)+i.val = 2+b+j.val at h
      omega
    | right j =>
      intro eq
      have h := congrArg Fin.val eq
      simp only [chartBasisPorts,chartPermutationPorts,appendPorts,Function.Embedding.coeFn_mk,Fin.addCases_left,Fin.addCases_right] at h
      change 1+((1+b)+p)+i.val = 1+((1+b)+p)+a+j.val at h
      omega
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      intro eq
      have h := congrArg Fin.val eq
      simp only [chartBasisPorts,chartPermutationPorts,appendPorts,Function.Embedding.coeFn_mk,Fin.addCases_left,Fin.addCases_right] at h
      change 2+i.val = 2+b+j.val at h
      omega
    | right j =>
      intro eq
      have h := congrArg Fin.val eq
      simp only [chartBasisPorts,chartPermutationPorts,appendPorts,Function.Embedding.coeFn_mk,Fin.addCases_right] at h
      change 2+i.val = 1+((1+b)+p)+a+j.val at h
      omega

/-- The two extra owner slots introduced by composition are the first two
tapes. Together with the three loaded banks they represent the whole chart. -/
theorem chartMetadata_rep {a b p spare T : ℕ} (A : Tapes a prime) (B : Tapes b prime) (P : Tapes p prime)
    (chart : Fin (chartTapeCount a b p spare) ↪ Fin T) (F : Stacks T prime) :
    let basis := (chartBasisPorts a b p spare).trans chart
    let perm := (chartPermutationPorts a b p spare).trans chart
    let full := (Fin.castAddEmb spare).trans chart
    let read := fun {n} (bank : Tapes n prime) (port : Fin n → Fin T) => RepT bank (F.L ∘ port) (F.R ∘ port)
    (∀ i : Fin 2, F.L (chart ⟨i.val,by unfold chartTapeCount; omega⟩) = [] ∧
      F.R (chart ⟨i.val,by unfold chartTapeCount; omega⟩) = []) →
    read A (basis ∘ Fin.castAdd b) → read B (basis ∘ Fin.natAdd a) → read P (perm ∘ Fin.castAdd spare) →
    read (((SharedBank.empty 1 prime).append (((SharedBank.empty 1 prime).append B).append P)).append A) full := by
  intro basis perm full read clear repA repB repP
  apply rep_append_of_restrict
  · apply rep_append_of_restrict
    · intro i z
      obtain ⟨l,r⟩ := clear 0
      have val : i = 0 := Subsingleton.elim _ _
      subst i
      change blank = readAt blank (F.L (chart ⟨(0 : Fin 2).val,_⟩)) (F.R (chart ⟨(0 : Fin 2).val,_⟩)) _
      rw [l,r]
      simp [readAt_nil_left,wordTape_nil]
    · apply rep_append_of_restrict
      · apply rep_append_of_restrict
        · intro i z
          obtain ⟨l,r⟩ := clear 1
          have val : i = 0 := Subsingleton.elim _ _
          subst i
          change blank = readAt blank (F.L (chart ⟨(1 : Fin 2).val,_⟩)) (F.R (chart ⟨(1 : Fin 2).val,_⟩)) _
          rw [l,r]
          simp [readAt_nil_left,wordTape_nil]
        · intro i z
          have cell := repB i z
          simp only [basis,chartBasisPorts,appendPorts,Function.Embedding.trans_apply,
            Function.Embedding.coeFn_mk,Fin.addCases_right,Function.comp_apply] at cell
          have eq : full (Fin.castAdd a (Fin.natAdd 1 (Fin.castAdd p (Fin.natAdd 1 i)))) = chart (chartSlice 2 (by unfold chartTapeCount; omega) i) := by
            apply congrArg chart
            apply Fin.ext
            change 1+(1+i.val) = 2+i.val
            omega
          simpa only [Function.comp_apply,eq] using cell
      · intro i z
        have cell := repP i z
        simp only [perm,chartPermutationPorts,appendPorts,Function.Embedding.trans_apply,
          Function.Embedding.coeFn_mk,Fin.addCases_left,Function.comp_apply] at cell
        have eq : full (Fin.castAdd a (Fin.natAdd 1 (Fin.natAdd (1+b) i))) = chart (chartSlice (2+b) (by unfold chartTapeCount; omega) i) := by
          apply congrArg chart
          apply Fin.ext
          change 1+((1+b)+i.val) = (2+b)+i.val
          omega
        simpa only [Function.comp_apply,eq] using cell
  · intro i z
    have cell := repA i z
    simp only [basis,chartBasisPorts,appendPorts,Function.Embedding.trans_apply,
      Function.Embedding.coeFn_mk,Fin.addCases_left,Function.comp_apply] at cell
    have eq : full (Fin.natAdd (1+((1+b)+p)) i) = chart (chartSlice (1+((1+b)+p)) (by unfold chartTapeCount; omega) i) := by
      apply congrArg chart
      exact Fin.ext rfl
    simpa only [Function.comp_apply,eq] using cell

/-- Install the three banks at their positions in the compiled chart using
a single host embedding for the chart and its spare tapes. -/
theorem loadCompiledChartBanks {P U : Type} {T Q d spare : ℕ} (degree : 2 ≤ d) (room : 35 ≤ spare)
    (left right : List (FlatCoordinateSchedule.Op d))
    (pairs : List {p : Fin d × Fin d // p.1 < p.2})
    (machine : {p : Fin d × Fin d // p.1 < p.2} → SharedBankSkeleton.Skeleton 1 prime)
    (fits : ∀ p, 25 ≤ (machine p).tapes) (body : P → Pr P T Q prime U)
    (chart : Fin (chartTapeCount (FlatCoordinateCleanSchedule.tapeCount left)
      (FlatCoordinateCleanSchedule.tapeCount right) (digitSwapSkeleton machine pairs).tapes spare) ↪ Fin T)
    (source : Fin 4 → Fin T) (precision : Fin T)
    (external : ∀ i j, chart i ≠ source j) (precisionOff : ∀ i, chart i ≠ precision) :
    let basis := (chartBasisPorts (FlatCoordinateCleanSchedule.tapeCount left)
      (FlatCoordinateCleanSchedule.tapeCount right) (digitSwapSkeleton machine pairs).tapes spare).trans chart
    let perm := (chartPermutationPorts (FlatCoordinateCleanSchedule.tapeCount left)
      (FlatCoordinateCleanSchedule.tapeCount right) (digitSwapSkeleton machine pairs).tapes spare).trans chart
    let place := (Fin.castAddEmb spare).trans perm
    ∃ rate : ℕ, ∃ code, ∀ w W, 0 < W → ∀ u (S : Stacks T prime),
      let M := prime^(w+1)
      let view := payloadView prime d (w+1) W
      let bank := fun (p : {p : Fin d × Fin d // p.1 < p.2}) => SharedBankStageInput.raw
        (LabelCall.bank (SharedBank.empty 1 prime) view (LabelPrepare.input view d p.val.1 p.val.2 (w+1))) (machine p).tapes
      let seed := adjacentStageStacks (basisHeaderStacks left (w+1) W) (basisHeaderStacks right (w+1) W)
      S.R precision = binSyms (w+1).size (w+1) →
      S.R (source 0) = binSyms M.size M → S.R (source 1) = binSyms 1 1 →
      S.R (source 2) = binSyms W.size W → (S.R (source 3)).length = w →
      (∀ i, S.L (chart i) = [] ∧ S.R (chart i) = []) →
      ∃ z F n, Exec body code (mk u S) n (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F n (rate*(M^d*W)) ∧
        (∀ i, F.L (basis i) = seed.L i ∧ F.R (basis i) = seed.R i) ∧
        RepT (digitPermutationMetadata machine bank pairs) (F.L ∘ place) (F.R ∘ place) ∧
        ∀ j, (∀ i, basis i ≠ j) → (∀ i, place i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro basis perm place
  obtain ⟨rate,code,run⟩ := loadChartBanks degree room left right pairs machine fits body basis perm
    (fun i j => chart.injective.ne (chartPorts_disjoint _ _ _ _ i j)) source precision
    (fun i j => external _ _) (fun i => precisionOff _) (fun i j => external _ _)
  refine ⟨rate,code,?_⟩
  intro w W pos u S M view bank seed prec base unit width clock free
  exact run w W pos u S prec base unit width clock (fun i => free _) (fun i => free _)

local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- The scheduled record supplies modulus, unit, spectator count and clock.
The initialized chart leaves the same record and live payload ready to run. -/
theorem loadChartFromRecord [M8.Machine.Net] {P U : Type} {T Q d spare : ℕ} (degree : 2 ≤ d) (room : 35 ≤ spare)
    (left right : List (FlatCoordinateSchedule.Op d))
    (pairs : List {p : Fin d × Fin d // p.1 < p.2})
    (machine : {p : Fin d × Fin d // p.1 < p.2} → SharedBankSkeleton.Skeleton 1 prime)
    (fits : ∀ p, 25 ≤ (machine p).tapes) (body : P → Pr P T Q prime U)
    (chart : Fin (chartTapeCount (FlatCoordinateCleanSchedule.tapeCount left)
      (FlatCoordinateCleanSchedule.tapeCount right) (digitSwapSkeleton machine pairs).tapes spare) ↪ Fin T)
    (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (precision : Fin T)
    (external : ∀ i j, chart i ≠ ports j) (precisionOff : ∀ i, chart i ≠ precision) :
    let basis := (chartBasisPorts (FlatCoordinateCleanSchedule.tapeCount left)
      (FlatCoordinateCleanSchedule.tapeCount right) (digitSwapSkeleton machine pairs).tapes spare).trans chart
    let perm := (chartPermutationPorts (FlatCoordinateCleanSchedule.tapeCount left)
      (FlatCoordinateCleanSchedule.tapeCount right) (digitSwapSkeleton machine pairs).tapes spare).trans chart
    let place := (Fin.castAddEmb spare).trans perm
    ∃ rate : ℕ, ∃ code, ∀ w W, 0 < W → ∀ u (S : Stacks T prime),
      let M := prime^(w+1)
      let view := payloadView prime d (w+1) W
      let bank := fun (p : {p : Fin d × Fin d // p.1 < p.2}) => SharedBankStageInput.raw
        (LabelCall.bank (SharedBank.empty 1 prime) view (LabelPrepare.input view d p.val.1 p.val.2 (w+1))) (machine p).tapes
      let seed := adjacentStageStacks (basisHeaderStacks left (w+1) W) (basisHeaderStacks right (w+1) W)
      ∀ (record : List (Fin (prime+4))) (word : Fin (M^d*W) → ZMod 2),
      let ready := fun D => RecordReady (b := prime) (w := w) (d := d) (W := W) (scheduledRecordPorts ports)
        M.size W.size record SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 word D
      ready S → S.R precision = binSyms (w+1).size (w+1) →
      (∀ i, S.L (chart i) = [] ∧ S.R (chart i) = []) →
      ∃ z F n, Exec body code (mk u S) n (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F n (rate*(M^d*W)) ∧ ready F ∧
        (∀ i, F.L (basis i) = seed.L i ∧ F.R (basis i) = seed.R i) ∧
        RepT (digitPermutationMetadata machine bank pairs) (F.L ∘ place) (F.R ∘ place) ∧
        (∀ (A : Tapes (FlatCoordinateCleanSchedule.tapeCount left) prime)
            (B : Tapes (FlatCoordinateCleanSchedule.tapeCount right) prime),
          let l := basisHeaderStacks left (w+1) W
          let r := basisHeaderStacks right (w+1) W
          RepT A l.L l.R → RepT B r.L r.R →
          let metadata := (((SharedBank.empty 1 prime).append
            (((SharedBank.empty 1 prime).append B).append (digitPermutationMetadata machine bank pairs))).append A)
          let full := (Fin.castAddEmb spare).trans chart
          RepT metadata (F.L ∘ full) (F.R ∘ full)) ∧
        ∀ j, (∀ i, basis i ≠ j) → (∀ i, place i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro basis perm place
  let r := scheduledRecordPorts ports
  let source : Fin 4 → Fin T := fun i => r (![2,28,27,33] i)
  obtain ⟨rate,code,run⟩ := loadCompiledChartBanks degree room left right pairs machine fits body chart
    source precision (fun i j => external i _) precisionOff
  refine ⟨rate,code,?_⟩
  intro w W pos u S M view bank seed record word ready stored prec free
  obtain ⟨z,F,n,exec,user,paid,loaded,rep,frame⟩ := run w W pos u S prec
    stored.modulus stored.one stored.width stored.clock free
  have keep i : F.L (r i) = S.L (r i) ∧ F.R (r i) = S.R (r i) :=
    frame _ (fun j => external _ _) (fun j => external _ _)
  refine ⟨z,F,n,exec,user,paid,?_,loaded,rep,?_,frame⟩
  · apply stored.returnPayload (fun i _ => keep i)
    intro h
    rw [(keep 24).1,(keep 24).2]
    exact (stored.src h).symm
  · intro A B l r repL repR metadata full
    apply chartMetadata_rep A B (digitPermutationMetadata machine bank pairs) chart F _ _ _ rep
    · intro i
      let slot : Fin (chartTapeCount (FlatCoordinateCleanSchedule.tapeCount left) (FlatCoordinateCleanSchedule.tapeCount right) (digitSwapSkeleton machine pairs).tapes spare) := ⟨i.val,by unfold chartTapeCount; omega⟩
      have outside : ∀ j, basis j ≠ chart slot := by
        intro j
        induction j using Fin.addCases with
        | left j =>
          apply chart.injective.ne
          intro eq
          have h := congrArg Fin.val eq
          simp only [chartBasisPorts,appendPorts,Function.Embedding.coeFn_mk,Fin.addCases_left] at h
          change 1+((1+_)+_)+j.val = i.val at h
          omega
        | right j =>
          apply chart.injective.ne
          intro eq
          have h := congrArg Fin.val eq
          simp only [chartBasisPorts,appendPorts,Function.Embedding.coeFn_mk,Fin.addCases_right] at h
          change 2+j.val = i.val at h
          omega
      have away : ∀ j, place j ≠ chart slot := by
        intro j
        apply chart.injective.ne
        intro eq
        have h := congrArg Fin.val eq
        simp only [Fin.castAddEmb_apply,chartPermutationPorts,appendPorts,Function.Embedding.coeFn_mk,
          Fin.addCases_left] at h
        change (2+_)+j.val = i.val at h
        omega
      have e := frame _ outside away
      exact ⟨e.1.trans (free _).1,e.2.trans (free _).2⟩
    · intro i h
      have eq := loaded (i.castAdd _)
      simp only [adjacentStageStacks,Fin.addCases_left] at eq
      simpa only [Function.comp_apply,eq.1,eq.2] using repL i h
    · intro i h
      have eq := loaded (i.natAdd _)
      simp only [adjacentStageStacks,Fin.addCases_right] at eq
      simpa only [Function.comp_apply,eq.1,eq.2] using repR i h

/-- Bind the chart's permanent owner slot to the live row while the other
slots keep their addresses in the initialized bank. -/
def chartLivePorts {t T : ℕ} (bank : Fin t ↪ Fin T) (slot : Fin t) (owner : Fin T)
    (apart : ∀ i, bank i ≠ owner) : Fin t ↪ Fin T where
  toFun i := if i = slot then owner else bank i
  inj' := by
    intro i j eq
    by_cases hi : i = slot <;> by_cases hj : j = slot
    · exact hi.trans hj.symm
    · exact False.elim ((apart j).symm (by simpa [hi,hj] using eq))
    · exact False.elim ((apart i) (by simpa [hi,hj] using eq))
    · exact bank.injective (by simpa [hi,hj] using eq)

/-- Run a loaded chart on the caller's owner row and charge the foreign
interpreter and its stack growth. -/
theorem runLoadedPortChart {P U : Type} {T Q V : ℕ}
    (stage : SharedBankStage.Stage _ 1 prime (@portOwner V)) (capacity : stage.states ≤ Q)
    (body : P → Pr P T Q prime U) (bank : Fin stage.tapes ↪ Fin T) (owner : Fin T)
    (apart : ∀ i, bank i ≠ owner) (x : Fin V → ZMod 2) (u : HS T Q prime U) (S : Stacks T prime)
    (loaded : RepT stage.metadata (S.L ∘ bank) (S.R ∘ bank))
    (row : ∀ h, readAt blank (S.L owner) (S.R owner) h = (portOwner x).tape 0 h) :
    let live := chartLivePorts bank (stage.slots 0) owner apart
    ∃ z F n, Exec body (embProg live Empty.elim (foreign (liftQ stage.program capacity)))
      (mk u S) n (mk z F) ∧ z.user = u.user ∧
      CleanupBound S F n (13*(stage.cost*(stage.tapes+5)+6)) ∧
      (∀ h, readAt blank (F.L owner) (F.R owner) h = (portOwner (stage.transform x)).tape 0 h) ∧
      ∀ j, j ≠ owner → (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro live
  have atOwner : live (stage.slots 0) = owner := by simp [live,chartLivePorts]
  have input : RepT (stage.input x) (embStk live S).L (embStk live S).R := by
    intro i h
    by_cases hit : i = stage.slots 0
    · subst i
      have tape := congrArg (fun v : Tapes 1 prime => v.tape 0 h) (stage.input_payload x)
      have head := congrArg (fun v : Tapes 1 prime => v.head 0) (stage.input_payload x)
      change _ = readAt blank (S.L (live _)) (S.R (live _)) _
      change (stage.input x).head _ = 0 at head
      rw [atOwner,head,sub_zero,row]
      exact tape
    · have unused : ¬ ∃ k, stage.slots k = i := fun ⟨k,eq⟩ => hit ((Subsingleton.elim k 0) ▸ eq.symm)
      have tape := congrArg (fun v : Tapes stage.tapes prime => v.tape i h) (stage.strip_input x)
      have head := congrArg (fun v : Tapes stage.tapes prime => v.head i) (stage.strip_input x)
      simp only [SharedBank.strip,unused,ite_false] at tape head
      simpa only [embStk,Function.comp_apply,live,chartLivePorts,Function.Embedding.coeFn_mk,
        ite_eq_right hit,tape,head] using loaded i h
  obtain ⟨v,D,_,rfl,rep,user,_,_,_,n,time,run⟩ := foreign_exec (P := Empty) Empty.elim _
    (HoareTime.liftQ capacity (stage.realizes x)) (embDn live u) (embStk live S) _ rfl input
  obtain ⟨z,F,exec,_,same,projection,off⟩ := exec_emb (ι := Empty.elim) (body' := body) live.injective
    (fun f => nomatch f) run u rfl S rfl
  refine ⟨z,F,n,exec,same.trans user,?_,?_,?_⟩
  · intro js unique
    exact (foreignCleanupBound exec js unique).trans (Nat.add_le_add_left (Nat.mul_le_mul_left 13 time) _)
  · intro h
    have cell := rep (stage.slots 0) h
    have tape := congrArg (fun v : Tapes 1 prime => v.tape 0 h) (stage.output_payload x)
    have head := congrArg (fun v : Tapes 1 prime => v.head 0) (stage.output_payload x)
    change (stage.output x).head _ = 0 at head
    rw [← projection] at cell
    simpa only [embStk,Function.comp_apply,atOwner,head,sub_zero] using cell.symm.trans tape
  · intro j ne away
    apply off
    intro i
    by_cases hit : i = stage.slots 0
    · simpa [hit,atOwner] using ne.symm
    · simpa [live,chartLivePorts,hit] using away i

private theorem portOwner_record {V : ℕ} (x : Fin V → ZMod 2) (h : ℤ) :
    (portOwner x).tape 0 h = RadixToBinary.binaryEncoding.encode
      (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ x)) h) := by
  change _ = FlatRepeatedControlNormalize.encoded (radix := prime) (putWord _ 0 _) h
  rw [RecursiveRoleSerialization.encoded_word,List.map_ofFn]
  rfl

/-- Execute a prepared one-owner chart directly on slot 24 of a scheduled
child record. Its headers and archive remain ready with the transformed row. -/
theorem runRecordPortChart {P U : Type} {T Q w W d : ℕ}
    (stage : SharedBankStage.Stage _ 1 prime (@portOwner ((prime^(w+1))^d*W)))
    (capacity : stage.states ≤ Q) (body : P → Pr P T Q prime U)
    (bank : Fin stage.tapes ↪ Fin T) (r : Fin 35 ↪ Fin T) (apart : ∀ i j, bank i ≠ r j)
    (record : List (Fin (prime+4))) (x : Fin ((prime^(w+1))^d*W) → ZMod 2)
    (u : HS T Q prime U) (S : Stacks T prime) (loaded : RepT stage.metadata (S.L ∘ bank) (S.R ∘ bank)) :
    let M := prime^(w+1)
    let ready := fun y D => RecordReady (b := prime) (w := w) (d := d) (W := W) r M.size W.size
      record SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 y D
    let live := chartLivePorts bank (stage.slots 0) (r 24) (fun i => apart i 24)
    ready x S → ∃ z F n, Exec body (embProg live Empty.elim (foreign (liftQ stage.program capacity)))
      (mk u S) n (mk z F) ∧ z.user = u.user ∧ CleanupBound S F n (13*(stage.cost*(stage.tapes+5)+6)) ∧
      ready (stage.transform x) F ∧
      ∀ j, j ≠ r 24 → (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro M ready live stored
  obtain ⟨z,F,n,exec,user,paid,out,off⟩ := runLoadedPortChart stage capacity body bank (r 24)
    (fun i => apart i 24) x u S loaded (fun h => by
      rw [portOwner_record]
      simpa only [sub_zero] using stored.src h)
  refine ⟨z,F,n,exec,user,paid,stored.returnPayload (fun i ne => off _ (r.injective.ne ne) (fun j => apart j i)) ?_,off⟩
  intro h
  simpa only [sub_zero,portOwner_record] using (out h).symm

/-- Transport the loader's representation to the actual composed stage.
The only size casts come from the two basis schedules and the fold of swaps. -/
theorem loadedChartStage_rep {d V T l r : ℕ}
    (a b : SharedBankStage.Stage _ 1 prime (@portOwner V))
    (swaps : {p : Fin d × Fin d // p.1 < p.2} → SharedBankStage.Stage _ 1 prime (@portOwner V))
    (pairs : List {p : Fin d × Fin d // p.1 < p.2})
    (machine : {p : Fin d × Fin d // p.1 < p.2} → SharedBankSkeleton.Skeleton 1 prime)
    (fixed : ∀ p, SharedBankSkeleton.ofStage (swaps p) = machine p)
    (raw : {p : Fin d × Fin d // p.1 < p.2} → (n : ℕ) → Tapes n prime)
    (privateBank : ∀ p, (swaps p).metadata = raw p (swaps p).tapes)
    (la : a.tapes = l) (rb : b.tapes = r) (L : Stacks l prime) (R : Stacks r prime)
    (left : RepT a.metadata (L.L ∘ Fin.cast la) (L.R ∘ Fin.cast la))
    (right : RepT b.metadata (R.L ∘ Fin.cast rb) (R.R ∘ Fin.cast rb))
    (full : Fin (1+(1+r+(digitSwapSkeleton machine pairs).tapes)+l) ↪ Fin T) (F : Stacks T prime)
    (loaded : ∀ (A : Tapes l prime) (B : Tapes r prime), RepT A L.L L.R → RepT B R.L R.R →
      RepT (((SharedBank.empty 1 prime).append (((SharedBank.empty 1 prime).append B).append
        (digitPermutationMetadata machine (fun p => raw p (machine p).tapes) pairs))).append A)
        (F.L ∘ full) (F.R ∘ full)) :
    let stage := SharedBankStage.compose (SharedBankStage.compose b (digitSwapStage swaps pairs)) a
    ∃ size : stage.tapes = 1+(1+r+(digitSwapSkeleton machine pairs).tapes)+l,
      RepT stage.metadata (F.L ∘ full ∘ Fin.cast size) (F.R ∘ full ∘ Fin.cast size) := by
  subst l r
  have eq := funext fixed
  subst machine
  have rep := loaded a.metadata b.metadata left right
  have banks := funext privateBank
  have data := digitSwapStage_metadata swaps pairs
  rw [banks] at data
  have dims : (digitSwapStage swaps pairs).tapes =
      (digitSwapSkeleton (fun p => SharedBankSkeleton.ofStage (swaps p)) pairs).tapes := by
    clear rep loaded data full
    induction pairs with
    | nil => rfl
    | cons p ps ih => exact congrArg (fun n => 1+n+(swaps p).tapes) ih
  have transport {m n : ℕ} (eq : m = n) {pm : Tapes m prime} {qm : Tapes n prime} (same : HEq pm qm)
      (place : Fin (1+(1+b.tapes+n)+a.tapes) ↪ Fin T) :
      let metaBank := fun {k} (v : Tapes k prime) =>
        ((SharedBank.empty 1 prime).append (((SharedBank.empty 1 prime).append b.metadata).append v)).append a.metadata
      RepT (metaBank qm) (F.L ∘ place) (F.R ∘ place) →
        RepT (metaBank pm) (F.L ∘ place ∘ Fin.cast (congrArg (fun k => 1+(1+b.tapes+k)+a.tapes) eq))
          (F.R ∘ place ∘ Fin.cast (congrArg (fun k => 1+(1+b.tapes+k)+a.tapes) eq)) := by
    cases eq
    cases eq_of_heq same
    exact fun h => h
  exact ⟨_,transport dims data full rep⟩

/-- Charged initialization, hosted execution and erasure of the chart bank. -/
noncomputable def recordChartCost [M8.Machine.Net] (rate c k tapes w V : ℕ) : ℕ :=
  rate*V+13*((c*V+k*(3808274*V+LeafCore.coreCost V w+1)+2)*(tapes+5)+6)+4*(tapes+35)+1

theorem recordChartCost_bound [M8.Machine.Net] (rate c k tapes : ℕ) :
    ∃ C : ℝ, ∀ w V : ℕ, 0 < w → 0 < V →
      (recordChartCost rate c k tapes w V : ℝ) ≤ C*V*(w : ℝ)^M8.Machine.BudgetBound.tau := by
  refine ⟨rate+13*((c+k*(3808275+|LeafCore.C|)+2)*(tapes+5)+6)+4*(tapes+35)+1,?_⟩
  intro w V hw hv
  let power := (w : ℝ)^M8.Machine.BudgetBound.tau
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast hw) M8.Machine.BudgetBound.exponent_range.1.le
  have vol : (V : ℝ) ≤ V*power := le_mul_of_one_le_right (Nat.cast_nonneg _) one
  have unit : 1 ≤ (V : ℝ)*power := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hv) one
  have core := RevBudget.coreCost_le V w (L := power) (by rw [max_eq_right hw])
  have swap : 3808274*(V : ℝ)+LeafCore.coreCost V w+1 ≤ (3808275+|LeafCore.C|)*(V*power) := by
    linarith only [core,vol,unit]
  have stage : (c : ℝ)*V+k*(3808274*(V : ℝ)+LeafCore.coreCost V w+1)+2 ≤
      (c+k*(3808275+|LeafCore.C|)+2)*(V*power) := by
    linarith only [mul_le_mul_of_nonneg_left vol (Nat.cast_nonneg c),
      mul_le_mul_of_nonneg_left swap (Nat.cast_nonneg k),unit]
  unfold recordChartCost
  push_cast
  change _ ≤ _*(V : ℝ)*power
  linarith only [mul_le_mul_of_nonneg_left vol (Nat.cast_nonneg rate),
    mul_le_mul_of_nonneg_right stage (show (0 : ℝ) ≤ tapes+5 by positivity),
    mul_le_mul_of_nonneg_left unit (show (0 : ℝ) ≤ 4*(tapes+35)+79 by positivity)]

/-- Runtime contract for a chart on the live child row, including initialization,
cleanup charges and preservation outside the chart and owner. -/
def RunsRecordChart [M8.Machine.Net] (d : ℕ)
    (effect : ∀ w W : ℕ, (Fin ((prime^(w+1))^d*W) → ZMod 2) → (Fin ((prime^(w+1))^d*W) → ZMod 2) → Prop) : Prop :=
    ∃ (machine : SharedBankSkeleton.Skeleton 1 prime) (c k : ℕ),
      ∀ {P User : Type} {T Q : ℕ} (body : P → Pr P T Q prime User) (_capacity : machine.states ≤ Q)
        (chart : Fin (machine.tapes+35) ↪ Fin T) (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T)
        (precision : Fin T), (∀ i j, chart i ≠ ports j) → (∀ i, chart i ≠ precision) →
      ∃ (rate : ℕ) (code : Pr P T Q prime User), ∀ w W, 0 < W → ∀ u (S : Stacks T prime),
        let M := prime^(w+1)
        let V := M^d*W
        ∀ (record : List (Fin (prime+4))) (x : Fin V → ZMod 2),
        let ready := fun y D => RecordReady (b := prime) (w := w) (d := d) (W := W) (scheduledRecordPorts ports)
          M.size W.size record SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 y D
        ready x S → S.R precision = binSyms (w+1).size (w+1) →
        (∀ i, S.L (chart i) = [] ∧ S.R (chart i) = []) →
        ∃ z F n y, Exec body code (mk u S) n (mk z F) ∧ z.user = u.user ∧
          CleanupBound S F n (recordChartCost rate c k machine.tapes (w+1) V) ∧
          ready y F ∧ effect w W x y ∧
          ∀ j, j ≠ scheduledRecordPorts ports 24 → F.L j = S.L j ∧ F.R j = S.R j

theorem RunsRecordChart.implies [M8.Machine.Net] {d : ℕ} {effect result}
    (run : RunsRecordChart d effect) (imp : ∀ w W x y, effect w W x y → result w W x y) :
    RunsRecordChart d result := by
  obtain ⟨machine,c,k,build⟩ := run
  refine ⟨machine,c,k,?_⟩
  intro P User T Q body capacity chart ports precision apart outside
  obtain ⟨rate,code,exec⟩ := build body capacity chart ports precision apart outside
  refine ⟨rate,code,?_⟩
  intro w W pos u S M V record x ready stored prec free
  obtain ⟨z,F,n,y,e,user,bill,out,action,off⟩ := exec w W pos u S record x stored prec free
  exact ⟨z,F,n,y,e,user,bill,out,imp w W x y action,off⟩

open Matrix IntegerMultBounds.Swap.Modular in
/-- Initialize and execute either direction of a bounded chart on the scheduled record.
The swap list, basis schedules and compiled skeleton are fixed across widths. -/
theorem initializedRecordChart [M8.Machine.Net] {d : ℕ} (U : Matrix (Fin d) (Fin d) ℚ)
    (unit : IsUnit U) (degree : 2 ≤ d) (bound : d ≤ 529)
    (entries : ∀ i j, (U i j).num.natAbs ≤ 10^10000 ∧ (U i j).den ≤ 10^10000) (backward : Bool := false) :
    RunsRecordChart d (fun w _ x y => ∀ v j, routedCell backward x y (FlatCoordinateLayout.index v j)
      (FlatCoordinateLayout.index (reduce (prime^(w+1)) U *ᵥ v) j)) := by
  obtain ⟨left,right,pairs,ma,mb,swaps,build⟩ := flatChart_withHeaders U unit (by omega) bound entries backward
  let machine := SharedBankSkeleton.compose (SharedBankSkeleton.compose mb (digitSwapSkeleton swaps pairs)) ma
  obtain ⟨a₀,b₀,leaf₀,⟨la₀,_⟩,⟨rb₀,_⟩,meta₀,fa₀,fb₀,_⟩ := build 1 1 (by decide) (by decide)
  have la : ma.tapes = FlatCoordinateCleanSchedule.tapeCount left :=
    (congrArg SharedBankSkeleton.Skeleton.tapes fa₀).symm.trans la₀
  have rb : mb.tapes = FlatCoordinateCleanSchedule.tapeCount right :=
    (congrArg SharedBankSkeleton.Skeleton.tapes fb₀).symm.trans rb₀
  have fits p : 25 ≤ (swaps p).tapes :=
    (meta₀ p).2.1.trans (congrArg SharedBankSkeleton.Skeleton.tapes (meta₀ p).1).le
  refine ⟨machine,FlatCoordinateCleanSchedule.constant left + FlatCoordinateCleanSchedule.constant right,pairs.length,?_⟩
  intro P User T Q body capacity chart ports precision external precOff
  let shape := chartTapeCount (FlatCoordinateCleanSchedule.tapeCount left)
    (FlatCoordinateCleanSchedule.tapeCount right) (digitSwapSkeleton swaps pairs).tapes 35
  have dims : shape = machine.tapes+35 := by
    change 1+(1+_+_)+_+35 = 1+(1+mb.tapes+_)+ma.tapes+35
    rw [la,rb]
  let bank := (Fin.castLEEmb dims.le).trans chart
  obtain ⟨rate,load,init⟩ := loadChartFromRecord degree (by decide : 35 ≤ 35) left right pairs swaps fits
    body bank ports precision (fun i j => external _ _) (fun i => precOff _)
  let r := scheduledRecordPorts ports
  let full := (Fin.castAddEmb 35).trans chart
  let live := chartLivePorts full (machine.slots 0) (r 24) (fun _ => external _ _)
  let work := (List.finRange (machine.tapes+35)).map chart
  have distinct : work.Nodup := (List.nodup_finRange _).map chart.injective
  refine ⟨rate,(load.seq (embProg live Empty.elim (foreign (liftQ machine.program capacity)))).seq
    (clearWorkTapes work),?_⟩
  intro w W pos u S M V record x ready stored prec free
  obtain ⟨v,D,t,start,user,charged,readyD,_,_,loaded,keep⟩ :=
    init w W pos u S record x stored prec (fun i => free _)
  obtain ⟨a,b,leaf,⟨sa,repA⟩,⟨sb,repB⟩,metadata,_,_,fixed,cost,action⟩ := build (w+1) W (by omega) pos
  let stage := SharedBankStage.compose (SharedBankStage.compose b (digitSwapStage leaf pairs)) a
  let raw := fun (p : {p : Fin d × Fin d // p.1 < p.2}) n => SharedBankStageInput.raw
    (LabelCall.bank (SharedBank.empty 1 prime) (payloadView prime d (w+1) W)
      (LabelPrepare.input (payloadView prime d (w+1) W) d p.val.1 p.val.2 (w+1))) n
  obtain ⟨size,rep⟩ := loadedChartStage_rep a b leaf pairs swaps (fun p => (metadata p).1) raw
    (fun p => (metadata p).2.2) sa sb _ _ repA repB _ D loaded
  have same : SharedBankSkeleton.ofStage stage = machine := fixed
  have run (m : SharedBankSkeleton.Skeleton 1 prime) (eq : SharedBankSkeleton.ofStage stage = m)
      (cap : m.states ≤ Q) (place : Fin m.tapes ↪ Fin T) (away : ∀ i j, place i ≠ r j)
      (stock : RepT stage.metadata (D.L ∘ place ∘ Fin.cast (congrArg SharedBankSkeleton.Skeleton.tapes eq))
        (D.R ∘ place ∘ Fin.cast (congrArg SharedBankSkeleton.Skeleton.tapes eq))) :
      ∃ z F n, Exec body (embProg (chartLivePorts place (m.slots 0) (r 24) (fun i => away i 24))
        Empty.elim (foreign (liftQ m.program cap))) (mk v D) n (mk z F) ∧ z.user = v.user ∧
        CleanupBound D F n (13*(stage.cost*(stage.tapes+5)+6)) ∧
        RecordReady (b := prime) (w := w) (d := d) (W := W) r M.size W.size record SparseRoleCircuit.encode
          (fun _ => blank) (fun _ => blank) 0 0 (stage.transform x) F ∧
        ∀ j, j ≠ r 24 → (∀ i, place i ≠ j) → F.L j = D.L j ∧ F.R j = D.R j :=
    by
      subst m
      exact runRecordPortChart stage cap body place r away record x v D stock readyD
  obtain ⟨z,F,n,exec,last,bill,out,off⟩ := run machine same capacity full (fun _ _ => external _ _) (by
    intro i h
    have cell := rep i h
    have eq : full (i.cast (congrArg SharedBankSkeleton.Skeleton.tapes same)) =
        bank ((i.cast size).castAdd 35) := congrArg chart (Fin.ext rfl)
    change stage.metadata.tape i h = readAt blank (D.L (full (i.cast _))) (D.R (full (i.cast _))) _
    exact cell.trans (congrArg (fun j => readAt blank (D.L j) (D.R j) (h-stage.metadata.head i)) eq.symm))
  obtain ⟨u',final,clear⟩ := clearWorkTapes_exec body work distinct z F
  let G := {F with L := fun j => if j ∈ work then [] else F.L j,
                   R := fun j => if j ∈ work then [] else F.R j}
  have blankAt j (inside : j ∈ work) : G.L j = [] ∧ G.R j = [] := by simp [G,inside]
  have recordOff i : r i ∉ work := by
    intro mem
    obtain ⟨h,_,eq⟩ := List.mem_map.mp mem
    exact external h _ eq
  have retained i : G.L (r i) = F.L (r i) ∧ G.R (r i) = F.R (r i) := by simp [G,recordOff]
  refine ⟨u',G,_,stage.transform x,(start.seq exec).seq clear,final.trans (last.trans user),?_,?_,action x,?_⟩
  · have paid := cleanupBound_clearBank work distinct (charged.seq bill)
      (le_refl (tapeCharge cleanupWeight work F+1)) blankAt
      (fun j => by by_cases h : j ∈ work <;> simp [G,h])
    have stock : tapeCharge cleanupWeight work S = 4*(machine.tapes+35) := by
      unfold tapeCharge
      rw [List.map_congr_left (g := fun _ => 4) (by
        intro j mem
        obtain ⟨i,_,rfl⟩ := List.mem_map.mp mem
        simp [cleanupWeight,(free i).1,(free i).2])]
      rw [List.map_const']
      simp [work,Nat.mul_comm]
    have tape := congrArg SharedBankSkeleton.Skeleton.tapes same
    change stage.tapes = machine.tapes at tape
    change stage.cost = _ at cost
    rw [cost,tape,stock] at paid
    exact paid
  · apply out.returnPayload (fun i _ => retained i)
    intro h
    rw [(retained 24).1,(retained 24).2]
    exact (out.src h).symm
  · intro j ne
    by_cases mem : j ∈ work
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp mem
      exact ⟨(blankAt _ mem).1.trans (free i).1.symm,(blankAt _ mem).2.trans (free i).2.symm⟩
    · have outside i : chart i ≠ j := fun eq => mem (List.mem_map.mpr ⟨i,List.mem_finRange _,eq⟩)
      have f := off j ne (fun _ => outside _)
      have e := keep j (fun _ => outside _) (fun _ => outside _)
      simpa only [G,ite_eq_right mem] using And.intro (f.1.trans e.1) (f.2.trans e.2)

open Matrix IntegerMultBounds.Swap.Modular Certificates.PR589 Certificates.PR589.Nine in
theorem initializedPairedChart [M8.Machine.Net] {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι Axis ℚ) (J : Matrix Axis ι ℚ) (hJ : H*J = 1)
    {height : ℕ} (bounded : ∀ i j, (H i j).num.natAbs ≤ height ∧ (H i j).den ≤ height)
    (order : Fin 128 ≃ ι ⊕ ι) (backward : Bool) (height_le : height ≤ 10^10000) :
    RunsRecordChart 128 (fun w _ x y => ∀ (s : Swap.Shear.State Axis (ZMod (prime^(w+1)))) j,
      routedCell backward x y (FlatCoordinateLayout.index (Sum.elim s.1 s.2 ∘ flatParentOrder) j)
        (FlatCoordinateLayout.index (Sum.elim (reduce (prime^(w+1)) H *ᵥ s.1)
          (reduce (prime^(w+1)) H *ᵥ s.2) ∘ order) j)) := by
  let D := fromBlocks H 0 0 H
  let U := D.submatrix order flatParentOrder
  let inv := (fromBlocks J 0 0 J).submatrix flatParentOrder order
  have cancel : U*inv = 1 := by
    dsimp only [U,inv]
    rw [submatrix_mul_equiv]
    simp [D,fromBlocks_multiply,hJ,submatrix_one_equiv]
  have entries (i j) : (U i j).num.natAbs ≤ 10^10000 ∧ (U i j).den ≤ 10^10000 := by
    change ((fromBlocks H 0 0 H) (order i) (flatParentOrder j)).num.natAbs ≤ _ ∧ _
    dsimp only [U,D,submatrix_apply]
    cases order i <;> cases flatParentOrder j
    all_goals first
      | exact ⟨(bounded _ _).1.trans height_le,(bounded _ _).2.trans height_le⟩
      | exact ⟨Nat.zero_le _, Nat.one_le_pow 10000 10 (by decide)⟩
  apply (initializedRecordChart U (isUnit_iff_exists.mpr ⟨_,cancel,mul_eq_one_comm.mp cancel⟩)
    (by decide) (by decide) entries backward).implies
  intro w W x y read s j
  let F := reduce (prime^(w+1)) H
  have mat : reduce (prime^(w+1)) U = (fromBlocks F 0 0 F).submatrix order flatParentOrder := by
    ext i j
    change ratMod _ (D (order i) (flatParentOrder j)) = (fromBlocks F 0 0 F) _ _
    cases order i <;> cases flatParentOrder j <;> first | rfl | exact ratMod_zero _
  have action : reduce (prime^(w+1)) U *ᵥ (Sum.elim s.1 s.2 ∘ flatParentOrder) = (Sum.elim (F *ᵥ s.1) (F *ᵥ s.2) ∘ order) := by
    rw [mat,submatrix_mulVec_equiv]
    simp [Function.comp_assoc,fromBlocks_mulVec,F]
  rw [← action]
  exact read _ j

open Certificates.PR589 Certificates.PR589.Nine in
/-- Both directions of a certified PR589 helper slot on the live record row. -/
theorem initializedHelperChart [M8.Machine.Net] (c : PortCertificate) (hc : c.Checked)
    (slot : Option (Fin 56)) (backward : Bool) :
    RunsRecordChart 128 (fun w _ x y => ∀ (s : Swap.Shear.State Axis (ZMod (prime^(w+1)))) j,
      routedCell backward x y (FlatCoordinateLayout.index (Sum.elim s.1 s.2 ∘ flatParentOrder) j)
        (FlatCoordinateLayout.index (helperSlotField c slot (w+1) s) j)) := by
  exact initializedPairedChart (height := 2) c.fullChart.transpose c.fullChart (c.fullChart_orthonormal hc)
    (fun i j => fullChart_entry c hc j i) (helperFieldOrder slot) backward
    ((by decide : 2 ≤ 10^1).trans (pow_le_pow_right₀ (by decide : 1 ≤ (10:ℕ)) (by decide)))

open Certificates.PR589 Certificates.PR589.Nine in
/-- Initialize and execute the selected sweep address change on any role.
On active roles the paired chart also performs the local polynomial shift. -/
theorem initializedSweepChart [M8.Machine.Net] (n : Fin 9) (r : Role) (backward : Bool) :
    RunsRecordChart 128 (fun w W x y => ∀ i, routedCell backward x y i
      ((flatToSweep (w+1) W n r i).cast
        (by simpa only [Nat.one_mul] using ordinaryCompact_width (prime^(w+1)) W))) := by
  by_cases active : r.bank.val / 2 = BitHosting.activePair n.val
  · obtain ⟨H,J,inverse,height,dst⟩ := activeSweepChartMatrix n r active
    apply (initializedPairedChart H J inverse height helperDigits backward le_rfl).implies
    intro w W x y read i
    obtain ⟨⟨s,j⟩,rfl⟩ := (flatWindowEquiv (w+1) W).surjective i
    rw [dst]
    exact read s j
  · apply (initializedHelperChart (port r.port.val) (port_checked _ r.port.isLt) none backward).implies
    intro w W x y read i
    obtain ⟨⟨s,j⟩,rfl⟩ := (flatWindowEquiv (w+1) W).surjective i
    simp only [flatToSweep,Equiv.trans_apply,Equiv.symm_apply_apply,sweepRoleEquiv,active,↓reduceIte]
    let cell := FlatCoordinateLayout.index (helperSlotField (port r.port.val) none (w+1) s) j
    change routedCell backward x y _ ((stagedOwnerIndex (0 : Fin 1) cell).cast _)
    have same : (stagedOwnerIndex (0 : Fin 1) cell).cast
        (by simpa only [Nat.one_mul] using ordinaryCompact_width (prime^(w+1)) W) = cell :=
      Fin.ext (staged_single_val cell)
    rw [same]
    exact read s j

end IntegerMultBounds.MathlibTM2.M6.BitNode
