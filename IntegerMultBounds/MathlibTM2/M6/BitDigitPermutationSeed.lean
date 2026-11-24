module

public import IntegerMultBounds.MathlibTM2.M6.BitBasisWorkerSeed
public import IntegerMultBounds.MathlibTM2.M6.BitFlatChartRun

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

open Cover RecursiveInterchangeLayout M8.RevMachine in
/-- The chart uses these same initialized swap stages for its address action
and its bill. The word and all tape programs are fixed before precision is supplied. -/
theorem digitPermutation_owner [M8.Machine.Net] {d : ℕ}
    (pairs : List {p : Fin d × Fin d // p.1 < p.2}) :
    ∃ machine : {p : Fin d × Fin d // p.1 < p.2} → SharedBankSkeleton.Skeleton 1 prime,
      ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^d*W
      ∃ stage : {p : Fin d × Fin d // p.1 < p.2} → SharedBankStage.Stage _ 1 prime (@portOwner V),
        (∀ p, SharedBankSkeleton.ofStage (stage p) = machine p ∧ 25 ≤ (stage p).tapes ∧
          (stage p).metadata = SharedBankStageInput.raw
            (LabelCall.bank (SharedBank.empty 1 prime) (payloadView prime d w W)
              (LabelPrepare.input (payloadView prime d w W) d p.val.1 p.val.2 w)) (stage p).tapes) ∧
        SharedBankSkeleton.ofStage (digitSwapStage stage pairs) = digitSwapSkeleton machine pairs ∧
        (digitSwapStage stage pairs).cost = pairs.length*(3808274*V + LeafCore.coreCost V w + 1) ∧
        ∀ x a j, (digitSwapStage stage pairs).transform x
          (FlatCoordinateLayout.index (a ∘ digitSwapPermutation pairs) j) =
          x (FlatCoordinateLayout.index a j) := by
  classical
  choose machine build using fun p : {p : Fin d × Fin d // p.1 < p.2} =>
    digitSwap_view_owner_cost p.val.1 p.val.2 p.property (fun w W => LeafCore.coreCost ((prime^w)^d*W) w) (by
      intro w W hw hW u
      have size : volume prime u = (prime^w)^d*W := swapView_volume _ _ p.property
      have positive : u.Positive := LeafCore.positive_of_volume
        (size ▸ Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW)
      simpa only [size,show u.width = w from rfl] using LeafCore.cost_le positive)
  refine ⟨machine,?_⟩
  intro w W hw hW V
  choose stage fixed cost metadata swap using fun p => build p w W hw hW
  obtain ⟨skeleton,paid,action⟩ := digitSwapStage_run stage _ cost (fun p x a j => by
    simpa only [ext_apply] using swapView_apply _ _ p.property (swap p x) a j) pairs
  exact ⟨stage,fun p => ⟨fixed p,(metadata p).1,(metadata p).2.2⟩,
    skeleton.trans (congrArg (fun m => digitSwapSkeleton m pairs) (funext fixed)),paid,action⟩

open Matrix Cover RecursiveInterchangeLayout IntegerMultBounds.Swap.Modular M8.RevMachine in
/-- Factor a chart with both basis headers and every digit-swap bank exposed
on the stages that execute the factorization. -/
theorem flatChart_withHeaders [M8.Machine.Net] {d : ℕ} (U : Matrix (Fin d) (Fin d) ℚ)
    (unit : IsUnit U) (pos : 1 ≤ d) (bound : d ≤ 529)
    (entries : ∀ i j, (U i j).num.natAbs ≤ 10^10000 ∧ (U i j).den ≤ 10^10000) :
    ∃ (left right : List (FlatCoordinateSchedule.Op d))
      (pairs : List {p : Fin d × Fin d // p.1 < p.2})
      (ma mb : SharedBankSkeleton.Skeleton 1 prime)
      (machine : {p : Fin d × Fin d // p.1 < p.2} → SharedBankSkeleton.Skeleton 1 prime),
      ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^d*W
      let Stage := SharedBankStage.Stage _ 1 prime (@portOwner V)
      let headers := fun (s : Stage) (ops : List (FlatCoordinateSchedule.Op d)) => ∃ size : s.tapes = FlatCoordinateCleanSchedule.tapeCount ops,
        let seed := basisHeaderStacks ops w W
        RepT s.metadata (seed.L ∘ Fin.cast size) (seed.R ∘ Fin.cast size)
      ∃ (a b : Stage) (swaps : {p : Fin d × Fin d // p.1 < p.2} → Stage),
        let chart := SharedBankStage.compose (SharedBankStage.compose b (digitSwapStage swaps pairs)) a
        headers a left ∧ headers b right ∧
        (∀ p, SharedBankSkeleton.ofStage (swaps p) = machine p ∧ 25 ≤ (swaps p).tapes ∧
          (swaps p).metadata = SharedBankStageInput.raw
            (LabelCall.bank (SharedBank.empty 1 prime) (payloadView prime d w W)
              (LabelPrepare.input (payloadView prime d w W) d p.val.1 p.val.2 w)) (swaps p).tapes) ∧
        SharedBankSkeleton.ofStage a = ma ∧ SharedBankSkeleton.ofStage b = mb ∧
        SharedBankSkeleton.ofStage chart = SharedBankSkeleton.compose
          (SharedBankSkeleton.compose mb (digitSwapSkeleton machine pairs)) ma ∧
        chart.cost = (FlatCoordinateCleanSchedule.constant left + FlatCoordinateCleanSchedule.constant right)*V +
          pairs.length*(3808274*V + LeafCore.coreCost V w + 1) + 2 ∧
        ∀ x v j, chart.transform x (FlatCoordinateLayout.index (reduce (prime^w) U *ᵥ v) j) =
          x (FlatCoordinateLayout.index v j) := by
  obtain ⟨A,B,π,factors,action⟩ := chartFactors U unit pos bound entries
  obtain ⟨pairs,rfl⟩ := exists_digitSwapPairs π
  have left := factors A (by simp)
  have right := factors B (by simp)
  obtain ⟨opsA,ma,runA⟩ := triangularPort_withHeaders A left.1 left.2 false
  obtain ⟨opsB,mb,runB⟩ := triangularPort_withHeaders B right.1 right.2 false
  obtain ⟨machine,runP⟩ := digitPermutation_owner pairs
  refine ⟨opsA,opsB,pairs,ma,mb,machine,?_⟩
  intro w W hw hW V Stage headers
  obtain ⟨a,fa,ta,sa,readA⟩ := runA w W hW
  obtain ⟨b,fb,tb,sb,readB⟩ := runB w W hW
  obtain ⟨swaps,metadata,fp,tp,readP⟩ := runP w W hw hW
  refine ⟨a,b,swaps,sa,sb,metadata,fa,fb,?_,?_,?_⟩
  · simp only [SharedBankSkeleton.ofStage_compose,fa,fb,fp]
  · change b.cost+(digitSwapStage swaps pairs).cost+1+a.cost+1 = _
    rw [ta,tb,tp]; ring
  · intro x v j
    rw [action]
    exact (readA _ _ j).trans ((readP _ _ j).trans (readB x v j))

/-- The shared slots introduced by composition are empty. All other
metadata belongs to a particular occurrence of a swap. -/
noncomputable def digitPermutationMetadata {d : ℕ}
    (machine : {p : Fin d × Fin d // p.1 < p.2} → SharedBankSkeleton.Skeleton 1 prime)
    (bank : ∀ p, Tapes (machine p).tapes prime)
    (pairs : List {p : Fin d × Fin d // p.1 < p.2}) : Tapes (digitSwapSkeleton machine pairs).tapes prime :=
  match pairs with
  | [] => SharedBank.empty 1 prime
  | p :: ps => ((SharedBank.empty 1 prime).append (digitPermutationMetadata machine bank ps)).append (bank p)

theorem digitSwapStage_metadata {d V : ℕ}
    (stage : {p : Fin d × Fin d // p.1 < p.2} → SharedBankStage.Stage _ 1 prime (@portOwner V))
    (pairs : List {p : Fin d × Fin d // p.1 < p.2}) :
    HEq (digitSwapStage stage pairs).metadata (digitPermutationMetadata
      (fun p => SharedBankSkeleton.ofStage (stage p)) (fun p => (stage p).metadata) pairs) := by
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
    have append {n m : ℕ} {a : Tapes n prime} {b : Tapes m prime}
        (size : n = m) (eq : HEq a b) :
        HEq (((SharedBank.empty 1 prime).append a).append (stage p).metadata)
          (((SharedBank.empty 1 prime).append b).append (stage p).metadata) := by
      cases size
      cases eq_of_heq eq
      rfl
    apply append _ ih
    clear ih
    induction ps with
    | nil => rfl
    | cons q qs h =>
      exact congrArg (fun n => 1+n+(stage q).tapes) h

theorem rep_append_of_restrict {n m : ℕ} (a : Tapes n prime) (b : Tapes m prime)
    (L R : Fin (n+m) → List (Fin (prime+4)))
    (left : RepT a (L ∘ Fin.castAdd m) (R ∘ Fin.castAdd m))
    (right : RepT b (L ∘ Fin.natAdd n) (R ∘ Fin.natAdd n)) : RepT (a.append b) L R := by
  intro i z
  induction i using Fin.addCases with
  | left i => simpa only [Function.comp_apply,Tapes.append,Fin.addCases_left] using left i z
  | right i => simpa only [Function.comp_apply,Tapes.append,Fin.addCases_right] using right i z

theorem digitPermutationMetadata_rep {d : ℕ}
    (machine : {p : Fin d × Fin d // p.1 < p.2} → SharedBankSkeleton.Skeleton 1 prime)
    (bank : ∀ p, Tapes (machine p).tapes prime)
    (pairs : List {p : Fin d × Fin d // p.1 < p.2})
    (L R : Fin (digitSwapSkeleton machine pairs).tapes → List (Fin (prime+4)))
    (loaded : ∀ a, RepT (bank pairs[a]) (L ∘ digitSwapBank machine pairs a) (R ∘ digitSwapBank machine pairs a))
    (empty : ∀ k, (∀ a h, digitSwapBank machine pairs a h ≠ k) → L k = [] ∧ R k = []) :
    RepT (digitPermutationMetadata machine bank pairs) L R := by
  induction pairs with
  | nil =>
    intro i z
    obtain ⟨l,r⟩ := empty i (fun a => Fin.elim0 a)
    simp [digitPermutationMetadata,SharedBank.empty,l,r,readAt_nil_left,wordTape_nil]
  | cons p ps ih =>
    let place := (Fin.natAddEmb 1 (m := (digitSwapSkeleton machine ps).tapes)).trans
      (Fin.castAddEmb (machine p).tapes)
    have tail := ih (L ∘ place) (R ∘ place) (fun a => loaded a.succ) (by
      intro k away
      apply empty
      intro a
      induction a using Fin.cases with
      | zero =>
        intro h eq
        have val := congrArg Fin.val eq
        change 1+(digitSwapSkeleton machine ps).tapes+h.val = 1+k.val at val
        omega
      | succ a => exact fun h => place.injective.ne (away a h))
    apply rep_append_of_restrict
    · apply rep_append_of_restrict
      · intro k z
        obtain ⟨l,r⟩ := empty ((k.castAdd (digitSwapSkeleton machine ps).tapes).castAdd (machine p).tapes) (by
          intro a
          induction a using Fin.cases with
          | zero =>
            intro h eq
            have val := congrArg Fin.val eq
            change 1+_+h.val = k.val at val
            omega
          | succ a =>
            intro h eq
            have val := congrArg Fin.val eq
            change 1+_ = k.val at val
            omega)
        change blank = readAt blank (L _) (R _) (z-0)
        rw [l,r]
        simp [readAt_nil_left,wordTape_nil]
      · exact tail
    · exact loaded 0

/-- Initialize the actual permutation machine in a chart port. Every digit
swap borrows the same 35 spare tapes after the permutation bank. -/
theorem loadDigitPermutation {P U : Type} {T Q d spare : ℕ} (degree : 2 ≤ d) (room : 35 ≤ spare)
    (pairs : List {p : Fin d × Fin d // p.1 < p.2})
    (machine : {p : Fin d × Fin d // p.1 < p.2} → SharedBankSkeleton.Skeleton 1 prime)
    (K : ℕ) (fits : ∀ p, 1+(24+K) ≤ (machine p).tapes)
    (body : P → Pr P T Q prime U) (chart : Fin ((digitSwapSkeleton machine pairs).tapes+spare) ↪ Fin T)
    (source : Fin 4 → Fin T) (apart : ∀ k j, chart k ≠ source j) :
    let port := fun a => (digitSwapBank machine pairs a).trans ((Fin.castAddEmb spare).trans chart)
    let suffix := fun a (h : Fin (24+K)) => port a ((h.natAdd 1).castLE (fits pairs[a]))
    let tmp := ((Fin.castLEEmb room).trans (Fin.natAddEmb (digitSwapSkeleton machine pairs).tapes)).trans chart
    ∃ rate : ℕ, ∃ code, ∀ w W, 0 < W → ∀ u (S : Stacks T prime),
      let M := prime^(w+1)
      S.R (source 0) = binSyms M.size M → S.R (source 1) = binSyms 1 1 →
      S.R (source 2) = binSyms W.size W → (S.R (source 3)).length = w →
      (∀ k, S.L (tmp k) = [] ∧ S.R (tmp k) = []) →
      (∀ a h, S.L (suffix a h) = [] ∧ S.R (suffix a h) = []) →
      ∃ z F n, Exec body code (mk u S) n (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F n (rate*(M^d*W)) ∧
        (∀ a h, let p := pairs[a]
          let seed := swapPrivateStacks K (payloadView prime d (w+1) W) d p.val.1 p.val.2 (w+1)
          F.L (suffix a h) = seed.L h ∧ F.R (suffix a h) = seed.R h) ∧
        ∀ k, (∀ a h, suffix a h ≠ k) → F.L k = S.L k ∧ F.R k = S.R k := by
  intro port suffix tmp
  let inner (a : Fin pairs.length) := (Fin.natAddEmb 1 (m := 24+K)).trans (Fin.castLEEmb (fits pairs[a]))
  let dest a := (inner a).trans (port a)
  have external a h k : dest a h ≠ tmp k := chart.injective.ne (by
    intro eq
    have val := congrArg Fin.val eq
    change (digitSwapBank machine pairs a (inner a h)).val = (digitSwapSkeleton machine pairs).tapes+k.val at val
    have := (digitSwapBank machine pairs a (inner a h)).isLt
    omega)
  let bank a := appendPorts tmp (dest a) (fun k h => (external a h k).symm)
  have atData a h : bank a (h.natAdd 35) = suffix a h := by
    simp [bank,appendPorts,dest,inner,suffix]
  have sources a h k : bank a h ≠ source k := by
    induction h using Fin.addCases with
    | left h => simpa [bank,appendPorts,tmp] using apart ((h.castLE room).natAdd _) k
    | right h => rw [atData]; exact apart _ _
  obtain ⟨rate,code,run⟩ := loadSwapPortSchedule body (fun _ => K) bank source sources d degree
    (fun a => pairs[a].val.1) (fun a => pairs[a].val.2) (List.finRange pairs.length) (List.nodup_finRange _) (by
      intro a _ b _ ne h l
      change bank a (h.natAdd 35) ≠ bank b l
      rw [atData]
      induction l using Fin.addCases with
      | left l =>
        have eq : bank b (l.castAdd _) = tmp l := by simp [bank,appendPorts]
        rw [eq]; exact external a h l
      | right l =>
        rw [atData]
        exact ((Fin.castAddEmb spare).trans chart).injective.ne
          (digitSwapBank_disjoint machine pairs a b ne (inner a h) (inner b l)))
  refine ⟨rate,code,?_⟩
  intro w W pos u S M base unit width clock scratch vacant
  obtain ⟨z,F,n,exec,user,paid,loaded,off⟩ := run w W pos u S base unit width clock (by
    intro a _ k
    induction k using Fin.addCases with
    | left k => simpa [bank,appendPorts] using scratch k
    | right k => rw [atData]; exact vacant a k)
  refine ⟨z,F,n,exec,user,paid,?_,?_⟩
  · intro a h
    rw [← atData]
    exact loaded a (List.mem_finRange _) h
  · intro k away
    apply off
    intro a _ h
    change bank a (h.natAdd 35) ≠ k
    rw [atData]
    exact away a h

open Cover RecursiveInterchangeLayout in
/-- Starting from an empty permutation bank, the charged loader realizes its
complete machine metadata, including all shared owner and unused slots. -/
theorem loadDigitPermutation_rep {P U : Type} {T Q d spare : ℕ} (degree : 2 ≤ d) (room : 35 ≤ spare)
    (pairs : List {p : Fin d × Fin d // p.1 < p.2})
    (machine : {p : Fin d × Fin d // p.1 < p.2} → SharedBankSkeleton.Skeleton 1 prime)
    (fits : ∀ p, 25 ≤ (machine p).tapes)
    (body : P → Pr P T Q prime U) (chart : Fin ((digitSwapSkeleton machine pairs).tapes+spare) ↪ Fin T)
    (source : Fin 4 → Fin T) (apart : ∀ k j, chart k ≠ source j) :
    let place := (Fin.castAddEmb spare).trans chart
    ∃ rate : ℕ, ∃ code, ∀ w W, 0 < W → ∀ u (S : Stacks T prime),
      let M := prime^(w+1)
      let view := payloadView prime d (w+1) W
      let bank := fun (p : {p : Fin d × Fin d // p.1 < p.2}) => SharedBankStageInput.raw (LabelCall.bank (SharedBank.empty 1 prime)
        view (LabelPrepare.input view d p.val.1 p.val.2 (w+1))) (machine p).tapes
      S.R (source 0) = binSyms M.size M → S.R (source 1) = binSyms 1 1 →
      S.R (source 2) = binSyms W.size W → (S.R (source 3)).length = w →
      (∀ k, S.L (chart k) = [] ∧ S.R (chart k) = []) →
      ∃ z F n, Exec body code (mk u S) n (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F n (rate*(M^d*W)) ∧
        RepT (digitPermutationMetadata machine bank pairs) (F.L ∘ place) (F.R ∘ place) ∧
        ∀ k, (∀ h, place h ≠ k) → F.L k = S.L k ∧ F.R k = S.R k := by
  intro place
  obtain ⟨rate,code,run⟩ := loadDigitPermutation degree room pairs machine 0 fits body chart source apart
  refine ⟨rate,code,?_⟩
  intro w W pos u S M view bank base unit width clock vacant
  obtain ⟨z,F,n,exec,user,paid,set,off⟩ := run w W pos u S base unit width clock
    (fun _ => vacant _) (fun _ _ => vacant _)
  let port a := digitSwapBank machine pairs a
  let hdr (a : Fin pairs.length) (h : Fin 24) := (h.natAdd 1).castLE (fits pairs[a])
  have blankAt k (away : ∀ a h, port a (hdr a h) ≠ k) :
      F.L (place k) = [] ∧ F.R (place k) = [] := by
    have same := off (place k) (fun a h => place.injective.ne (away a h))
    exact ⟨same.1.trans (vacant _).1,same.2.trans (vacant _).2⟩
  refine ⟨z,F,n,exec,user,paid,?_,fun k away => off k (fun _ _ => away _)⟩
  apply digitPermutationMetadata_rep
  · intro a
    let localBank := (port a).trans place
    let localStacks : Stacks (machine pairs[a]).tapes prime :=
      ⟨[],[],F.L ∘ localBank,F.R ∘ localBank⟩
    have other k (outside : ∀ h, hdr a h ≠ k) :
        localStacks.L k = [] ∧ localStacks.R k = [] := by
      apply blankAt
      intro b h
      by_cases eq : b = a
      · subst b
        exact (port a).injective.ne (outside h)
      · exact digitSwapBank_disjoint machine pairs b a eq _ _
    apply swap_bank_rep (fits pairs[a]) _ _ _ localStacks
    · intro k z
      obtain ⟨l,r⟩ := other ((k.castAdd 24).castLE (fits pairs[a])) (by
        intro h eq
        have val := congrArg Fin.val eq
        change 1+h.val = k.val at val
        omega)
      rw [l,r]
      simp [SharedBank.empty,readAt_nil_left,wordTape_nil]
    · intro k
      have cell := set a (k.castAdd 0)
      simp only [swapPrivateStacks,Fin.append_left] at cell
      exact cell
    · intro k high
      apply other
      intro h eq
      have val := congrArg Fin.val eq
      change 1+h.val = k.val at val
      omega
  · exact fun k away => blankAt k (fun a h => away a _)

end IntegerMultBounds.MathlibTM2.M6.BitNode
