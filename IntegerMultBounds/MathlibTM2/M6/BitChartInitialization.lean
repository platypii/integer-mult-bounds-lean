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

end IntegerMultBounds.MathlibTM2.M6.BitNode
