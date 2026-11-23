module

public import IntegerMultBounds.MathlibTM2.M6.BitIntervalPackEntry
public import IntegerMultBounds.MathlibTM2.M6.BitFlatNodeHandoff

/-! Run a supplied recursive flat node between the two inherited interval passes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
local notation "N" => rowSwapBlock.tapes

private theorem projectFan {c T B V : ℕ} (e : Fin T ↪ Fin B) (fan : Fin (c+2) ↪ Fin T)
    (data : Fin c → Fin V → ZMod 2) (S : Stacks B prime)
    (ready : HelperFan (fan.trans e) data S) : HelperFan fan data (embStk e S) := ready

private theorem projectedUser {T B Q A : ℕ} {U : Type} (e : Fin T ↪ Fin B) (v : HS B Q A U) :
    (embDn e v).user = v.user := rfl

/-- Local work of both layout passes and preparation of the child owner bank. -/
noncomputable def intervalChildToll (U : Type) (lo hi w W : ℕ) (axes : ℕ := 64) : ℕ :=
  let M := prime^(w+1)
  let V := M^(axes+axes)*W
  let header := 16*M.size+8*W.size+6*(w+1)+11*(w+1).size+58
  let pass := intervalPassTime U lo hi w W axes
  142080*(header+pass)+1 + (142081*(8*V+10)+1) + (142080*pass+1)

theorem intervalChildToll_fixed_le (U : Type) (lo hi : ℕ) (axes : ℕ := 64) (positive : 0 < axes := by decide) :
    ∃ a b : ℕ, ∀ w W, 0 < W → intervalChildToll U lo hi w W axes ≤
      (a+b*swapVolumeRate w)*((prime^(w+1))^(axes+axes)*W) := by
  obtain ⟨a,b,pass⟩ := intervalPassTime_le U lo hi axes positive
  refine ⟨142080*(101+2*a)+142081*18+3,142080*2*b,?_⟩
  intro w W hW
  let M := prime^(w+1)
  let V := M^(axes+axes)*W
  have atom : w+1 ≤ M := (Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt).le
  have modulus : M ≤ V := (Nat.le_self_pow (by omega : (axes+axes) ≠ 0) M).trans
    (Nat.le_mul_of_pos_right _ hW)
  have spectator : W ≤ V := Nat.le_mul_of_pos_left W (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
  have digits (n : ℕ) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have header : 16*M.size+8*W.size+6*(w+1)+11*(w+1).size+58 ≤ 99*V := by
    have := digits M
    have := digits W
    have := digits (w+1)
    omega
  have run : intervalPassTime U lo hi w W axes ≤ 1+(a+b*swapVolumeRate w)*V := pass w W hW
  change 142080*(_+_)+1+(142081*(8*V+10)+1)+(142080*_+1) ≤ _*V
  grw [header,run]
  generalize swapVolumeRate w = rate
  ring_nf
  omega

private theorem uniformRate {ι : Type} [Fintype ι] (a b : ι → ℕ) (i : ι) (rate V : ℕ) :
    (a i+b i*rate)*V ≤ (Finset.univ.sup a+Finset.univ.sup b*rate)*V :=
  Nat.mul_le_mul_right _ (Nat.add_le_add (Finset.le_sup (f := a) (Finset.mem_univ i))
    (Nat.mul_le_mul_right _ (Finset.le_sup (f := b) (Finset.mem_univ i))))

/-- One pair of coefficients covers every interval of the 64-axis node,
independently of the selected child, the allocation and the width. -/
theorem intervalChildToll_le (U : Type) :
    ∃ a b : ℕ, ∀ lo hi, lo ≤ hi → hi ≤ 64 → ∀ w W, 0 < W →
      intervalChildToll U lo hi w W ≤ (a+b*swapVolumeRate w)*((prime^(w+1))^128*W) := by
  choose setup swaps bound using fun i : Fin 65 × Fin 65 =>
    intervalChildToll_fixed_le U i.1.val i.2.val
  refine ⟨Finset.univ.sup setup,Finset.univ.sup swaps,?_⟩
  intro lo hi ordered fits w W pos
  let i : Fin 65 × Fin 65 := (⟨lo,by omega⟩,⟨hi,by omega⟩)
  apply (bound i w W pos).trans
  exact uniformRate setup swaps i _ _

/-- Across an interval schedule the layout passes cost a uniform rate per
lane volume and each supplied recursive budget is counted once. -/
theorem intervalSchedule_parentCost (U : Type) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} [Fintype ι] (lo hi budget steps : ι → ℕ) (w W : ℕ),
      0 < W → (∀ i, lo i ≤ hi i) → (∀ i, hi i ≤ 64) →
      (∀ i, steps i ≤ intervalChildToll U (lo i) (hi i) w W + budget i) →
      let V := (prime^(w+1))^128*W
      ((∑ i, steps i : ℕ) : ℝ) ≤ ((∑ i, budget i : ℕ) : ℝ) +
        Fintype.card ι*(C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) := by
  obtain ⟨setup,swaps,toll⟩ := intervalChildToll_le U
  obtain ⟨C,positive,bound⟩ := copyReturn_parentCost setup swaps
  refine ⟨C,positive,?_⟩
  intro ι _ lo hi budget steps w W hW ordered fits paid V
  have total {n t b k : ℕ} (run : n ≤ t+b) (localBound : t ≤ k) : n ≤ b+2*k := by omega
  have cost (i : ι) := bound w V (budget i) (steps i)
    (total (paid i) (toll (lo i) (hi i) (ordered i) (fits i) w W hW))
  simpa only [Nat.cast_sum,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul] using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => cost i)

theorem runIntervalChild {P U : Type} {T B Q w W atom price lo hi axes : ℕ}
    (capacity : rowSwapBlock.states ≤ Q) (ordered : lo ≤ hi) (fits : hi ≤ axes) (positive : 0 < W)
    (widthAt : (phaseIntervalChild lo hi (w+1) W axes).width = 64*atom)
    {body : P → Pr P B Q prime U} {code src dst seed}
    (child : PackedPieceHandoff ((prime^(w+1))^(axes+axes)*W) (packedChildOutput atom _) body code src dst seed price)
    (live : Fin (142080+2) ↪ Fin T) (headers : Fin 6 ↪ Fin T) (width : Fin T)
    (apart : ∀ r : Fin 142080, ∀ i, live (r.castAdd 2) ≠ headers i)
    (widthFree : ∀ r : Fin 142080, live (r.castAdd 2) ≠ width) :
    let H := 142082+T+B
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb B)
    let extend := Fin.castAddEmb (n := H) (142080*(N+35))
    let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let ports := intervalRecordBank (live.trans caller) (small 24)
    let lane := phaseIntervalChild lo hi (w+1) W axes
    let size := intervalChild_volume ordered fits (w+1) W
    ∃ (host : Empty ⊕ P → Pr (Empty ⊕ P) (H+142080*(N+35)) Q prime U)
      (program : Pr (Empty ⊕ P) (H+142080*(N+35)) Q prime U)
      (returned : Fin (142080+2) ↪ Fin H),
    (∀ j, (∀ i, live i ≠ j) → ∀ r, returned r ≠ caller j) ∧
    ∀ (input : Fin 142080 → Fin (volume prime lane) → ZMod 2) u S,
      IntervalHeaderInputs ((headers.trans caller).trans extend) (extend (caller width)) w W S →
      HelperFan ((live.trans caller).trans extend) (fun r i => input r (i.cast size.symm)) S →
      (∀ r k, k ≠ small 24 → S.L (ports r k) = [] ∧ S.R (ports r k) = []) →
      (∀ i : Fin 142082, let j := extend ((i.castAdd T).castAdd B)
        S.L j = [] ∧ S.R j = []) →
      (∀ i : Fin B, let j := extend (i.natAdd (142082+T))
        S.L j = seed.L i ∧ S.R j = seed.R i) →
      ∃ z F n, Exec host program (mk u S) n (mk z F) ∧
        n ≤ intervalChildToll U lo hi w W axes + price ∧
        z.user = u.user ∧ HelperFan (returned.trans extend)
          (fun r i => Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (input r) (i.cast size.symm)) F ∧
        ∀ j, (∀ i, live i ≠ j) → F.L (extend (caller j)) = S.L (extend (caller j)) ∧
          F.R (extend (caller j)) = S.R (extend (caller j)) := by
  intro H caller extend small ports lane size
  obtain ⟨bank,inner,call,disjoint,run⟩ := runSplitChild child live
  let returned := (childReturnFan dst).trans bank
  let host := fun p => embProg extend id (inner p)
  obtain ⟨enter,leave,passes⟩ := withIntervalBank_exec capacity (live.trans caller) returned
    (headers.trans caller) (caller width) (fun r i => caller.injective.ne (apart r i))
    (fun r => caller.injective.ne (widthFree r)) host lo hi ordered fits
  let M := prime^(w+1)
  let V := M^(axes+axes)*W
  have away j (outside : ∀ i, live i ≠ j) (r) : returned r ≠ caller j :=
    disjoint j (fun i => outside _) _
  refine ⟨host,(enter.seq (embProg extend id call)).seq leave,returned,away,?_⟩
  intro input u S dimensions owners free fresh prepared
  let output := fun r => Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (input r)
  obtain ⟨z,F,n,exec,paid,user,rows,frame⟩ := passes w W positive input output (embProg extend id call)
    (142081*(8*V+10)+1+price) (fun k => ∃ j, k = caller j ∧ ∀ i, live i ≠ j) u S (by
      rintro _ ⟨j,rfl,outside⟩ r
      exact ⟨caller.injective.ne (outside _),away j outside _⟩) dimensions owners free (by
      intro v D packed keep
      have untouched (j : Fin H) (outside : ∀ r : Fin 142080, caller (live (r.castAdd 2)) ≠ j) :=
        keep (extend j) (intervalRecordBank_outside (live.trans caller) _ j outside)
      obtain ⟨y,G,t,_,ran,bill,same,_,words,childFrame⟩ := run lane widthAt size input (embDn extend v)
        (embStk extend D) (projectFan extend (live.trans caller) _ D packed) (fun i => by
          have frame := untouched ((i.castAdd T).castAdd B) (fun r eq => by
            have h := congrArg Fin.val eq
            change 142082+(live (r.castAdd 2)).val = i.val at h
            omega)
          exact ⟨frame.1.trans (fresh i).1,frame.2.trans (fresh i).2⟩) (fun i => by
          have frame := untouched (i.natAdd (142082+T)) (fun r eq => by
            have h := congrArg Fin.val eq
            change 142082+(live (r.castAdd 2)).val = 142082+T+i.val at h
            omega)
          exact ⟨frame.1.trans (prepared i).1,frame.2.trans (prepared i).2⟩)
      obtain ⟨z,F,exec,user,rows,privateTapes,view⟩ := liftIntervalChild_exec (small 24) inner call
        (live.trans caller) returned _ v D y G t ran words
      have state := same.trans (projectedUser extend v)
      refine ⟨z,F,t,exec,bill,user.trans state,rows,privateTapes,?_⟩
      rintro _ ⟨j,rfl,outside⟩
      have unchanged := childFrame j (fun i => outside _)
      exact ⟨(view _).1.trans unchanged.1,(view _).2.trans unchanged.2⟩)
  refine ⟨z,F,n,exec,?_,user,rows,fun j outside => frame _ ⟨j,rfl,outside⟩⟩
  simp only [List.map_const',List.length_finRange,List.sum_replicate_nat] at paid
  unfold intervalChildToll
  dsimp only [V,M] at paid ⊢
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
