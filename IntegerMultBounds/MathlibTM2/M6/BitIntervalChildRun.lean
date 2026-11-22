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
noncomputable def intervalChildToll (U : Type) (lo hi w W : ℕ) : ℕ :=
  let M := prime^(w+1)
  let V := M^128*W
  let header := 16*M.size+8*W.size+6*(w+1)+11*(w+1).size+58
  let pass := intervalPassTime U lo hi w W
  142080*(header+pass)+1 + (142081*(8*V+10)+1) + (142080*pass+1)

private theorem intervalChildToll_fixed_le (U : Type) (lo hi : ℕ) :
    ∃ a b : ℕ, ∀ w W, 0 < W → intervalChildToll U lo hi w W ≤
      (a+b*swapVolumeRate w)*((prime^(w+1))^128*W) := by
  obtain ⟨a,b,pass⟩ := intervalPassTime_le U lo hi
  refine ⟨142080*(101+2*a)+142081*18+3,142080*2*b,?_⟩
  intro w W hW
  let M := prime^(w+1)
  let V := M^128*W
  have atom : w+1 ≤ M := (Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt).le
  have modulus : M ≤ V := (Nat.le_self_pow (by decide : 128 ≠ 0) M).trans
    (Nat.le_mul_of_pos_right _ hW)
  have spectator : W ≤ V := Nat.le_mul_of_pos_left W (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
  have digits (n : ℕ) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have header : 16*M.size+8*W.size+6*(w+1)+11*(w+1).size+58 ≤ 99*V := by
    have := digits M
    have := digits W
    have := digits (w+1)
    omega
  have run : intervalPassTime U lo hi w W ≤ 1+(a+b*swapVolumeRate w)*V := pass w W hW
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

theorem runIntervalChild {P U : Type} {T B Q w W atom price lo hi : ℕ}
    (capacity : rowSwapBlock.states ≤ Q) (ordered : lo ≤ hi) (fits : hi ≤ 64) (positive : 0 < W)
    (widthAt : (phaseIntervalChild lo hi (w+1) W 64).width = 64*atom)
    {body : P → Pr P B Q prime U} {code src dst seed}
    (child : PackedPieceHandoff ((prime^(w+1))^128*W) (packedChildOutput atom _) body code src dst seed price)
    (live : Fin (142080+2) ↪ Fin T) (headers : Fin 6 ↪ Fin T) (width : Fin T)
    (apart : ∀ r : Fin 142080, ∀ i, live (r.castAdd 2) ≠ headers i)
    (widthFree : ∀ r : Fin 142080, live (r.castAdd 2) ≠ width) :
    let H := 142082+T+B
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb B)
    let extend := Fin.castAddEmb (n := H) (142080*(N+35))
    let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let ports := intervalRecordBank (live.trans caller) (small 24)
    let lane := phaseIntervalChild lo hi (w+1) W 64
    let size := intervalChild_volume ordered fits (w+1) W
    ∃ (host : Empty ⊕ P → Pr (Empty ⊕ P) (H+142080*(N+35)) Q prime U)
      (program : Pr (Empty ⊕ P) (H+142080*(N+35)) Q prime U)
      (returned : Fin (142080+2) ↪ Fin H),
    ∀ (input : Fin 142080 → Fin (volume prime lane) → ZMod 2) u S,
      IntervalHeaderInputs ((headers.trans caller).trans extend) (extend (caller width)) w W S →
      HelperFan ((live.trans caller).trans extend) (fun r i => input r (i.cast size.symm)) S →
      (∀ r k, k ≠ small 24 → S.L (ports r k) = [] ∧ S.R (ports r k) = []) →
      (∀ i : Fin 142082, let j := extend ((i.castAdd T).castAdd B)
        S.L j = [] ∧ S.R j = []) →
      (∀ i : Fin B, let j := extend (i.natAdd (142082+T))
        S.L j = seed.L i ∧ S.R j = seed.R i) →
      ∃ z F n, Exec host program (mk u S) n (mk z F) ∧
        n ≤ intervalChildToll U lo hi w W + price ∧
        z.user = u.user ∧ HelperFan (returned.trans extend)
          (fun r i => Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (input r) (i.cast size.symm)) F := by
  intro H caller extend small ports lane size
  obtain ⟨bank,inner,call,run⟩ := runSplitChild child live
  let returned := (childReturnFan dst).trans bank
  let host := fun p => embProg extend id (inner p)
  obtain ⟨enter,leave,passes⟩ := withIntervalBank_exec capacity (live.trans caller) returned
    (headers.trans caller) (caller width) (fun r i => caller.injective.ne (apart r i))
    (fun r => caller.injective.ne (widthFree r)) host lo hi ordered fits
  let M := prime^(w+1)
  let V := M^128*W
  refine ⟨host,(enter.seq (embProg extend id call)).seq leave,returned,?_⟩
  intro input u S dimensions owners free fresh prepared
  let output := fun r => Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (input r)
  obtain ⟨z,F,n,exec,paid,user,rows,_⟩ := passes w W positive input output (embProg extend id call)
    (142081*(8*V+10)+1+price) (fun _ => False) u S (by simp) dimensions owners free (by
      intro v D packed keep
      have untouched (j : Fin H) (outside : ∀ r : Fin 142080, caller (live (r.castAdd 2)) ≠ j) :=
        keep (extend j) (intervalRecordBank_outside (live.trans caller) _ j outside)
      obtain ⟨y,G,t,_,ran,bill,same,_,words,_⟩ := run lane widthAt size input (embDn extend v)
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
      obtain ⟨z,F,exec,user,rows,privateTapes,_⟩ := liftIntervalChild_exec (small 24) inner call
        (live.trans caller) returned _ v D y G t ran words
      have state := same.trans (projectedUser extend v)
      exact ⟨z,F,t,exec,bill,user.trans state,rows,privateTapes,by simp⟩)
  refine ⟨z,F,n,exec,?_,user,rows⟩
  simp only [List.map_const',List.length_finRange,List.sum_replicate_nat] at paid
  unfold intervalChildToll
  dsimp only [V,M] at paid ⊢
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
