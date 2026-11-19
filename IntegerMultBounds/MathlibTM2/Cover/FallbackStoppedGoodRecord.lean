module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodParentSetup
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodRecordRun
public import IntegerMultBounds.MathlibTM2.Cover.FallbackCallerLeaf

/-! Execute a good record with its stopped weighted child installed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host GoodForm FlatCoordinateLayout LabelTraversal
open CrossWeightLayout Matrix M8.Exchange IntegerMultBounds.Swap.Shear
open HeadPivotLayout HeadWidthLayout M8.ReversedExchange
open GoodChildLayout
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {U : Type} {n d Q : ℕ}
local notation "fields" => d+1

theorem stoppedGoodRecord_exec (cap : 217 ≤ Q) (fits : leafCapacity ((fields+d)+1) ≤ Q)
    (rank g : ℕ) (dim : fields = rank+g) (hr : rank ≤ fields) (caller seedHost : Fin 58 ↪ Fin n)
    (shared : ∀ j : Fin 58, j ≠ 28 → seedHost j = caller j) (digits : ℕ) :
    ∃ T, ∃ body : Unit → Pr Unit (n+T) Q prime U, ∃ C : ℝ, ∃ overhead : ℕ,
    ∀ w W H J, let M := prime^(w+1)
    letI : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩
    ∃ budget : ℕ, (H = Nat.size M → J = Nat.size W → 0 < W →
      (budget : ℝ) ≤ C*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*(M^(fields+fields)*W : ℕ)) ∧
    ∀ (desc : RecursiveInterchangeLayout.Descriptor) (_ : desc.between < 2^(digits*H+1)) (G : Matrix (Fin fields) (Fin fields) (ZMod M))
      (minor : ∀ j (hj : j < rank), IsUnit (lead (j+1) (lt_of_lt_of_le hj hr) G).det)
      (_ : G*G = G) (L : Matrix (Fin fields) (Fin rank) (ZMod M)) (R : Matrix (Fin rank) (Fin fields) (ZMod M))
      (_ : G = L*R) (weights inv : Fin fields → ZMod M) (_ : ∀ i, weights i * inv i = 1)
      (_ : M < 2^H) (_ : W < 2^J) (_ : 0 < W)
      (tail dest rest invRest pivotTail : List (Fin (prime+4))) (target : ℤ → Fin 4) (q : ℤ)
      (_ : ∀ z, q ≤ z → z < q+(M^(fields+fields)*W : ℕ) → target z = blank),
    let full := caller.trans (Fin.castAddEmb T)
    let middleHost := seedHost.trans (Fin.castAddEmb T)
    let K := digits*H+1
    let machine := parent.trans (parentWithWeights.trans full)
    let bank := adapterBank.trans machine
    let host := head.trans bank
    let c := child.trans host
    let h := (coeff true).trans host
    let s := shear.trans host
    let words := fun j => if hj : j ≤ rank then matrixWords prime H (stageAt G rank hr minor j hj).M else []
    let pair := matrixArchive words (words 0 ++ tail) dest rank
    let stage := stageAt G rank hr minor rank le_rfl
    let piv := fun j : Fin rank => stage.M (j.castLE hr) (j.castLE hr)
    let parent := (List.ofFn fun i => binSyms H (weights i).val).flatten ++ rest
    let ready := HeadColumnReady (d := fields+fields) (W := W) h (entry.trans bank) H J [] parent [] SparseRoleCircuit.encode (fun _ => blank) target 0 q
    let ordinary := ordinaryHead.trans bank
    let ts := shear.trans ordinary
    let middleCost := (((List.finRange rank).map fun i => childWeightTime prime w H i.val).sum+1 + dimensionTime H K (g+g)) +
        (budget+2+(2*(rank*H+rank*H+((g+g)*H+K))+7))
    ∀ v S (word : Fin (M^(fields+fields)*W) → ZMod 2),
      ready word S →
      S.R (bank 27) = [] → S.R (machine 54) = (List.ofFn fun j => binSyms H (inv j).val).flatten ++ invRest →
      (S.R (host 49),S.R (host 50)) = pair → (S.R (host 51)).length = fields*fields*H →
      S.R (c 18) = (List.ofFn fun j => binSyms H (piv j).val).flatten ++ pivotTail →
      S.R (c 15) = binSyms H (1 : ZMod M).val → (S.R (c 16)).length = w →
      (∀ j : Fin 20, (j ≤ 14 ∧ j ≠ 4) ∨ j = 17 → S.R (c j) = []) →
      (∀ k ∈ [full 55,full 56,full 57], S.R k = []) →
      ((middleHost 28 = full 28 ∧ binSyms (A := prime) K desc.between = binSyms 1 1) ∨
        ((∀ i, full i ≠ middleHost 28) ∧ S.R (middleHost 28) = binSyms K desc.between)) →
      (∀ j : Fin (n+T), n ≤ j.val → S.L j = [] ∧ S.R j = []) →
      ∃ z F n out, z.user = v.user ∧
        n ≤ 1 + goodIncomingTime (P := Empty) (U := U) (A := prime) Empty.elim machine prime w W H J rank hr + middleCost + (1 + goodOutgoingTime (P := Empty) (U := U) (A := prime) Empty.elim machine prime w W H J rank hr) ∧
        (H = Nat.size M → J = Nat.size W → n ≤ budget + overhead*(M^(fields+fields)*W) ∧
          (n : ℝ) ≤ (C+overhead)*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*(M^(fields+fields)*W : ℕ)) ∧
        Exec body (hostedGoodRecordAt cap full middleHost () prime rank g hr) (mk v S) n (mk z F) ∧ ready out F ∧ F.R (bank 27) = [] ∧
        (∀ j, (∀ i, s i ≠ j) → (∀ i, ts i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        ∀ x j, let y := transform (diagonal weights) 1 (revExchangeOf (rev fields) G (transform (diagonal inv) 1 x))
               out (index (Fin.append y.1 y.2) j) = word (index (Fin.append x.1 x.2) j) := by
  obtain ⟨T,prog,child⟩ := stoppedChild_program (P := Unit) (U := U) fits rank g dim caller
  let body := fun _ : Unit => prog
  obtain ⟨C,charge⟩ := child body (Fast.Main.mnProgPush prog) (fun _ => le_rfl)
  let ports := parent.trans (parentWithWeights.trans (caller.trans (Fin.castAddEmb T)))
  obtain ⟨overhead,parentBound⟩ := goodRecordTime_volume_le (P := Empty) (A := prime) (U := U)
    Empty.elim ports rank g digits dim (Nat.succ_pos d) hr
  refine ⟨T,body,C,overhead,?_⟩
  intro w W H J M
  let : NeZero (prime^(w+1)) := ⟨(pow_pos prime_prime.pos _).ne'⟩
  obtain ⟨budget,rate,leaf⟩ := charge w W H J
  refine ⟨budget,rate,?_⟩
  intro desc fitsMiddle G minor idem L R factor weights inv inverse hm hw hW tail dest rest invRest pivotTail target q empty
    full middleHost K machine bank host c h s words pair stage piv parent ready ordinary ts middleCost
    v S word initial free stored packed count pivots one clock scratch fresh seed privateFree
  have parentRun := hostedGoodRecord_exec cap body full middleHost (fun j hj => congrArg (Fin.castAdd T) (shared j hj))
    desc K fitsMiddle () budget G g dim hr minor idem L R factor weights inv inverse
    prime_prime H J hm hw hW tail dest rest invRest pivotTail SparseRoleCircuit.encode (fun _ => blank)
    target 0 q empty v S word initial free stored packed count pivots one clock scratch fresh seed
  obtain ⟨z,F,l,out,hz,hl,run,readyOut,clean,frame,effect⟩ := parentRun (by
    intro _ units u D before payload base widthWord unitWord _ _ _ archive padded clockLen off
    apply leaf _ _ units hm hw hW u D before payload base widthWord unitWord archive padded clockLen
    intro j hj
    have kept := off j (fun i eq => by
      have h := congrArg Fin.val eq
      change (caller i).val = j.val at h
      have := (caller i).isLt
      omega)
    exact ⟨kept.1.trans (privateFree j hj).1,kept.2.trans (privateFree j hj).2⟩)
  refine ⟨z,F,l,out,hz,hl,?_,run,readyOut,clean,frame,effect⟩
  rintro rfl rfl
  have total := hl.trans (parentBound w W budget hW)
  refine ⟨total,?_⟩
  let V := M^(fields+fields)*W
  let scale := ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
  have scale_ge : 1 ≤ scale :=
    Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 w) M8.Machine.BudgetBound.exponent_range.1.le
  have parentCost : (overhead : ℝ)*V ≤ overhead*scale*V := by
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg V)
    simpa using mul_le_mul_of_nonneg_left scale_ge (Nat.cast_nonneg overhead)
  have childCost : (budget : ℝ) ≤ C*scale*V := rate rfl rfl hW
  have steps : (l : ℝ) ≤ budget + (overhead : ℝ)*V := by exact_mod_cast total
  exact steps.trans ((add_le_add childCost parentCost).trans_eq (by ring))

end IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
