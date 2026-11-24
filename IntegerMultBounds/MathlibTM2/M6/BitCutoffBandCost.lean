module

public import IntegerMultBounds.MathlibTM2.M6.BitCutoffBandSupplier

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout

private theorem bandChildSize (v : Descriptor) (r : ℕ) (fits : r ≤ 64) :
    let b := v.width/64
    let child := rankDescriptor prime (r*b) ((64-r)*b) (role v 142080)
    child.width ≤ v.width ∧ volume prime child*142080 ≤ volume prime v := by
  intro b child
  have width : 64*b ≤ v.width := Nat.mul_div_le _ _
  have rows : (v.rows/142080)*142080 ≤ v.rows := Nat.div_mul_le_self ..
  refine ⟨(Nat.mul_le_mul_right b fits).trans width,?_⟩
  have powers : prime^(r*b)*prime^((64-r)*b) ≤ prime^v.width := by
    rw [← pow_add,← Nat.add_mul,Nat.add_sub_of_le fits]
    exact Nat.pow_le_pow_right Shared50ModularControl.prime_prime.pos width
  calc
    volume prime child*142080 =
      v.beforeRows*((v.rows/142080)*142080)*v.beforeH*(prime^(r*b)*prime^((64-r)*b))*
        v.between*(prime^(r*b)*prime^((64-r)*b))*v.afterD := by
          dsimp only [child,rankDescriptor,role,volume]; ring
    _ ≤ volume prime v := by unfold volume; gcongr

/-- The rank-42 continuations use at most 1440 of the 142080 role volumes.
The stopped ranks use at most forty parent volumes per level. Summing them
gives a bound independent of the number of remaining levels. -/
theorem cutoffBandBudget_volume [M8.Machine.Net] (D rate : ℝ) (cutoff fuel W : ℕ)
    (v : Descriptor) (fits : v.width ≤ W) :
    (cutoffBandBudget D rate cutoff fuel v : ℝ) ≤
      (2*(max 0 D+40*max 0 rate))*((W : ℝ)^M8.Machine.BudgetBound.tau*volume prime v) := by
  let A := max 0 D
  let B := max 0 rate
  let C := 2*(A+40*B)
  let power := (W : ℝ)^M8.Machine.BudgetBound.tau
  have ha : 0 ≤ A := le_max_left ..
  have hb : 0 ≤ B := le_max_left ..
  have hc : 0 ≤ C := by dsimp [C]; positivity
  have hp : 0 ≤ power := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have leaf (rate : ℝ) (x : Descriptor) (small : x.width ≤ W) :
      (⌊rate*(x.width : ℝ)^M8.Machine.BudgetBound.tau*volume prime x⌋₊ : ℝ) ≤ max 0 rate*power*volume prime x := by
    have pw := Real.rpow_le_rpow (Nat.cast_nonneg x.width) (Nat.cast_le.mpr small : (x.width : ℝ) ≤ W)
      M8.Machine.BudgetBound.exponent_range.1.le
    apply (Nat.cast_le.mpr (Nat.floor_mono (mul_le_mul_of_nonneg_right
      (mul_le_mul (le_max_right ..) pw (by positivity) (le_max_left 0 rate)) (Nat.cast_nonneg (volume prime x))))).trans
    exact Nat.floor_le (by positivity)
  have stop (x : Descriptor) (small : x.width ≤ W) :
      (⌊rate*(x.width : ℝ)^M8.Machine.BudgetBound.tau*volume prime x⌋₊ : ℝ) ≤ C*(power*volume prime x) := by
    rw [← mul_assoc]
    exact (leaf rate x small).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith : B ≤ C) hp) (Nat.cast_nonneg _))
  change _ ≤ C*(power*volume prime v)
  induction fuel generalizing v with
  | zero => exact stop v fits
  | succ n ih =>
    rw [cutoffBandBudget]
    split
    next active =>
      let child := fun r => rankDescriptor prime (r*(v.width/64)) ((64-r)*(v.width/64)) (role v 142080)
      let mass := power*volume prime v
      have massPos : 0 ≤ mass := by dsimp [mass]; positivity
      have share (r : ℕ) (hr : r ≤ 64) : power*volume prime (child r) ≤ mass/142080 := by
        obtain ⟨_,size⟩ := bandChildSize v r hr
        have vol : (volume prime (child r) : ℝ)*142080 ≤ volume prime v := by exact_mod_cast size
        apply (le_div_iff₀ (by norm_num)).2
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left vol hp
      have charge (r : ℕ) (hr : r ≤ 64) :
          (⌊rate*((child r).width : ℝ)^M8.Machine.BudgetBound.tau*volume prime (child r)⌋₊ : ℝ) ≤
            B*(mass/142080) := by
        apply (leaf rate _ ((bandChildSize v r hr).1.trans fits)).trans
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (share r hr) hb
      let hist := fiveHistogram.take 7
      have small : ∀ e ∈ hist, e.1 ≤ 64 := by decide
      have count : (hist.map Prod.snd).sum ≤ 40*142080 := by decide
      have leaves : ((hist.map (fun e => e.2*⌊rate*((child e.1).width : ℝ)^M8.Machine.BudgetBound.tau*
          volume prime (child e.1)⌋₊)).sum : ℝ) ≤ 40*(B*mass) := by
        have sum (xs : List (ℕ × ℕ)) (ok : ∀ e ∈ xs, e.1 ≤ 64) :
            ((xs.map (fun e => e.2*⌊rate*((child e.1).width : ℝ)^M8.Machine.BudgetBound.tau*
              volume prime (child e.1)⌋₊)).sum : ℝ) ≤ ((xs.map Prod.snd).sum : ℝ)*(B*(mass/142080)) := by
          induction xs with
          | nil => simp
          | cons e xs ih =>
            simp only [List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_mul,add_mul]
            exact add_le_add (mul_le_mul_of_nonneg_left (charge e.1 (ok _ (by simp))) (Nat.cast_nonneg _))
              (ih (fun f hf => ok f (List.mem_cons_of_mem _ hf)))
        apply (sum hist small).trans
        have coeff : (((hist.map Prod.snd).sum : ℕ) : ℝ) ≤ 40*142080 := by exact_mod_cast count
        exact (mul_le_mul_of_nonneg_right coeff (by positivity)).trans_eq (by ring)
      have cont := (ih (child 42) ((bandChildSize v 42 (by decide)).1.trans fits)).trans
        (mul_le_mul_of_nonneg_left (share 42 (by decide)) hc)
      have localBound : (⌊D*((volume prime v : ℝ)*(v.width : ℝ)^M8.Machine.BudgetBound.tau)⌋₊ : ℝ) ≤ A*mass := by
        rw [mul_comm (volume prime v : ℝ)]
        simpa only [mul_assoc] using leaf D v fits
      simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
      change _ ≤ C*mass
      dsimp only [C] at cont ⊢
      linarith only [localBound,leaves,cont,mul_nonneg ha massPos,mul_nonneg hb massPos]
    next => exact stop v fits

private theorem bandStoppingCost [M8.Machine.Net] (D rate : ℝ) (fuel : ℕ) (p : CutoffNodeInput)
    (band : 7*(p.w+1) ≤ p.cutoff) (σ : ℝ) (hs : 0 ≤ σ) (le : σ ≤ M8.Machine.BudgetBound.tau) :
    (cutoffBandBudget D rate p.cutoff fuel p.node : ℝ) ≤
      10*(2*(max 0 D+40*max 0 rate))*(p.node.width : ℝ)^σ*(p.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ)*
        volume prime p.node := by
  let K := 2*(max 0 D+40*max 0 rate)
  have pos : 0 ≤ K := by dsimp [K]; positivity
  let τ := M8.Machine.BudgetBound.tau
  have width : (p.node.width : ℝ) ≤ 10*p.cutoff := by
    exact_mod_cast (show p.node.width ≤ 10*p.cutoff by rw [p.width]; omega)
  have power : (p.node.width : ℝ)^τ ≤ (p.node.width : ℝ)^σ*(10*(p.cutoff : ℝ)^(τ-σ)) := by
    conv_lhs => rw [show τ = σ+(τ-σ) by ring,Real.rpow_add (by exact_mod_cast (show 0 < p.node.width by rw [p.width]; omega))]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      _ ≤ (10*(p.cutoff : ℝ))^(τ-σ) := Real.rpow_le_rpow (by positivity) width (sub_nonneg.mpr le)
      _ = (10 : ℝ)^(τ-σ)*(p.cutoff : ℝ)^(τ-σ) := Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 10)
          (show τ-σ ≤ 1 by have := M8.Machine.BudgetBound.exponent_range.2.le; dsimp [τ]; linarith)) (by positivity)
  have bill := cutoffBandBudget_volume D rate p.cutoff fuel p.node.width p.node le_rfl
  apply bill.trans
  change K*(_*_) ≤ 10*K*_*_*_
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right power (Nat.cast_nonneg _)) pos).trans_eq (by ring)

/-- The selected PR589 moment exponent is available at the physical stopping
entry. The remaining width power is paid on the cutoff alone. -/
theorem selectedBandStoppingCost (D rate : ℝ) (fuel : ℕ) (p : CutoffNodeInput)
    (band : 7*(p.w+1) ≤ p.cutoff) :
    let _ := BinaryRadixEqualShared.supplierNet
    let σ := 1-Layer.SelectedMoments.bitSaving
    (cutoffBandBudget D rate p.cutoff fuel p.node : ℝ) ≤
      20*(max 0 D+40*max 0 rate)*(p.node.width : ℝ)^σ*(p.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ)*
        volume prime p.node := by
  intro inst σ
  have le : σ ≤ M8.Machine.BudgetBound.tau := by
    change 1-Layer.SelectedMoments.bitSaving ≤ M8.Global.pr97.tau
    rw [M8.Global.pr97_tau]
    norm_num [Layer.SelectedMoments.bitSaving,M8.Global.Branching97.tau,M8.Global.Branching97.saving]
  simpa only [← mul_assoc,show (10 : ℝ)*2 = 20 by norm_num] using
    bandStoppingCost D rate fuel p band σ (by norm_num [σ,Layer.SelectedMoments.bitSaving]) le

/-- Charge the cutoff band at an outer exponent, moving only the difference
between that exponent and the row-swap exponent onto the cutoff. -/
theorem cutoffBandStoppingSupplier (U : Type) :
    let _ := BinaryRadixEqualShared.supplierNet
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q →
    ∃ (N : ℕ) (P : Type) (body : P → Pr P N Q prime U) (dst : Fin (142081+2) ↪ Fin N)
      (C : ℝ), 0 ≤ C ∧
    ∀ {T : ℕ} (live : Fin (142080+2) ↪ Fin T) (record : Fin 34 ↪ Fin T),
      (∀ i j, 8 ≤ j.val → record j ≠ live i) →
      let H := 142082+T+N
      ∃ (bank : Fin N ↪ Fin H) (host : Empty ⊕ P → Pr (Empty ⊕ P) H Q prime U)
        (code : Pr (Empty ⊕ P) H Q prime U), (∀ f, host (.inr f) = embProg bank Sum.inr (body f)) ∧
        ChildBankFrame live bank ∧ ∀ (p : CutoffNodeInput) blocks,
        p.root.Positive → 142080^(p.depth+1) ∣ p.root.rows →
        p.root.beforeH = blocks*prime^(64*p.root.width) → p.cutoff < p.node.width → 7*(p.w+1) ≤ p.cutoff →
        ∀ σ : ℝ, 0 ≤ σ → σ ≤ M8.Machine.BudgetBound.tau →
        InstalledRecordChildExec p live record dst bank host code
          ⌊C*(p.node.width : ℝ)^σ*(p.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ)*volume prime p.node⌋₊ := by
  intro inst
  obtain ⟨states,build⟩ := cutoffBandSupplier U
  refine ⟨states,?_⟩
  intro Q fits
  obtain ⟨N,P,body,dst,rate,D,nonneg,install⟩ := build fits
  let K := 2*(max 0 D+40*max 0 rate)
  have pos : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨N,P,body,dst,10*K,by positivity,?_⟩
  intro T live record apart H
  obtain ⟨bank,host,code,placed,frame,run⟩ := install live record apart
  refine ⟨bank,host,code,placed,frame,?_⟩
  intro p blocks positive rows label active band σ hs le
  have cap := Nat.le_floor (bandStoppingCost D rate (min (p.depth-p.path.length) 6) p band σ hs le)
  intro A L place link outer entry installed dispatch data u S fan fields cut len scratch bridge vacant
  obtain ⟨z,F,t,y,exec,user,paid,rest⟩ := run D le_rfl p blocks positive rows label active band
    place link outer entry installed dispatch data u S fan fields cut len scratch bridge vacant
  exact ⟨z,F,t,y,exec,user,fun js nd => (paid js nd).trans (Nat.add_le_add_left cap _),rest⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
