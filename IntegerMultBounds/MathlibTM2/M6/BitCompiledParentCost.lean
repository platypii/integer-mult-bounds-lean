module

public import IntegerMultBounds.MathlibTM2.M6.BitCompiledPackedParent

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine RecursiveInterchangeLayout
open Shared50ModularControl (prime)

private theorem idleLocal_le (p : CutoffNodeInput) (i : Fin 9) (fixed base swaps : ℕ) :
    160*((remainderRanks i).map (fun r => if p.cutoff < r*(p.w+1) then
      idleRecordOverhead p fixed base swaps else 0)).sum ≤
      (142080*fixed+base+swaps*(@swapVolumeRate BinaryRadixEqualShared.supplierNet p.w))*p.cells := by
  let fee := idleRecordOverhead p fixed base swaps
  let charge := fun w => if p.cutoff < w then fee else 0
  change 160*((remainderRanks i).map (fun r => charge (r*(p.w+1)))).sum ≤ _
  rw [← idleWindowWidthSum p i charge,← idleWindowOverhead]
  have each (j : Fin idleCopies.length) : charge (scheduledChild prime p.node (idleDirectoryIndex (i,j))).width ≤ fee := by
    unfold charge
    split <;> simp
  have total := Finset.sum_le_sum (s := Finset.univ) (fun j _ => each j)
  dsimp only [fee] at total
  omega

/-- The compiled parent has a uniform local coefficient at the exponent of the
physical row-swap supplier. This includes the active wrappers at every cutoff. -/
theorem compiledParentLocal_bound (work : Fin 9 → ℕ → ℕ → ℕ) (init fixed base swaps : Fin 9 → ℕ)
    (assemble : ℕ)
    (stage : ∀ i, ∃ C : ℝ, ∀ w V : ℕ, 0 < w → 0 < V → (work i w V : ℝ) ≤
      C*((V : ℝ)*(w : ℝ)^(@M8.Machine.BudgetBound.tau BinaryRadixEqualShared.supplierNet))) :
    ∃ C : ℝ, ∀ p : CutoffNodeInput, (compiledParentLocal p work init fixed base swaps assemble : ℝ) ≤
      C*((volume prime p.node : ℝ)*(p.node.width : ℝ)^(@M8.Machine.BudgetBound.tau BinaryRadixEqualShared.supplierNet)) := by
  let _ := BinaryRadixEqualShared.supplierNet
  let linear := fun i => init i+735+142080*fixed i+base i
  let localWork := fun i w V => work i (w+1) V+(linear i+swaps i*swapVolumeRate w)*V
  obtain ⟨C,bound⟩ := CutoffNodeInput.localCharge_bound localWork assemble (by
    intro i
    obtain ⟨A,stageBound⟩ := stage i
    let K := 3808275+LeafCore.C
    refine ⟨A+((linear i : ℝ)+(swaps i : ℝ)*K),?_⟩
    intro w V positive
    let power := ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
    have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 w)
      M8.Machine.BudgetBound.exponent_range.1.le
    have fee := add_le_add (le_mul_of_one_le_right (Nat.cast_nonneg (linear i)) one)
      (mul_le_mul_of_nonneg_left (swapVolumeRate_le w) (Nat.cast_nonneg (swaps i)))
    have coeff : ((linear i+swaps i*swapVolumeRate w : ℕ) : ℝ) ≤ ((linear i : ℝ)+(swaps i : ℝ)*K)*power := by
      rw [Nat.cast_add,Nat.cast_mul,add_mul,mul_assoc]
      exact fee
    have paid := add_le_add (stageBound (w+1) V (Nat.succ_pos _) positive)
      (mul_le_mul_of_nonneg_right coeff (Nat.cast_nonneg V))
    dsimp only [localWork]
    rw [Nat.cast_add,Nat.cast_mul]
    exact paid.trans_eq (by dsimp only [power]; ring))
  refine ⟨C,fun p => (Nat.cast_le.mpr ?_).trans (bound p)⟩
  have windows := Finset.sum_le_sum (s := Finset.univ) (fun i _ => idleLocal_le p i (fixed i) (base i) (swaps i))
  unfold compiledParentLocal CutoffNodeInput.localCharge
  simp only [localWork,linear,Nat.add_mul,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] at windows ⊢
  omega

private theorem treeLocal_mono [M8.Machine.Net] {a b : ℝ} (ab : a ≤ b) (rate : ℝ)
    (cutoff fuel : ℕ) (v : Descriptor) :
    cutoffTreeBudget a rate cutoff fuel v ≤ cutoffTreeBudget b rate cutoff fuel v := by
  induction fuel generalizing v with
  | zero => rfl
  | succ fuel ih =>
    simp only [cutoffTreeBudget]
    split
    · exact Nat.add_le_add (Nat.floor_mono (mul_le_mul_of_nonneg_right ab (by positivity)))
        (Finset.sum_le_sum (fun k _ => ih (scheduledChild prime v k)))
    · rfl

/-- Install a record family already priced by a fixed tree. Increasing the parent
coefficient pays for the entry and leaves every descendant's allowance available. -/
theorem recordFamilyOfTreeBound [M8.Machine.Net] {Config P U : Type} {T Q : ℕ}
    {input : Config → CutoffNodeInput} {body : P → Pr P T Q prime U} {dst} {price : Config → ℕ}
    (family : SplitRecordChildFamily input body dst price) (A rate : ℝ)
    (bound : ∀ x, let p := input x
      p.cutoff < p.node.width → price x ≤ cutoffTreeBudget A rate p.cutoff (p.depth-p.path.length) p.node) :
    RecordTreeFamily input body dst rate (fun _ _ _ => True) := by
  obtain ⟨entry,install⟩ := family
  let minimum := max 0 A+((entry+21 : ℕ) : ℝ)
  refine ⟨minimum,by dsimp [minimum]; positivity,?_⟩
  intro K live record apart H
  obtain ⟨bank,host,program,placed,frame,exec⟩ := install live record apart
  refine ⟨bank,host,program,placed,frame,?_⟩
  intro D enough x p active fuel _
  have depth : p.depth-p.path.length = fuel+1 := p.remainingDepth_eq active
  let scale := (volume prime p.node : ℝ)*(p.node.width : ℝ)^M8.Machine.BudgetBound.tau
  have nonneg : 0 ≤ scale := by dsimp [scale]; positivity
  have vol : (volume prime p.node : ℝ) ≤ scale := le_mul_of_one_le_right (by positivity)
    (Real.one_le_rpow (by exact_mod_cast (show 1 ≤ p.node.width by rw [p.width]; omega))
      M8.Machine.BudgetBound.exponent_range.1.le)
  let reserve := entry*p.cells+(142081*(10*p.cells+10)+1)+2
  have reserveVol : reserve ≤ (entry+21)*volume prime p.node := recordEntryBound p entry
  have rootCharge : ⌊A*scale⌋₊+reserve ≤ ⌊D*scale⌋₊ := by
    have r : (reserve : ℝ) ≤ ((entry+21 : ℕ) : ℝ)*scale := by
      exact (Nat.cast_le.mpr reserveVol).trans (by rw [Nat.cast_mul]; gcongr)
    calc
      _ ≤ ⌊max 0 A*scale⌋₊+reserve := Nat.add_le_add_right (Nat.floor_mono
        (mul_le_mul_of_nonneg_right (le_max_right _ _) nonneg)) _
      _ = ⌊max 0 A*scale+reserve⌋₊ := (Nat.floor_add_natCast (mul_nonneg (le_max_left _ _) nonneg) _).symm
      _ ≤ _ := by
        apply Nat.floor_mono
        apply (add_le_add le_rfl r).trans
        rw [← add_mul]; exact mul_le_mul_of_nonneg_right enough nonneg
  have ab : A ≤ D := (le_max_right 0 A).trans ((le_add_of_nonneg_right (Nat.cast_nonneg (entry+21))).trans enough)
  have child := Finset.sum_le_sum (s := Finset.univ) (fun k _ =>
    treeLocal_mono ab rate p.cutoff fuel (scheduledChild prime p.node k))
  have core := bound x active
  change price x ≤ cutoffTreeBudget A rate p.cutoff (p.depth-p.path.length) p.node at core
  rw [depth,cutoffTreeBudget,ite_eq_left active] at core
  rw [depth,cutoffTreeBudget,ite_eq_left active]
  have fits : entry*p.cells+(142081*(10*p.cells+10)+1+price x)+2 ≤
      ⌊D*scale⌋₊+∑ k, cutoffTreeBudget D rate p.cutoff fuel (scheduledChild prime p.node k) := by
    dsimp only [reserve,scale] at rootCharge ⊢
    omega
  refine ⟨?_,(exec x).call fits⟩
  intro data u S fan fields cut len scratch bridge vacant
  obtain ⟨z,F,t,y,ran,user,paid,out⟩ := exec x data u S fan fields cut len scratch bridge vacant
  refine ⟨z,F,t,y,ran,user,?_,out⟩
  intro js unique
  exact (paid js unique).trans (Nat.add_le_add_left ((Nat.le_add_right _ 2).trans fits) _)

end IntegerMultBounds.MathlibTM2.M6.BitNode
