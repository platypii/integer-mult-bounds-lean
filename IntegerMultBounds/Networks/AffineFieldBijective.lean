import IntegerMultBounds.Networks.AffineFieldProgram

/-! Bijectivity of legal ordered field programs on finite coefficient rings.
This supplies the inverse-function semantics already used by the fixed Shared50
control; it introduces no abstract machine or uncharged inverse operation. -/
namespace IntegerMultBounds.Networks.AffineFieldBijective
noncomputable section
variable {ι R : Type*} [Fintype ι] [LinearOrder ι] [CommRing R]

omit [Fintype ι] in
/-- Unit scales and earlier-control shifts are injective coordinate updates. -/
theorem ordered_injective (op : OrderedAffine.Op ι R) (h : OrderedAffine.Legal op) :
    Function.Injective (OrderedAffine.execute op) := by
  intro x y hxy
  funext k
  cases op with
  | scale i a =>
    by_cases hk : k=i
    · subst k
      apply h.mul_right_injective
      simpa only [OrderedAffine.execute,Function.update_self] using congrFun hxy i
    · simpa only [OrderedAffine.execute,Function.update_of_ne hk] using congrFun hxy k
  | shift i j a =>
    have hj : j ≠ i := ne_of_lt h
    have hc : x j = y j := by
      simpa only [OrderedAffine.execute,Function.update_of_ne hj] using congrFun hxy j
    by_cases hk : k=i
    · subst k
      have ht := congrFun hxy i
      simpa only [OrderedAffine.execute,Function.update_self,hc,add_left_inj] using ht
    · simpa only [OrderedAffine.execute,Function.update_of_ne hk] using congrFun hxy k

/-- Every source field instruction is injective, including reflected subtraction
and the literal H_i/D_j interchange. -/
theorem execute_injective (op : AffineFieldProgram.Op ι R) (h : AffineFieldProgram.Legal op) :
    Function.Injective (AffineFieldProgram.execute op) := by
  cases op with
  | affineH op =>
    intro x y hxy
    have hH := congrArg Prod.fst hxy
    have hD := congrArg Prod.snd hxy
    exact Prod.ext (ordered_injective op h hH) hD
  | affineD op =>
    intro x y hxy
    have hH := congrArg Prod.fst hxy
    have hD := congrArg Prod.snd hxy
    exact Prod.ext hH (ordered_injective op h hD)
  | addToD i j =>
    intro x y hxy
    have hh := congrArg Prod.fst hxy
    change x.1 = y.1 at hh
    refine Prod.ext hh ?_
    funext k
    have hd := congrFun (congrArg Prod.snd hxy) k
    by_cases hk : k=j
    · subst k
      simpa only [AffineFieldProgram.execute,Swap.Shear.Op.run,Function.update_self,hh,add_left_inj] using hd
    · simpa only [AffineFieldProgram.execute,Swap.Shear.Op.run,Function.update_of_ne hk] using hd
  | subFromD i j =>
    apply Function.Involutive.injective
    intro x
    simp only [AffineFieldProgram.execute,Swap.Shear.Op.run,Function.update_self,sub_sub_cancel,
      Function.update_idem,Function.update_eq_self,Prod.mk.eta]
  | interchange i j =>
    apply Function.Involutive.injective
    intro x
    simp only [AffineFieldProgram.execute,Swap.Shear.Op.run,Function.update_self,
      Function.update_idem,Function.update_eq_self,Prod.mk.eta]

/-- List composition preserves injectivity in its actual execution order. -/
theorem run_injective (ops : List (AffineFieldProgram.Op ι R))
    (h : ∀ op ∈ ops, AffineFieldProgram.Legal op) : Function.Injective (AffineFieldProgram.run ops) := by
  induction ops with
  | nil => exact Function.injective_id
  | cons op ops ih =>
    exact (ih (fun op hop => h op (List.mem_cons_of_mem _ hop))).comp (execute_injective op (h op List.mem_cons_self))

/-- Over the finite modular address type, all legal programs are permutations. -/
theorem run_bijective [Finite R] (ops : List (AffineFieldProgram.Op ι R))
    (h : ∀ op ∈ ops, AffineFieldProgram.Legal op) : Function.Bijective (AffineFieldProgram.run ops) :=
  ⟨run_injective ops h,Finite.surjective_of_injective (run_injective ops h)⟩

end
end IntegerMultBounds.Networks.AffineFieldBijective
