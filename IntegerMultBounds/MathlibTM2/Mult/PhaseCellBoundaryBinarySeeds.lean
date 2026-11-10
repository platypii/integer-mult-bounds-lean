module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryHeaderInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedHeaderList
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! One structural header conversion builds all three retained geometry seeds.
Unary masters and the shared arithmetic scratch survive verbatim. -/
@[expose] public section
set_option autoImplicit false
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
variable {Q A s : ℕ} {P U : Type}

def boundarySeedPairs (masters : Fin 11 → Fin 117) : List (Fin 117 × Fin 117) :=
  [(masters 1,masters 4),(masters 9,masters 5),(masters 2,masters 6)]

def boundaryBinarySeeds (masters : Fin 11 → Fin 117) : Pr P 117 Q A U :=
  paddedHeaderList (masters 7) 19 20 21 22 23 25 (boundarySeedPairs masters)

def boundaryBinarySeedsCost (D s width W : ℕ) := 21*(s+width+W)+36*D+85

private theorem seedScratchRegs (a b c : Fin 117) (hreg : [a,b,c].Nodup)
    (ha : 63 ≤ a.val) (hb : 63 ≤ b.val) (hc : 63 ≤ c.val) :
    [a,b,c,19,20,21,22,23,25].Nodup := by
  change ([a,b,c]++[19,20,21,22,23,25]).Nodup
  rw [List.nodup_append]
  refine ⟨hreg,by decide,?_⟩
  intro i hi j hs heq
  subst j
  have hsmall : ∀ i ∈ [(19 : Fin 117),20,21,22,23,25], i.val < 63 := by decide +kernel
  have hlt := hsmall i hs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl <;> omega

theorem boundaryBinarySeeds_exec_within (body : P → Pr P 117 Q A U)
    (masters : Fin 11 → Fin 117) (p width W D N : ℕ) (seedValue : Fin 117 → ℕ)
    (hvalues : ∀ j, seedValue (boundarySeedGlobals j) = ![s,width,W] j)
    (hfit : ∀ j, ![s,width,W] j < 2^D)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (input : BoundaryUnarySource (s := s) p width W D N masters S) (depth : ℕ) :
    let F : Stacks 117 A := {S with R := paddedHeaderListR D (fun i => (S.R i).length) (boundarySeedPairs masters) S.R}
    ∃ v' n, v'.user = v.user ∧ n ≤ boundaryBinarySeedsCost D s width W ∧
      BoundaryHeaderSource (s := s) p width W D N masters seedValue F ∧
      (∀ i, i ∉ boundaryBinarySeedHeaders masters → F.R i = S.R i) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+
        2*boundaryBinarySeedsCost D s width W) depth (boundaryBinarySeeds masters)
        (mk v S) n (mk v' F) := by
  dsimp only
  have hs : (S.R (masters 1)).length = s := input.scalars.line
  have hw : (S.R (masters 9)).length = width := input.scalars.core
  have hW : (S.R (masters 2)).length = W := input.scalars.wide
  have hreg : ∀ pair ∈ boundarySeedPairs masters,
      [pair.1,masters 7,pair.2,19,20,21,22,23,25].Nodup := by
    have hr := input.seedReg
    regs_ne hr
    intro pair hp
    simp only [boundarySeedPairs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    all_goals apply seedScratchRegs (hreg := by regs_nodup) <;> exact input.mastersPrivate _
  have hnd : ((boundarySeedPairs masters).map Prod.snd).Nodup := by
    have hr := input.seedReg
    regs_ne hr
    simp only [boundarySeedPairs,List.map_cons,List.map_nil]
    regs_nodup
  have hdst (pair : Fin 117 × Fin 117) (hp : pair ∈ boundarySeedPairs masters) :
      ∃ j : Fin 3, pair.2 = masters (boundarySeamSeedMaster j) := by
    simp only [boundarySeedPairs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
  have hsrc (pair : Fin 117 × Fin 117) (hp : pair ∈ boundarySeedPairs masters) :
      ∃ i : Fin 11, i ∉ [4,5,6] ∧ pair.1 = masters i := by
    simp only [boundarySeedPairs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨1,by decide,rfl⟩
    · exact ⟨9,by decide,rfl⟩
    · exact ⟨2,by decide,rfl⟩
  obtain ⟨v',n,hu,hn,hex⟩ := paddedHeaderList_exec (body := body) (masters 7) 19 20 21 22 23 25 D
    (fun i => (S.R i).length) (boundarySeedPairs masters)
    (by intro pair hp
        simp only [boundarySeedPairs,List.mem_cons,List.not_mem_nil,or_false] at hp
        rcases hp with rfl | rfl | rfl
        · simpa [hs] using Nat.size_le.mpr (hfit 0)
        · simpa [hw] using Nat.size_le.mpr (hfit 1)
        · simpa [hW] using Nat.size_le.mpr (hfit 2)) hreg hnd
    (by intro pair hp other ho
        obtain ⟨j,hj⟩ := hdst pair hp
        obtain ⟨i,hi,hsi⟩ := hsrc other ho
        rw [hj,hsi]
        exact (input.seedsOff i hi _ (by fin_cases j <;> simp [boundarySeamSeedMaster])).symm)
    (by intro pair hp
        obtain ⟨j,hj⟩ := hdst pair hp
        rw [hj]
        have hr := input.seedReg
        regs_ne hr
        fin_cases j <;> dsimp only [boundarySeamSeedMaster,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] <;> assumption)
    v S input.scalars.ruler (by intro pair hp; rfl)
    (by intro pair hp; obtain ⟨j,hj⟩ := hdst pair hp; rw [hj]; exact input.seedsBlank _ (List.mem_ofFn.mpr ⟨j,rfl⟩))
    (by intro i hi
        have hsmall : ∀ i ∈ [(19 : Fin 117),20,21,22,23,25], i.val < 63 ∧ i ≠ 95 ∧ i ≠ 96 := by decide +kernel
        exact input.blank i (hsmall i hi).1 (hsmall i hi).2.1 (hsmall i hi).2.2)
  let F : Stacks 117 A := {S with R := paddedHeaderListR D (fun i => (S.R i).length) (boundarySeedPairs masters) S.R}
  have hframe (i : Fin 117) (hi : i ∉ boundaryBinarySeedHeaders masters) : F.R i = S.R i := by
    apply paddedHeaderListR_off
    intro pair hp heq
    obtain ⟨j,hj⟩ := hdst pair hp
    exact hi (List.mem_ofFn.mpr ⟨j,hj.symm.trans heq⟩)
  have hget (j : Fin 3) : F.R (masters (boundarySeamSeedMaster j)) = binSyms D (![s,width,W] j) := by
    have hpair : ∃ i : Fin 11, (masters i,masters (boundarySeamSeedMaster j)) ∈ boundarySeedPairs masters ∧
        (S.R (masters i)).length = ![s,width,W] j := by
      fin_cases j
      · exact ⟨1,by simp [boundarySeedPairs,boundarySeamSeedMaster],hs⟩
      · exact ⟨9,by simp [boundarySeedPairs,boundarySeamSeedMaster],hw⟩
      · exact ⟨2,by simp [boundarySeedPairs,boundarySeamSeedMaster],hW⟩
    obtain ⟨i,hi,hv⟩ := hpair
    have h := paddedHeaderListR_get D (fun i => (S.R i).length) (boundarySeedPairs masters) hnd S.R _ hi
    simpa only [hv] using h
  have hn' : n ≤ boundaryBinarySeedsCost D s width W := by
    simp only [boundarySeedPairs,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,hs,hw,hW] at hn
    unfold boundaryBinarySeedsCost
    omega
  refine ⟨v',n,hu,hn',input.with_seeds seedValue (by intro j; rw [hvalues j]; exact hget j) hframe,hframe,?_⟩
  exact mn_native_exec_within hex 2 (paddedHeaderList_native ..) depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hn') _)

/-- Place the shared converter once, retaining its exact preparation frame. -/
theorem placedBoundaryBinarySeeds_exec_within {T : ℕ}
    (body : P → Pr P T Q A U) (e : Fin 117 → Fin T) (he : Function.Injective e)
    (masters : Fin 11 → Fin 117) (p width W D N : ℕ) (seedValue : Fin 117 → ℕ)
    (hvalues : ∀ j, seedValue (boundarySeedGlobals j) = ![s,width,W] j)
    (hfit : ∀ j, ![s,width,W] j < 2^D)
    (v : HS T Q A U) (S : Stacks T A)
    (input : BoundaryUnarySource (s := s) p width W D N masters (embStk e S)) (depth : ℕ) :
    ∃ v' n, ∃ M : Stacks T A, v'.user = v.user ∧
      n ≤ boundaryBinarySeedsCost D s width W ∧
      BoundaryHeaderSource (s := s) p width W D N masters seedValue (embStk e M) ∧
      M.inp = S.inp ∧ M.out = S.out ∧ M.L = S.L ∧
      (∀ i, i ∉ (boundaryBinarySeedHeaders masters).map e → M.R i = S.R i) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+
        2*boundaryBinarySeedsCost D s width W) depth
        (embProg e Empty.elim (boundaryBinarySeeds (P := Empty) masters))
        (mk v S) n (mk v' M) := by
  obtain ⟨u,n,hu,hn,ready,hframe,hex⟩ := boundaryBinarySeeds_exec_within
    (fun f : Empty => nomatch f) masters p width W D N seedValue hvalues hfit
    (embDn e v) (embStk e S) input depth
  obtain ⟨v',_,hu',hex'⟩ := exec_emb_ovr_within_stock (e := e) (ι := Empty.elim)
    (body' := body) he (by intro f; cases f) hex v rfl S rfl
  let F : Stacks 117 A := {embStk e S with R := (paddedHeaderListR D
    (fun i => ((embStk e S).R i).length) (boundarySeedPairs masters) (embStk e S).R)}
  let M := embOvr e F.get S
  refine ⟨v',n,M,hu'.trans hu,hn,?_,rfl,rfl,embOvr_right_left ..,?_,hex'⟩
  · rw [embStk_ovr he]
    exact ready
  · intro i hi
    by_cases him : ∃ j, e j = i
    · obtain ⟨j,rfl⟩ := him
      change embExt e _ S.R (e j) = S.R (e j)
      rw [embExt_apply he]
      exact hframe j (by intro hj; exact hi (List.mem_map.mpr ⟨j,hj,rfl⟩))
    · exact (embOvr_off _ S (by simpa only [not_exists] using him)).2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
