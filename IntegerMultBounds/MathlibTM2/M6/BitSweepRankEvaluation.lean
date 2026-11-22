module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepBinaryRank
public import IntegerMultBounds.MathlibTM2.M6.BitSweepCoordinateFormula

/-! The prepared matrix and arithmetic tapes for one PR589 record rank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589 Certificates.PR589.Nine
open Cover.Fallback RingFormula Shared50ModularControl Host Node Cover.LabelTraversal
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

/-- The two input matrices needed by a coordinate evaluator. Only eight
translation rows are read in the active case. -/
noncomputable def sweepRankMatrices (w : ℕ) (parent : Fin 64 → ZMod (prime^w))
    (n : Fin 9) (r : Role) (dest : Fin ((prime^w)^128)) :
    Bool → Matrix (Fin 64) (Fin 64) (ZMod (prime^w)) :=
  let c := port r.port.val
  let active := r.bank.val / 2 = BitHosting.activePair n.val
  let x := FlatCoordinateLayout.coordinates dest
  let pair := (sweepRank (prime^w)).symm dest
  let u := (copyActive (Q := prime^w)).symm pair.1
  let s := (chartAddress.symm (copyAddress.symm (u,finProdFinEquiv (pair.2,(0 : Fin 1))))).1
  fun b => if b then fun i j =>
    if i = 0 then (if active then s.1 (stageAxis.symm j) else x (@finSumFinEquiv 64 64 (.inl j)))
    else if i = 1 then (if active then s.2 (stageAxis.symm j) else x (@finSumFinEquiv 64 64 (.inr j)))
    else if i = 2 then parent j
    else Sum.elim (fun k => ((undoTranslation ⟨(i.val-3)%8,Nat.mod_lt _ (by decide)⟩ k : ℤ) : ZMod (prime^w)))
      (fun _ => 0) (stageAxis.symm j)
  else if active then (Swap.Modular.reduce (prime^w) (c.stageRoute n)).submatrix stageAxis.symm stageAxis.symm
  else (Swap.Modular.reduce (prime^w) c.fullChart).submatrix stageAxis.symm remainderAxis

noncomputable def sweepCoordinateCode (n : Fin 9) (r : Role) :=
  if r.bank.val / 2 = BitHosting.activePair n.val then activeCoordinateCode else inactiveCoordinateCode

/-- The rank obtained by evaluating the actual coordinate programs on their
two input matrices is the source rank demanded by the selector compiler. -/
theorem sweepCoordinate_rank (w : ℕ) (parent : Fin 64 → ZMod (prime^w)) (units : ∀ i, IsUnit (parent i))
    (n : Fin 9) (r : Role) (dest : Fin ((prime^w)^128)) :
    let mat := sweepRankMatrices w parent n r dest
    FlatCoordinateLayout.rank (fun k => eval (entryValue mat) (sweepCoordinateCode n r k)) =
      nodeSourceRank w parent units n r dest := by
  intro mat
  let c := port r.port.val
  have weight : (eval (entryValue mat) ∘ matrixInput true 2) = parent := by
    funext j
    simp [mat,entryValue,matrixInput,eval,sweepRankMatrices]
  have wu (i) : IsUnit (eval (entryValue mat) (matrixInput true 2 i)) := by
    change IsUnit ((eval (entryValue mat) ∘ matrixInput true 2) i)
    simp only [weight]
    exact units i
  by_cases active : r.bank.val / 2 = BitHosting.activePair n.val
  · rw [nodeSourceRank_active w parent units n r active]
    let pair := (sweepRank (prime^w)).symm dest
    let u := (copyActive (Q := prime^w)).symm pair.1
    let t := finProdFinEquiv (pair.2,(0 : Fin 1))
    let x := (chartAddress.symm (copyAddress.symm (u,t))).1
    let D := undoTranslation.map (Int.cast : ℤ → ZMod (prime^w))
    let R := Swap.Modular.reduce (prime^w) (c.stageRoute n)
    have route (i j) : mat false (stageAxis i) (stageAxis j) = R i j := by simp [mat,sweepRankMatrices,active,R,c]
    have tr (a b : Fin 8) : mat true ⟨3+a.val,by omega⟩ (stageAxis (.inl b)) =
        ((undoTranslation a b : ℤ) : ZMod (prime^w)) := by
      have ne (k : Fin 64) (hk : k.val < 3) : (⟨3+a.val,by omega⟩ : Fin 64) ≠ k := by
        intro eqn
        have := congrArg Fin.val eqn
        simp only at this
        omega
      simp [mat,sweepRankMatrices,ne 0 (by decide),ne 1 (by decide),ne 2 (by decide),Nat.mod_eq_of_lt a.isLt]
    have h (j) : mat true 0 (stageAxis j) = x.1 j := by simp [mat,sweepRankMatrices,active,x,t,u,pair]
    have d (j) : mat true 1 (stageAxis j) = x.2 j := by simp [mat,sweepRankMatrices,active,x,t,u,pair]
    apply congrArg FlatCoordinateLayout.rank
    funext k
    have value := parentDigitFormula_eval w (entryValue mat) (matrixInput true 2)
      (activeHalfFormula 0) (activeHalfFormula 1) wu k
    rw [activeHalf_eval w mat R 0 x.1 route tr h,activeHalf_eval w mat R 1 x.2 route tr d] at value
    have decode := chartAddress_decode_local u t (M8.Exchange.transform D D)
    simp only [sweepCoordinateCode,active,↓reduceIte,activeCoordinateCode]
    rw [value]
    apply congrFun _ k
    simp only [weight]
    apply congrArg (nodeDigitsEquiv w parent units)
    let y := chartHalves.symm (M8.Exchange.transform D D (chartHalves x).1,(chartHalves x).2)
    calc
      _ = M8.Exchange.transform R R y := rfl
      _ = M8.Exchange.transform R R (chartAddress.symm (copyAddress.symm (M8.Exchange.transform D D u,t))).1 :=
        congrArg (M8.Exchange.transform R R) decode
      _ = _ := rfl
  · rw [nodeSourceRank_inactive w parent units n r active]
    let x := FlatCoordinateLayout.coordinates dest
    let digit := fun j => Sum.elim (matrixInput true 0) (matrixInput true 1) ((@finSumFinEquiv 64 64).symm j)
    have digits : eval (entryValue mat) ∘ digit = x := by
      funext j
      obtain ⟨i,rfl⟩ := (@finSumFinEquiv 64 64).surjective j
      cases i <;> simp [mat,sweepRankMatrices,active,digit,eval,entryValue,matrixInput,x]
    apply congrArg FlatCoordinateLayout.rank
    funext k
    have value := inactiveDigitFormula_eval w c (entryValue mat)
      (fun i j => matrixInput false (stageAxis i) (remainderAxis.symm j)) (matrixInput true 2) digit
      (by intro i j; simp [mat,sweepRankMatrices,active,eval,matrixInput,entryValue,c]) wu k
    rw [digits] at value
    simpa only [sweepCoordinateCode,active,↓reduceIte,inactiveCoordinateCode,weight] using value

/-- A single binary word at the destination register is the selector
compiler's required source rank. Coordinates are computed as subprograms. -/
theorem sweepSourceRank_writes {T Q A : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (ports : Leaf (Entry Bool 64) → Fin T → Fin 7 ↪ Fin T)
    (coordBank rankBank : ℕ → Fin T → Fin 13 ↪ Fin T)
    (regs : Leaf (Option (Fin 128)) → Fin T → Fin 4 ↪ Fin T)
    (w H : ℕ) (fits : (prime^w)^128 < 2^H) (parent : Fin 64 → ZMod (prime^w))
    (units : ∀ i, IsUnit (parent i)) (n : Fin 9) (r : Role) (dest : Fin ((prime^w)^128)) (out : Fin T) :
    let mat := sweepRankMatrices w parent n r dest
    let f := sweepCoordinateCode n r
    let x := fun k => eval (entryValue mat) (f k)
    let coord := fun k => compile (readLeaf ports) coordBank (f k) 0
    let ready := fun k => prepared coordBank (entryValue mat) H (leafReady ports mat H) (f k) 0
    let cost := fun k => time H (readTime H) (f k)
    Writes body (prepared rankBank (rankInput x) H (rankLeafReady H x ready regs) sweepBinaryRankCode 0 out) out
      (compile (rankLeafProgram coord regs) rankBank sweepBinaryRankCode 0 out)
      (binSyms H (nodeSourceRank w parent units n r dest).val) (time H (rankLeafCost H cost) sweepBinaryRankCode) := by
  intro mat f x coord ready cost
  rw [← sweepCoordinate_rank w parent units n r dest]
  exact rankFromCoordinates_writes body H fits x rankBank regs coord ready cost
    (fun i d => compile_from_matrices body ports coordBank mat H
      ((Nat.le_self_pow (by decide : 128 ≠ 0) _).trans_lt fits) (f i) d) out

private theorem quadraticFormulaTime {ι : Type} (C : ℕ) (f : RingFormula ι) :
    ∃ K : ℕ, ∀ H cost, (∀ a, cost a ≤ C*(H+1)^2) → time H cost f ≤ K*(H+1)^2 := by
  induction f with
  | input i => exact ⟨C,fun _ _ cap => cap _⟩
  | zero => exact ⟨C,fun _ _ cap => cap _⟩
  | one => exact ⟨C,fun _ _ cap => cap _⟩
  | sub x y ih jh | mul x y ih jh =>
    obtain ⟨a,ha⟩ := ih
    obtain ⟨b,hb⟩ := jh
    refine ⟨a+b+160,?_⟩
    intro H cost cap
    have hx := ha H cost cap
    have hy := hb H cost cap
    simp only [RingFormula.time,Gate.time]
    ring_nf at hx hy ⊢
    omega

/-- The full source-rank evaluation, including every nested coordinate
computation, costs quadratically in the binary width. -/
theorem sweepSourceRank_time :
    ∃ C : ℕ, ∀ H n r, time H (rankLeafCost H (fun i =>
      time H (readTime H) (sweepCoordinateCode n r i))) sweepBinaryRankCode ≤ C*(H+1)^2 := by
  obtain ⟨K,allCoords⟩ := sweepCoordinate_time
  obtain ⟨C,bound⟩ := quadraticFormulaTime (K+6) sweepBinaryRankCode
  refine ⟨C,?_⟩
  intro H n r
  apply bound
  have copy : 6*H+6 ≤ (K+6)*(H+1)^2 := by ring_nf; omega
  intro a
  cases a with
  | zero | one => exact copy
  | input a =>
    cases a with
    | none => exact copy
    | some i =>
      have h := allCoords H (decide (r.bank.val / 2 = BitHosting.activePair n.val))
      have single := Finset.single_le_sum (f := fun k : Fin 128 =>
        time H (readTime H) (sweepCoordinateCode n r k)) (fun k _ => Nat.zero_le _) (Finset.mem_univ i)
      have total : (∑ k, time H (readTime H) (sweepCoordinateCode n r k)) ≤ K*(H+1)^2 := by
        by_cases act : r.bank.val / 2 = BitHosting.activePair n.val <;> simpa [sweepCoordinateCode,act] using h
      exact (single.trans total).trans (Nat.mul_le_mul_right _ (by omega))

end IntegerMultBounds.MathlibTM2.M6.BitNode
