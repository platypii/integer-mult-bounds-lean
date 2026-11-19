module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackColumnAdd
public import IntegerMultBounds.MathlibTM2.Cover.FallbackColumnReady

/-! Execute one reverse elimination column on the physical tape bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open Matrix GoodForm IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

noncomputable def columnProgram (k : Fin d) : Pr P (N+1) columnCapacity prime U :=
  reverseColumn (Fin.last N) k (fun r i => columnAddProgram k i r)
    (coordinateSwap (fun i j => columnSwapProgram d i j) k)

noncomputable def columnProgramTime (U : Type) (k r : Fin d) (w W H J : ℕ) : ℕ :=
  let swap := fun (i j : Fin d) => 1+completeSwapTime (P := Empty) (U := U) Empty.elim d i j w W H J
  let shear := fun a b t => 1+reverseRowTime (P := Empty) (U := U) (A := prime) Empty.elim
      (Function.Embedding.refl _) a b k t r prime w W H J
  let cost := fun i => if k < i then shear k i i else swap i k + shear i k i + swap i k
  2*(r.val+1)+(d-1)*Finset.univ.sup cost+swap (min k r) (max k r)

/-- The finite row sweep preserves the one-coordinate saving in setup time. -/
theorem columnProgramTime_setup_le (U : Type) (d : ℕ) :
    ∃ C : ℕ, ∀ (k r : Fin d) w H, columnProgramTime U k r w 0 H 0 ≤
      C*(w+1+(prime^(w+1))^(d-1))*(H+1)^2 := by
  let size := fun w H : ℕ => (w+1+(prime^(w+1))^(d-1))*(H+1)^2
  let swap := fun (i j : Fin d) w H =>
    1+completeSwapTime (P := Empty) (U := U) Empty.elim d i j w 0 H 0
  have swaps (i j : Fin d) : ∃ c : ℕ, ∀ w H, swap i j w H ≤ c*size w H := by
    obtain ⟨c,h⟩ := completeSwapTime_setup_le (P := Empty) (U := U) Empty.elim d i j
    refine ⟨2*c+1, fun w H => ?_⟩
    dsimp only [swap, size]
    grw [h w H]
    generalize (prime^(w+1))^(d-1) = prefixes
    ring_nf
    omega
  have columns (kr : Fin d × Fin d) : ∃ c : ℕ, ∀ w H,
      columnProgramTime U kr.1 kr.2 w 0 H 0 ≤ c*size w H := by
    obtain ⟨k,r⟩ := kr
    let shear := fun (a b i : Fin d) w H => 1+reverseRowTime (P := Empty) (U := U)
      (A := prime) Empty.elim (Function.Embedding.refl _) a b k i r prime w 0 H 0
    let cost := fun w H (i : Fin d) => if k < i then shear k i i w H else
      swap i k w H + shear i k i w H + swap i k w H
    have one (w H : ℕ) : 1 ≤ size w H := Nat.mul_pos (by omega) (pow_pos (by omega) _)
    have rows (i : Fin d) : ∃ c : ℕ, ∀ w H, cost w H i ≤ c*size w H := by
      obtain ⟨s,hs⟩ := swaps i k
      by_cases h : k < i
      · obtain ⟨c,hc⟩ := reverseRowTime_setup_le (P := Empty) (U := U) (A := prime)
          Empty.elim (Function.Embedding.refl _) k i k i r prime prime_prime.pos
        refine ⟨1+c, fun w H => ?_⟩
        simp only [cost, h, ↓reduceIte, shear, Nat.add_mul, one_mul]
        exact Nat.add_le_add (one w H) (by simpa only [size, Nat.mul_assoc] using hc w H)
      · obtain ⟨c,hc⟩ := reverseRowTime_setup_le (P := Empty) (U := U) (A := prime)
          Empty.elim (Function.Embedding.refl _) i k k i r prime prime_prime.pos
        refine ⟨s+(1+c)+s, fun w H => ?_⟩
        simp only [cost, h, ↓reduceIte, shear, Nat.add_mul, one_mul]
        exact Nat.add_le_add (Nat.add_le_add (hs w H) (Nat.add_le_add (one w H)
          (by simpa only [size, Nat.mul_assoc] using hc w H))) (hs w H)
    choose c hc using rows
    obtain ⟨s,hs⟩ := swaps (min k r) (max k r)
    refine ⟨2*(r.val+1)+(d-1)*Finset.univ.sup c+s, fun w H => ?_⟩
    change 2*(r.val+1)+(d-1)*Finset.univ.sup (cost w H)+swap _ _ w H ≤ _
    have bound : Finset.univ.sup (cost w H) ≤ Finset.univ.sup c * size w H :=
      Finset.sup_le fun i hi => (hc i w H).trans (Nat.mul_le_mul_right _ (Finset.le_sup hi))
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc (d-1)]
    exact Nat.add_le_add (Nat.add_le_add (Nat.le_mul_of_pos_right _ (one w H))
      (Nat.mul_le_mul_left _ bound)) (hs w H)
  choose c hc using columns
  refine ⟨Finset.univ.sup c, fun k r w H => ?_⟩
  rw [Nat.mul_assoc]
  exact (hc (k,r) w H).trans (Nat.mul_le_mul_right _ (Finset.le_sup (Finset.mem_univ (k,r))))

/-- Only swaps incur the width-dependent rate, uniformly over columns and pivots. -/
theorem columnProgramTime_le_setup_add_width_volume (U : Type) (d : ℕ) :
    ∃ swaps shears : ℕ, ∀ (k r : Fin d) w W H J, columnProgramTime U k r w W H J ≤
      columnProgramTime U k r w 0 H J +
        (swaps * swapVolumeRate w + shears) * ((prime^(w+1))^d * W) := by
  let swap := fun (i j : Fin d) w W H J =>
    1 + completeSwapTime (P := Empty) (U := U) Empty.elim d i j w W H J
  let shear := fun (a b k t r : Fin d) w W H J =>
    1 + reverseRowTime (P := Empty) (U := U) (A := prime) Empty.elim
      (Function.Embedding.refl _) a b k t r prime w W H J
  have swaps (i j : Fin d) : ∃ s : ℕ, ∀ w W H J, swap i j w W H J ≤
      swap i j w 0 H J + s * swapVolumeRate w * ((prime^(w+1))^d * W) := by
    refine ⟨?_, fun w W H J => ?_⟩
    rotate_left
    simpa only [swap, Nat.add_assoc] using Nat.add_le_add_left
      (completeSwapTime_le_setup_add_volume (P := Empty) (U := U) Empty.elim d i j w W H J) 1
  choose s hs using swaps
  let S := Finset.univ.sup fun i => Finset.univ.sup (s i)
  have shears : ∃ c : ℕ, ∀ a b k t r w W H J, shear a b k t r w W H J =
      shear a b k t r w 0 H J + c * ((prime^(w+1))^d * W) := by
    refine ⟨?_, fun a b k t r w W H J => ?_⟩
    rotate_left
    simpa only [shear, Nat.add_assoc] using congrArg (1 + ·)
      (reverseRowTime_eq_setup_add_volume (P := Empty) (U := U) (A := prime) Empty.elim
        (Function.Embedding.refl _) a b k t r prime w W H J)
  obtain ⟨c, hc⟩ := shears
  refine ⟨(d-1)*(S+S)+S, (d-1)*c, fun k r w W H J => ?_⟩
  let V := (prime^(w+1))^d * W
  have swapBound (i j : Fin d) : swap i j w W H J ≤ swap i j w 0 H J + S*swapVolumeRate w*V := by
    have h : s i j ≤ S := (Finset.le_sup (f := s i) (Finset.mem_univ j)).trans
      (Finset.le_sup (f := fun a => Finset.univ.sup (s a)) (Finset.mem_univ i))
    exact (hs i j w W H J).trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h)) _)
  let cost := fun x (i : Fin d) => if k < i then shear k i k i r w x H J else
    swap i k w x H J + shear i k k i r w x H J + swap i k w x H J
  have rows : Finset.univ.sup (cost W) ≤ Finset.univ.sup (cost 0) + (S*swapVolumeRate w+c+S*swapVolumeRate w)*V := by
    apply Finset.sup_le
    intro i hi
    have base := Finset.le_sup (f := cost 0) hi
    apply le_trans _ (Nat.add_le_add_right base _)
    simp only [cost, Nat.add_mul]
    split <;> rw [hc] <;> have h := swapBound i k <;> dsimp [V] at * <;> omega
  change 2*(r.val+1)+(d-1)*Finset.univ.sup (cost W)+swap _ _ w W H J ≤
    2*(r.val+1)+(d-1)*Finset.univ.sup (cost 0)+swap _ _ w 0 H J+_ * V
  grw [rows, swapBound]
  exact le_of_eq (by ring)

/-- A single volume rate works for all columns and pivot choices at fixed atom width. -/
theorem columnProgramTime_le_setup_add_volume (U : Type) (d w : ℕ) :
    ∃ rate : ℕ, ∀ (k r : Fin d) W H J, columnProgramTime U k r w W H J ≤
      columnProgramTime U k r w 0 H J + rate * ((prime^(w+1))^d * W) := by
  obtain ⟨swaps, shears, bound⟩ := columnProgramTime_le_setup_add_width_volume U d
  exact ⟨_, fun k r => bound k r w⟩

/-- At a fixed field width one counter charge bounds every column and pivot. -/
theorem columnProgramTime_le_setup_add_counter (U : Type) (d H : ℕ) :
    ∃ rate : ℕ, ∀ (k r : Fin d) w W J, columnProgramTime U k r w W H J ≤
      columnProgramTime U k r w W H 0 + rate * J := by
  let swap := fun (i j : Fin d) w W J =>
    1 + completeSwapTime (P := Empty) (U := U) Empty.elim d i j w W H J
  let shear := fun (a b k t r : Fin d) w W J =>
    1 + reverseRowTime (P := Empty) (U := U) (A := prime) Empty.elim
      (Function.Embedding.refl _) a b k t r prime w W H J
  have swaps (i j : Fin d) : ∃ s : ℕ, ∀ w W J, swap i j w W J = swap i j w W 0 + s*J := by
    refine ⟨?_, fun w W J => ?_⟩
    rotate_left
    simpa only [swap, Nat.add_assoc] using congrArg (1 + ·)
      (completeSwapTime_eq_setup_add_counter (P := Empty) (U := U) Empty.elim d i j w W H J)
  have shears (b : Fin d) : ∃ c : ℕ, ∀ a k t r w W J, shear a b k t r w W J =
      shear a b k t r w W 0 + c*J := by
    refine ⟨?_, fun a k t r w W J => ?_⟩
    rotate_left
    simpa only [shear, Nat.add_assoc] using congrArg (1 + ·)
      (reverseRowTime_eq_setup_add_counter (P := Empty) (U := U) (A := prime) Empty.elim
        (Function.Embedding.refl _) a b k t r prime w W H J)
  choose s hs using swaps
  choose c hc using shears
  let S := Finset.univ.sup fun i => Finset.univ.sup (s i)
  let C := Finset.univ.sup c
  refine ⟨(d-1)*(S+C+S)+S, fun k r w W J => ?_⟩
  have swapBound (i j : Fin d) : s i j * J ≤ S*J := Nat.mul_le_mul_right _ <|
    (Finset.le_sup (f := s i) (Finset.mem_univ j)).trans
      (Finset.le_sup (f := fun a => Finset.univ.sup (s a)) (Finset.mem_univ i))
  have shearBound (b : Fin d) : c b * J ≤ C*J :=
    Nat.mul_le_mul_right _ (Finset.le_sup (f := c) (Finset.mem_univ b))
  let cost := fun x (i : Fin d) => if k < i then shear k i k i r w W x else
    swap i k w W x + shear i k k i r w W x + swap i k w W x
  have rows : Finset.univ.sup (cost J) ≤ Finset.univ.sup (cost 0) + (S+C+S)*J := by
    apply Finset.sup_le
    intro i hi
    apply le_trans _ (Nat.add_le_add_right (Finset.le_sup (f := cost 0) hi) _)
    simp only [cost, Nat.add_mul]
    split <;> simp only [hc _ _ _ _ _ w W J, hs _ _ w W J] <;>
      have := swapBound i k <;> have := shearBound k <;> have := shearBound i <;> omega
  change 2*(r.val+1)+(d-1)*Finset.univ.sup (cost J)+swap _ _ w W J ≤
    2*(r.val+1)+(d-1)*Finset.univ.sup (cost 0)+swap _ _ w W 0+_ * J
  rw [hs _ _ w W J]
  grw [rows, swapBound]
  exact le_of_eq (by ring)

theorem columnProgram_exec (k : Fin d) (rows : Fin d → Fin d) (H J : ℕ)
    (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P (N+1) columnCapacity prime U) (v : HS (N+1) columnCapacity prime U) (S : Stacks (N+1) prime)
    (matrix : Matrix (Fin d) (Fin d) (ZMod M)) (unit : IsUnit (matrix (rows k) k)) (tail rest : List (Fin (prime+4)))
    (dest : ℤ → Fin 4) (q : ℤ) (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank)
    (original : Fin (M^d*W) → ZMod 2) (addr : (Fin d → ZMod M) → Fin d → ZMod M)
    (code : S.R (Fin.last N) = orderedScheduleCode (((List.finRange d).take (k.val+1)).reverse) rows ++ rest) :
    let r := rows k
    let ready := ColumnReady columnBank H J matrix tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original
    let clean := fun (D : Stacks (N+1) prime) => ∀ i : Fin N, 35 ≤ i.val → D.L (columnPorts i) = [] ∧ D.R (columnPorts i) = []
    let remaining := orderedScheduleCode (((List.finRange d).take k.val).reverse) rows ++ rest
    ready (fun x => stepOp k r matrix (Ring.inverse (matrix r k)) *ᵥ addr x) S → clean S →
    ∃ z F n, z.user = v.user ∧ n ≤ columnProgramTime U k r w W H J ∧
      Exec body (columnProgram k) (mk v S) n (mk z F) ∧ ready addr F ∧ clean F ∧ F.R (Fin.last N) = remaining := by
  intro r ready clean remaining initial free
  let swap := fun (i j : Fin d) => 1+completeSwapTime (P := Empty) (U := U) Empty.elim d i j w W H J
  let shear := fun a b t => 1+reverseRowTime (P := Empty) (U := U) (A := prime) Empty.elim
      (Function.Embedding.refl _) a b k t r prime w W H J
  let cost := fun i => if k < i then shear k i i else swap i k + shear i k i + swap i k
  let ok := fun y D => ready y D ∧ clean D ∧ D.R (Fin.last N) = remaining
  apply reverseColumn_exec body (Fin.last N) k rows matrix _ _ _ ok _ _ v S rest addr code
  · have outside (i : Fin N) : columnPorts i ≠ Fin.last N := fun e => i.isLt.ne (congrArg Fin.val e)
    have bankOutside (i : Fin 35) : columnBank i ≠ Fin.last N := outside _
    obtain ⟨word,layout,placed⟩ := initial
    refine ⟨⟨word,?_,placed⟩,fun i hi => ?_,Function.update_self ..⟩
    · rcases layout with ⟨base,width,one,padded,clock,archive,scratch,src,dst⟩
      constructor <;> simp only [Function.update_of_ne (bankOutside _)] <;> assumption
    · exact ⟨(free i hi).1,(Function.update_of_ne (outside i) ..).trans (free i hi).2⟩
  · intro i ne y u D h
    obtain ⟨z,F,n,hz,hn,run,next⟩ := columnAddProgram_exec k i r ne H J hm hw hW body u D matrix unit tail
      remaining dest q empty original y h
    exact ⟨z,F,n,hz,hn.trans (Finset.le_sup (f := cost) (Finset.mem_univ i)),run,next⟩
  · intro y u D h
    change ∃ z F n, z.user = u.user ∧ n ≤ swap (min k r) (max k r) ∧ Exec body (coordinateSwap (fun i j => columnSwapProgram d i j) k r) (mk u D) n (mk z F) ∧ ok (fun x => y x ∘ Equiv.swap k r) F
    have ordered (i j : Fin d) (lt : i < j) := columnSwapProgram_exec i j lt H J hm hw hW body u D matrix
      tail dest q original y h.1 h.2.1
    rcases lt_trichotomy k r with lt | eq | gt
    · obtain ⟨z,F,n,hz,hn,run,next,freeF,_,stream⟩ := ordered k r lt
      exact ⟨z,F,n,hz,by simpa [min_eq_left lt.le,max_eq_right lt.le] using hn,
        by simpa [coordinateSwap,lt] using run,next,freeF,stream.trans h.2.2⟩
    · refine ⟨u,D,1,rfl,by simp [swap],?_,?_⟩
      · simpa [← eq,coordinateSwap] using Exec.act (body := body) .done (mk u D)
      · simpa [← eq] using h
    · obtain ⟨z,F,n,hz,hn,run,next,freeF,_,stream⟩ := ordered r k gt
      exact ⟨z,F,n,hz,by simpa [min_eq_right gt.le,max_eq_left gt.le] using hn,
        by simpa [coordinateSwap,gt.not_gt,gt] using run,by simpa [Equiv.swap_comm k r] using next,
        freeF,stream.trans h.2.2⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
