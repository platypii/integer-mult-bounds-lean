module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackDiagonalRewind
public import IntegerMultBounds.MathlibTM2.Cover.FallbackForwardReady

/-! Execute a residual matrix from its packed coefficients and round-trip pivot schedule. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

noncomputable def signedResidual (d : ℕ) : Pr P (N+2) columnCapacity prime U :=
  .seq (streamedItinerary (d+1) prime forwardBank (Fin.last N).castSucc (d+1)) (diagonalRewind d)

noncomputable def signedResidualTime (U : Type) (rows : Fin (d+1) → Fin (d+1)) (w W H J : ℕ) : ℕ :=
  let pairCost := ((List.finRange d).map fun i => pairScalingTime U i.succ 0 i.succ w W H J).sum
  let stepCost := 1+Finset.univ.sup (fun k => columnProgramTime U k (rows k) w W H J)+((d+1)*(d+1)*(4*H+4)+1)
  let forwardCost := (d+1)*(2*(d+1)+(4*w+4+columnTime (d+1) prime w H))+1
  forwardCost + ((1+(pairCost+1))+((d+1)*stepCost+1))

/-- For a residual matrix of dimension `d+1`, setup enumerates at most
`d` coordinates. The constant works for every pivot itinerary. -/
theorem signedResidualTime_setup_le (U : Type) (d : ℕ) :
    ∃ C : ℕ, ∀ (rows : Fin (d+1) → Fin (d+1)) w H,
      signedResidualTime U rows w 0 H 0 ≤ C*(w+1+(prime^(w+1))^d)*(H+1)^2 := by
  choose c hc using fun i : Fin d => pairScalingTime_setup_le U i.succ 0 i.succ
  obtain ⟨s,hs⟩ := columnProgramTime_setup_le U (d+1)
  refine ⟨((List.finRange d).map c).sum + (d+1)*s + 1000*(prime+1)*(d+2)^5, ?_⟩
  intro rows w H
  let size := (w+1+(prime^(w+1))^d)*(H+1)^2
  have pairs (xs : List (Fin d)) :
      (xs.map fun i => pairScalingTime U i.succ 0 i.succ w 0 H 0).sum ≤ (xs.map c).sum*size := by
    induction xs with
    | nil => simp
    | cons i xs ih =>
      simp only [List.map_cons, List.sum_cons, Nat.add_mul]
      exact Nat.add_le_add (by simpa only [size, Nat.add_one_sub_one, Nat.mul_assoc] using hc i w H) ih
  have columns : Finset.univ.sup (fun k => columnProgramTime U k (rows k) w 0 H 0) ≤ s*size :=
    Finset.sup_le fun k _ => by simpa only [size, Nat.add_one_sub_one, Nat.mul_assoc] using hs k (rows k) w H
  simp only [signedResidualTime]
  grw [pairs, columns]
  simp only [columnTime, entryTime, size]
  grw [Nat.sub_le prime 2]
  generalize (prime^(w+1))^d = prefixes
  generalize ((List.finRange d).map c).sum = total
  generalize prime = p
  ring_nf
  omega

/-- Apart from the largest pivot-column cost, the payload charge of the
whole residual schedule has one rate shared by every pivot itinerary. -/
theorem signedResidualTime_le_setup_add_columns (U : Type) (d : ℕ) :
    ∃ swaps shears : ℕ, ∀ (rows : Fin (d+1) → Fin (d+1)) w W H J,
      let columns := fun x => Finset.univ.sup (fun k => columnProgramTime U k (rows k) w x H J)
      signedResidualTime U rows w W H J ≤ signedResidualTime U rows w 0 H J +
        (swaps * swapVolumeRate w + shears) * ((prime^(w+1))^(d+1) * W) + (d+1) * (columns W - columns 0) := by
  choose s h hr using fun i : Fin d => pairScalingTime_le_setup_add_width_volume U i.succ 0 i.succ
  refine ⟨((List.finRange d).map s).sum, ((List.finRange d).map h).sum, ?_⟩
  intro rows w W H J columns
  let V := (prime^(w+1))^(d+1) * W
  have pairs (xs : List (Fin d)) :
      (xs.map fun i => pairScalingTime U i.succ 0 i.succ w W H J).sum ≤
        (xs.map fun i => pairScalingTime U i.succ 0 i.succ w 0 H J).sum + ((xs.map s).sum * swapVolumeRate w + (xs.map h).sum) * V := by
    induction xs with
    | nil => simp
    | cons i xs ih =>
      simp only [List.map_cons, List.sum_cons, Nat.add_mul]
      have hi := hr i w W H J
      change _ ≤ _ + (s i * swapVolumeRate w + h i) * V at hi
      simp only [Nat.add_mul] at ih hi ⊢
      omega
  have col : columns W ≤ columns 0 + (columns W - columns 0) := by omega
  have steps := Nat.mul_le_mul_left (d+1) col
  rw [Nat.mul_add] at steps
  unfold signedResidualTime
  dsimp only
  have hp := pairs (List.finRange d)
  dsimp [V] at hp
  dsimp [columns] at steps ⊢
  simp only [Nat.mul_add] at *
  omega

/-- The residual execution bound is affine in volume, uniformly over pivot itineraries. -/
theorem signedResidualTime_le_setup_add_width_volume (U : Type) (d : ℕ) :
    ∃ swaps shears : ℕ, ∀ (rows : Fin (d+1) → Fin (d+1)) w W H J,
      signedResidualTime U rows w W H J ≤ signedResidualTime U rows w 0 H J +
        (swaps * swapVolumeRate w + shears) * ((prime^(w+1))^(d+1) * W) := by
  obtain ⟨ps, ph, hp⟩ := signedResidualTime_le_setup_add_columns U d
  obtain ⟨cs, ch, hc⟩ := columnProgramTime_le_setup_add_width_volume U (d+1)
  refine ⟨ps + (d+1)*cs, ph + (d+1)*ch, fun rows w W H J => ?_⟩
  let columns := fun x => Finset.univ.sup (fun k => columnProgramTime U k (rows k) w x H J)
  let V := (prime^(w+1))^(d+1) * W
  have bound : columns W ≤ columns 0 + (cs * swapVolumeRate w + ch)*V := by
    apply Finset.sup_le
    intro k hk
    exact (hc k (rows k) w W H J).trans (Nat.add_le_add_right
      (Finset.le_sup (f := fun i => columnProgramTime U i (rows i) w 0 H J) hk) _)
  have delta : columns W - columns 0 ≤ (cs * swapVolumeRate w + ch)*V := by omega
  apply (hp rows w W H J).trans
  change _ + (ps * swapVolumeRate w + ph)*V + (d+1)*(columns W - columns 0) ≤ _ + _*V
  grw [delta]
  exact le_of_eq (by ring)

/-- The residual execution bound is affine in volume, uniformly over pivot itineraries. -/
theorem signedResidualTime_le_setup_add_volume (U : Type) (d w : ℕ) :
    ∃ rate : ℕ, ∀ (rows : Fin (d+1) → Fin (d+1)) W H J,
      signedResidualTime U rows w W H J ≤ signedResidualTime U rows w 0 H J +
        rate * ((prime^(w+1))^(d+1) * W) := by
  obtain ⟨swaps, shears, bound⟩ := signedResidualTime_le_setup_add_width_volume U d
  exact ⟨_, fun rows => bound rows w⟩

/-- The forward scan contributes no counter-width charge. The reverse schedule
pays the sum of the pair charges and one uniform charge per column. -/
theorem signedResidualTime_le_setup_add_counter (U : Type) (d H : ℕ) :
    ∃ rate : ℕ, ∀ (rows : Fin (d+1) → Fin (d+1)) w W J,
      signedResidualTime U rows w W H J ≤ signedResidualTime U rows w W H 0 + rate * J := by
  choose r hr using fun i : Fin d => pairScalingTime_eq_setup_add_counter U i.succ 0 i.succ H
  obtain ⟨c, hc⟩ := columnProgramTime_le_setup_add_counter U (d+1) H
  refine ⟨((List.finRange d).map r).sum + (d+1)*c, fun rows w W J => ?_⟩
  let columns := fun x => Finset.univ.sup (fun k => columnProgramTime U k (rows k) w W H x)
  have col : columns J ≤ columns 0 + c*J := by
    apply Finset.sup_le
    intro k hk
    exact (hc k (rows k) w W J).trans (Nat.add_le_add_right
      (Finset.le_sup (f := fun i => columnProgramTime U i (rows i) w W H 0) hk) _)
  have steps := Nat.mul_le_mul_left (d+1) col
  dsimp [columns] at steps
  simp only [signedResidualTime, hr _ w W J, List.sum_map_add, List.sum_map_mul_right,
    Nat.mul_add, Nat.add_mul, Nat.mul_assoc] at steps ⊢
  omega

/-- Least uniform cost per payload-counter bit over all pivot itineraries. -/
noncomputable def residualCounterRate (U : Type) (d H : ℕ) : ℕ := by
  classical
  exact Nat.find (signedResidualTime_le_setup_add_counter U d H)

theorem residualCounterRate_spec (U : Type) (d H : ℕ) (rows : Fin (d+1) → Fin (d+1))
    (w W J : ℕ) : signedResidualTime U rows w W H J ≤
      signedResidualTime U rows w W H 0 + residualCounterRate U d H * J := by
  classical
  exact Nat.find_spec (signedResidualTime_le_setup_add_counter U d H) rows w W J

theorem residualCounterRate_le (U : Type) (d H rate : ℕ)
    (bound : ∀ (rows : Fin (d+1) → Fin (d+1)) w W J, signedResidualTime U rows w W H J ≤
      signedResidualTime U rows w W H 0 + rate * J) : residualCounterRate U d H ≤ rate := by
  classical
  exact Nat.find_min' (signedResidualTime_le_setup_add_counter U d H) bound

theorem signedResidual_exec (rows : Fin (d+1) → Fin (d+1)) (m : Matrix (Fin (d+1)) (Fin (d+1)) (ZMod M))
    (valid : Itinerary.Valid rows m (d+1)) (s : (ZMod M)ˣ)
    (sign : (Itinerary.run rows m (d+1)).det = (s : ZMod M)) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P (N+2) columnCapacity prime U) (v : HS (N+2) columnCapacity prime U) (S : Stacks (N+2) prime)
    (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(d+1)*W : ℕ) → dest z = blank) (original : Fin (M^(d+1)*W) → ZMod 2) :
    let bank := fun n => columnBank.trans (archivePorts n)
    let ready := fun n t => ColumnReady (bank n) H J (Itinerary.run rows m n) t SparseRoleCircuit.encode
      (fun _ => blank) dest 0 q original
    let clean := fun (D : Stacks (N+2) prime) => ∀ i : Fin N, 35 ≤ i.val → D.L (columnPorts i).castSucc = [] ∧ D.R (columnPorts i).castSucc = []
    let anchor := fun x j => ((Fin.cons s (fun _ => 1) : Fin (d+1) → (ZMod M)ˣ) j : ZMod M) * x j
    let schedule := orderedScheduleCode (List.finRange (d+1)).reverse rows ++ rest
    ready 0 tail anchor S → clean S → S.R (Fin.last N).castSucc = scheduleCode rows ++ schedule →
    ∃ z F n, z.user = v.user ∧ n ≤ signedResidualTime U rows w W H J ∧
      Exec body (signedResidual d) (mk v S) n (mk z F) ∧ ready 0 tail (fun x => m.mulVec x) F ∧
      clean F ∧ F.R (Fin.last N).castSucc = rest ∧ F.R (bank 1 34) = S.R (bank 1 34) := by
  intro bank ready clean anchor schedule before free code
  obtain ⟨u,D,l,suffix,hu,hl,forward,next,freeD,stream,archive⟩ :=
    forwardReady_exec rows H J hm body v S m valid tail schedule dest q original anchor before free code
  let finalMatrix := Itinerary.run rows m (d+1)
  obtain ⟨_,_,_,cleared,units⟩ := Itinerary.run_spec rows m (d+1) le_rfl valid
  let a := fun j : Fin (d+1) => (units j j.isLt).unit
  have diag : finalMatrix = Matrix.diagonal (fun j => (a j : ZMod M)) := by
    ext i j
    by_cases h : i = j
    · subst j
      rw [Matrix.diagonal_apply_eq]
      exact (units i i.isLt).unit_spec.symm
    · rw [Matrix.diagonal_apply_ne _ h]
      exact cleared i j j.isLt h
  have prod : ∏ j, a j = s := by
    apply Units.ext
    rw [Units.coe_prod,← Matrix.det_diagonal,← diag]
    exact sign
  obtain ⟨z,F,n,hz,hn,rewind,result⟩ := diagonalRewind_exec rows m valid a diag s prod H J hm hw hW
    body u D tail (S.R (bank 1 34)) suffix rest dest q empty original next freeD stream archive
  exact ⟨z,F,l+n,hz.trans hu,Nat.add_le_add hl hn,Exec.seq forward rewind,result⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
