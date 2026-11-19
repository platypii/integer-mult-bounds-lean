module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackSwapColumn
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodChildLayout
import IntegerMultBounds.MathlibTM2.Cover.FallbackPrefixVolume

/-! Run the adjacent exchanges with their header setup and cleanup on one tape bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type}
local notation "N" => rowSwapBlock.tapes
local notation "Q" => rowSwapBlock.states
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos prime_prime.pos _).ne'⟩

noncomputable def packSchedule (d : ℕ) : List ℕ → Pr P (N+35) Q prime U
  | [] => .act .done
  | i::is => .seq (completeSwap d i (i+1)) (packSchedule d is)

def adjacentFields {d : ℕ} {α : Type*} (x : Fin d → α) (i : ℕ) : Fin d → α :=
  if h : i+1 < d then x ∘ Equiv.swap ⟨i,by omega⟩ ⟨i+1,h⟩ else x

omit [M8.Machine.Net] in
theorem swapAtomAt_get {α : Type*} (xs : List α) (i : ℕ) (inside : i+1 < xs.length) :
    swapAtomAt i xs = List.ofFn (adjacentFields (fun k : Fin xs.length => xs[k]) i) := by
  induction xs generalizing i with
  | nil => simp at inside
  | cons x xs ih =>
    cases i with
    | zero =>
      cases xs with
      | nil => simp at inside
      | cons y ys =>
        rw [List.ofFn_succ,List.ofFn_succ]
        simp only [swapAtomAt,adjacentFields,dite_eq_left inside,Function.comp_apply]
        congr 1
        congr 1
        conv_lhs => rw [← List.ofFn_getElem (xs := ys)]
        apply congrArg List.ofFn
        funext j
        rw [Equiv.swap_apply_of_ne_of_ne] <;> first | rfl | (intro e; have := congrArg Fin.val e; simp at this)
    | succ i =>
      have hi : i+1 < xs.length := by simpa using inside
      rw [List.ofFn_succ]
      simp only [swapAtomAt,ih i hi,adjacentFields,dite_eq_left inside,dite_eq_left hi,Function.comp_apply]
      congr 1
      apply congrArg List.ofFn
      funext j
      simp only [Function.comp_apply,Equiv.swap_apply_def]
      split_ifs <;> simp_all [Fin.ext_iff, Fin.succ]
      rename_i h₀ h₁
      have ne₀ : j.val ≠ i := fun e => h₀ (Fin.ext e)
      have ne₁ : j.val ≠ i+1 := fun e => h₁ (Fin.ext e)
      simp [ne₀,ne₁]

omit [M8.Machine.Net] in
theorem fold_adjacentFields {α : Type*} {d : ℕ} (is : List ℕ) (x : Fin d → α)
    (fits : ∀ i ∈ is, i+1 < d) :
    List.ofFn (is.foldl adjacentFields x) =
      is.foldl (fun xs i => swapAtomAt i xs) (List.ofFn x) := by
  induction is generalizing x with
  | nil => rfl
  | cons i is ih =>
    have hi := fits i (by simp)
    have step := swapAtomAt_get (List.ofFn x) i (by simpa using hi)
    simp only [List.foldl_cons]
    rw [ih _ (fun j hj => fits j (by simp [hj])),step]
    congr 1
    simp
    funext j
    simp [adjacentFields,hi,Equiv.swap_apply_def,Function.comp_apply, Fin.ext_iff]
    split_ifs <;> rfl

/-- Keep the active head in place while moving the active tail over both gap slices. -/
def goodChildPackSchedule (r g : ℕ) : List ℕ :=
  (middleTailSchedule (g+g) r).map (r+·)

omit [M8.Machine.Net] in
theorem goodChildPackSchedule_inside {r g i : ℕ} (used : i ∈ goodChildPackSchedule r g) :
    i+1 < (r+g)+(r+g) := by
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp used
  have := middleTailSchedule_inside hj
  omega

omit [M8.Machine.Net] in
theorem goodChildPackSchedule_fields {α : Type*} {r g : ℕ}
    (x : Fin ((r+g)+(r+g)) → α) (head mid tail : List α)
    (hr : head.length = r) (hm : mid.length = g+g) (ht : tail.length = r)
    (layout : List.ofFn x = head++mid++tail) :
    List.ofFn ((goodChildPackSchedule r g).foldl adjacentFields x) = head++tail++mid := by
  rw [fold_adjacentFields _ _ (fun _ => goodChildPackSchedule_inside),layout]
  simp only [goodChildPackSchedule,List.foldl_map,List.append_assoc]
  rw [← hr,fold_swapAtomAt_prefix,hr,← hm,← ht]
  simpa using congrArg (head++·) (middleTailSchedule_packs mid tail [])

/-- Generating and retiring the headers costs a quadratic field-width term
and a linear suffix-counter term for each fixed packing schedule. -/
theorem packSchedule_setup_le [Fintype P] (body : P → Pr P (N+35) Q prime U)
    (d : ℕ) (is : List ℕ) :
    ∃ C : ℕ, ∀ w H J, (is.map (fun i => completeSwapTime body d i (i+1) w 0 H J)).sum+1 ≤
      C*(w+1+(H+1)^2+J) := by
  induction is with
  | nil => exact ⟨1,by intros; simp; omega⟩
  | cons i is ih =>
    obtain ⟨C,rest⟩ := ih
    obtain ⟨a,base⟩ := completeSwapTime_setup_le body d i (i+1)
    have counter : ∃ b : ℕ, ∀ w H J, completeSwapTime body d i (i+1) w 0 H J =
        completeSwapTime body d i (i+1) w 0 H 0 + b*J :=
      ⟨_,fun w H J => completeSwapTime_eq_setup_add_counter body d i (i+1) w 0 H J⟩
    obtain ⟨b,counter⟩ := counter
    refine ⟨a+b+C,?_⟩
    intro w H J
    simp only [List.map_cons,List.sum_cons,counter w H J,Nat.add_mul]
    have := rest w H J
    have := (base w H).trans (Nat.mul_le_mul_left a (Nat.le_add_right _ J))
    have := Nat.mul_le_mul_left b (Nat.le_add_left J (w+1+(H+1)^2))
    omega

/-- A fixed packing schedule incurs a single width-dependent rate on the parent volume. -/
theorem packSchedule_volume_le [Fintype P] (body : P → Pr P (N+35) Q prime U)
    (d : ℕ) (is : List ℕ) :
    ∃ C : ℕ, ∀ w W H J,
      (is.map (fun i => completeSwapTime body d i (i+1) w W H J)).sum + 1 ≤
      (is.map (fun i => completeSwapTime body d i (i+1) w 0 H J)).sum + 1 +
        C * swapVolumeRate w * ((prime^(w+1))^d * W) := by
  induction is with
  | nil => exact ⟨0,by simp⟩
  | cons i is ih =>
    obtain ⟨C,rest⟩ := ih
    have step : ∃ c : ℕ, ∀ w W H J, completeSwapTime body d i (i+1) w W H J ≤
        completeSwapTime body d i (i+1) w 0 H J + c * swapVolumeRate w * ((prime^(w+1))^d * W) :=
      ⟨_,fun w W H J => completeSwapTime_le_setup_add_volume body d i (i+1) w W H J⟩
    obtain ⟨c,step⟩ := step
    refine ⟨c+C,?_⟩
    intro w W H J
    simp only [List.map_cons,List.sum_cons,Nat.add_mul]
    have := step w W H J
    have := rest w W H J
    omega

/-- At the parent's binary counter widths the setup is linear in its volume.
Only the row exchanges incur the atom-width factor. -/
theorem goodChildPackTime_le [Fintype P] (body : P → Pr P (N+35) Q prime U)
    (r g : ℕ) (positive : 0 < r+g) :
    ∃ setup swaps : ℕ, ∀ w W, 0 < W →
      let d := (r+g)+(r+g)
      let M := prime^(w+1)
      let H := Nat.size M
      let J := Nat.size W
      ((goodChildPackSchedule r g).map (fun i => completeSwapTime body d i (i+1) w W H J)).sum+1 ≤
        (setup + swaps*swapVolumeRate w)*(M^d*W) := by
  let d := (r+g)+(r+g)
  let c := 2*(Nat.size prime+1)^2
  obtain ⟨a,base⟩ := packSchedule_setup_le body d (goodChildPackSchedule r g)
  obtain ⟨b,run⟩ := packSchedule_volume_le body d (goodChildPackSchedule r g)
  refine ⟨a*(c+1),b,?_⟩
  intro w W hW _ M H J
  have dim : d-1+1 = d := by dsimp [d]; omega
  have field := prefixSetup_volume_le w (d-1)
  change (w+1+M^(d-1))*(H+1)^2 ≤ c*M^(d-1+1) at field
  rw [dim] at field
  have digits : 0 < M^(d-1) := pow_pos (pow_pos prime_prime.pos _) _
  have bits : 0 < (H+1)^2 := pow_pos (by omega) _
  have h : w+1+(H+1)^2 ≤ c*M^d := by
    apply le_trans _ field
    rw [Nat.add_mul]
    exact Nat.add_le_add (Nat.le_mul_of_pos_right _ bits) (Nat.le_mul_of_pos_left _ digits)
  have volume : 0 < M^d := pow_pos (pow_pos prime_prime.pos _) _
  have len : J ≤ W := Nat.size_le.mpr Nat.lt_two_pow_self
  have cost := base w H J
  have headers := Nat.add_le_add (h.trans (Nat.mul_le_mul_left c (Nat.le_mul_of_pos_right _ hW)))
    (len.trans (Nat.le_mul_of_pos_left W volume))
  have total := (run w W H J).trans (Nat.add_le_add_right (cost.trans (Nat.mul_le_mul_left a headers)) _)
  exact total.trans_eq (by dsimp only [d] at *; ring)

theorem packSchedule_exec [Fintype P] {d w W : ℕ} (is : List ℕ) (fits : ∀ i ∈ is, i+1 < d)
    (H J : ℕ) (hm : prime^(w+1) < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P (N+35) Q prime U) (v : HS (N+35) Q prime U) (S : Stacks (N+35) prime)
    (record : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (original : Fin ((prime^(w+1))^d*W) → ZMod 2)
    (addr : (Fin d → ZMod (prime^(w+1))) → Fin d → ZMod (prime^(w+1))) :
    let bank : Fin 35 ↪ Fin (N+35) := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let ready := ColumnRecordReady bank H J record SparseRoleCircuit.encode (fun _ => blank) dest 0 q original
    let clean := fun (D : Stacks (N+35) prime) => ∀ k : Fin (N+35), 35 ≤ k.val → D.L k = [] ∧ D.R k = []
    ready addr S → clean S → ∃ z F n, z.user = v.user ∧
      n ≤ (is.map (fun i => completeSwapTime body d i (i+1) w W H J)).sum+1 ∧
      Exec body (packSchedule d is) (mk v S) n (mk z F) ∧
      ready (fun x => is.foldl adjacentFields (addr x)) F ∧ clean F := by
  intro bank ready clean start free
  induction is generalizing v S addr with
  | nil => exact ⟨v,S,1,rfl,by simp,Exec.act _ _,start,free⟩
  | cons i is ih =>
    have hi := fits i (by simp)
    let a : Fin d := ⟨i,by omega⟩
    let b : Fin d := ⟨i+1,hi⟩
    obtain ⟨u,D,t,user,cost,swap,next,empty⟩ := columnRecord_swap a b (by change i < i+1; omega)
      H J hm hw hW body v S record dest q original addr start free
    obtain ⟨z,F,n,hz,hn,run,done,clear⟩ := ih (fun j h => fits j (by simp [h])) u D
      (fun x => addr x ∘ Equiv.swap a b) next empty
    refine ⟨z,F,t+n,hz.trans user,?_,.seq swap run,?_,clear⟩
    · simp only [List.map_cons,List.sum_cons,Nat.add_assoc]
      exact Nat.add_le_add cost hn
    · simpa only [List.foldl_cons,adjacentFields,dite_eq_left hi] using done

/-- Execute the good child's packing on the caller's bank with its actual
binary headers, retaining a fieldwise description of the returned address. -/
theorem goodChildPack_exec [Fintype P] (body : P → Pr P (N+35) Q prime U)
    (r g : ℕ) (positive : 0 < r+g) :
    ∃ setup swaps : ℕ, ∀ w W, 0 < W →
      let d := (r+g)+(r+g)
      let M := prime^(w+1)
      let bank := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
      let clean := fun (S : Stacks (N+35) prime) => ∀ k : Fin (N+35), 35 ≤ k.val → S.L k = [] ∧ S.R k = []
      ∀ (v : HS (N+35) Q prime U) (S : Stacks (N+35) prime)
        (record : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
        (original : Fin (M^d*W) → ZMod 2) (addr : (Fin d → ZMod M) → Fin d → ZMod M),
      let ready := ColumnRecordReady bank (Nat.size M) (Nat.size W) record SparseRoleCircuit.encode
        (fun _ => blank) dest 0 q original
      ready addr S → clean S → ∃ z F n packed, z.user = v.user ∧
        n ≤ (setup+swaps*swapVolumeRate w)*(M^d*W) ∧
        Exec body (packSchedule d (goodChildPackSchedule r g)) (mk v S) n (mk z F) ∧
        ready packed F ∧ clean F ∧
        ∀ x (head mid tail : List (ZMod M)), head.length = r → mid.length = g+g → tail.length = r →
          List.ofFn (addr x) = head++mid++tail → List.ofFn (packed x) = head++tail++mid := by
  obtain ⟨setup,swaps,bound⟩ := goodChildPackTime_le body r g positive
  refine ⟨setup,swaps,?_⟩
  intro w W hW d M bank clean v S record dest q original addr ready start free
  obtain ⟨z,F,n,user,cost,run,placed,clear⟩ := packSchedule_exec (goodChildPackSchedule r g)
    (fun _ => goodChildPackSchedule_inside) (Nat.size M) (Nat.size W)
    (Nat.size_le.mp le_rfl) (Nat.size_le.mp le_rfl) hW body v S record dest q original addr start free
  exact ⟨z,F,n,_,user,cost.trans (bound w W hW),run,placed,clear,
    fun x => goodChildPackSchedule_fields (addr x)⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
