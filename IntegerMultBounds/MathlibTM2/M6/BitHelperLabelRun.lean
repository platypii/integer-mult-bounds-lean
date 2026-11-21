module

public import IntegerMultBounds.MathlibTM2.M6.BitHelperLabelGap
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryDirectoryLeaf

/-! Stopped helper-slot packing on a permanent owner with reusable descriptor headers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
variable [M8.Machine.Net] {n Q : ℕ} {P U : Type}

noncomputable def helperLabelProgram (capacity : columnCapacity ≤ Q)
    (headers : ℕ → Fin 6 → Fin n) (owner : Fin n) : List ℕ → Pr P (n+LeafCore.small) Q prime U
  | [] => .act .done
  | i::is => .seq (hostedStoppedDirectory capacity (headers i) owner)
      (helperLabelProgram capacity headers owner is)

omit [M8.Machine.Net] in
private theorem payload_cast {N V T : ℕ} (eq : N = V) (port : Fin T) (S : Stacks T prime)
    (word : Fin V → ZMod 2) :
    RecordPayload port (fun _ => blank) 0 (fun i => word (Fin.cast eq i)) S ↔
      RecordPayload port (fun _ => blank) 0 word S := by subst V; rfl

/-- One owner and one private workspace suffice for the entire schedule. Every
archived header survives each call, and each leaf's copy and cleanup are charged. -/
theorem helperLabelProgram_exec {w L W : ℕ} {v : Descriptor}
    (size : volume prime v = (prime^w)^16*(L*((prime^w)^112*W))) (positive : 0 < volume prime v)
    (capacity : columnCapacity ≤ Q) (body : P → Pr P (n+LeafCore.small) Q prime U)
    (headers : ℕ → Fin 6 → Fin n) (owner : Fin n) (is : List ℕ)
    (fits : ∀ i ∈ is, i < 127) (separate : ∀ i ∈ is, ∀ j, headers i j ≠ owner) :
    let view := fun i : ℕ => helperAdjacentView w L W (Fin.ofNat 127 i)
    let rate := ((LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|))*
      ((volume prime v : ℝ)*((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)
    ∀ word (u : HS (n+LeafCore.small) Q prime U) (S : Stacks (n+LeafCore.small) prime),
      (∀ i ∈ is, ∀ j, S.R ((headers i j).castAdd LeafCore.small) = (Routines.hdr (view i) j).map bitSymbol) →
      RecordPayload (owner.castAdd LeafCore.small) (fun _ => blank) 0 word S →
      (∀ j : Fin LeafCore.small, S.L (j.natAdd n) = [] ∧ S.R (j.natAdd n) = []) →
      ∃ z F k, z.user = u.user ∧ Exec body (helperLabelProgram capacity headers owner is) (mk u S) k (mk z F) ∧
        (k : ℝ) ≤ (is.map (fun i => descriptorHeaderCost (view i)+rate)).sum+1 ∧
        RecordPayload (owner.castAdd LeafCore.small) (fun _ => blank) 0 (is.foldl (helperPackingStep size) word) F ∧
        (∀ j : Fin n, j ≠ owner → F.L (j.castAdd LeafCore.small) = S.L (j.castAdd LeafCore.small) ∧
          F.R (j.castAdd LeafCore.small) = S.R (j.castAdd LeafCore.small)) ∧
        ∀ j : Fin LeafCore.small, F.L (j.natAdd n) = [] ∧ F.R (j.natAdd n) = [] := by
  intro view rate
  induction is with
  | nil =>
    intro word u S _ payload free
    exact ⟨u,S,1,rfl,Exec.act ..,by simp,payload,fun _ _ => ⟨rfl,rfl⟩,free⟩
  | cons i is ih =>
    intro word u S stored payload free
    have hi := fits i (by simp)
    have eq : volume prime (view i) = volume prime v := (helperAdjacent_volume ..).trans size.symm
    let input := fun t => word (Fin.cast eq t)
    obtain ⟨z,D,k,user,run,paid,out,_,keep,clear⟩ := hostedStoppedView_exec capacity body (headers i) owner
      (view i) input u S (eq.symm ▸ positive) (stored i (by simp)) ((payload_cast eq _ S word).mpr payload) free
    have index : (Fin.ofNat 127 i) = (⟨i,hi⟩ : Fin 127) := Fin.ext (Nat.mod_eq_of_lt hi)
    have next := (payload_cast eq.symm _ D (Shared50RecursiveNodeRows.transpose (one_dvd (view i).rows) input)).mpr out
    have output : RecordPayload (owner.castAdd LeafCore.small) (fun _ => blank) 0 (helperPackingStep size word i) D := by
      unfold helperPackingStep
      rw [dite_eq_left hi]
      let atIndex := fun t : Fin 127 => RevSemantics.leafOut (helperAdjacentView w L W t)
        ((helperAdjacent_volume ..).trans size.symm) word
      change RecordPayload _ _ _ (atIndex ⟨i,hi⟩) D
      rw [← index]
      exact next
    obtain ⟨y,F,m,same,rest,bill,final,other,clean⟩ := ih (fun t ht => fits t (by simp [ht]))
      (fun t ht => separate t (by simp [ht])) _ z D (fun t ht j =>
        ((keep _ (separate t (by simp [ht]) j)).2).trans (stored t (by simp [ht]) j)) output clear
    refine ⟨y,F,k+m,same.trans user,Exec.seq run rest,?_,final,?_,clean⟩
    · rw [eq] at paid
      change (k : ℝ) ≤ descriptorHeaderCost (view i)+rate at paid
      simp only [List.map_cons,List.sum_cons,Nat.cast_add]
      linarith
    · intro j hj
      exact ⟨(other j hj).1.trans (keep j hj).1,(other j hj).2.trans (keep j hj).2⟩

/-- Choose a single hosted program and coefficient from the slot change. Both work
for every positive caller volume, including the first use of a pending helper. -/
theorem helperLabelSlot_exec (src dst : Option (Fin 56)) (capacity : columnCapacity ≤ Q)
    (body : P → Pr P (n+LeafCore.small) Q prime U) (headers : ℕ → Fin 6 → Fin n) (owner : Fin n)
    (separate : ∀ i j, headers i j ≠ owner) :
    ∃ (code : Pr P (n+LeafCore.small) Q prime U) (C : ℝ), ∀ {w L W : ℕ} {v : Descriptor}
      (size : volume prime v = (prime^w)^16*(L*((prime^w)^112*W))) (positive : 0 < volume prime v)
      (word : Fin (volume prime v) → ZMod 2) (u : HS (n+LeafCore.small) Q prime U) (S : Stacks (n+LeafCore.small) prime),
      (∀ i : Fin 127, ∀ j, S.R ((headers i.val j).castAdd LeafCore.small) =
        (Routines.hdr (helperAdjacentView w L W i) j).map bitSymbol) →
      RecordPayload (owner.castAdd LeafCore.small) (fun _ => blank) 0 word S →
      (∀ j : Fin LeafCore.small, S.L (j.natAdd n) = [] ∧ S.R (j.natAdd n) = []) →
      ∃ z F k, ∃ out : Fin (volume prime v) → ZMod 2, z.user = u.user ∧ Exec body code (mk u S) k (mk z F) ∧
        (k : ℝ) ≤ C*((volume prime v : ℝ)*((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) ∧
        RecordPayload (owner.castAdd LeafCore.small) (fun _ => blank) 0 out F ∧
        (∀ c s label j, ext out (helperFieldCell (helperSlotField c dst w s) label j) =
          ext word (helperFieldCell (helperSlotField c src w s) (label : Fin L) (j : Fin W))) ∧
        (∀ j : Fin n, j ≠ owner → F.L (j.castAdd LeafCore.small) = S.L (j.castAdd LeafCore.small) ∧
          F.R (j.castAdd LeafCore.small) = S.R (j.castAdd LeafCore.small)) ∧
        ∀ j : Fin LeafCore.small, F.L (j.natAdd n) = [] ∧ F.R (j.natAdd n) = [] := by
  obtain ⟨is,fits,reads⟩ := helperLabelPacking src dst
  let A : ℝ := (LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|)
  refine ⟨helperLabelProgram capacity headers owner is,is.length*(110+A)+1,?_⟩
  intro w L W v size positive word u S stored payload free
  have valid (i) (h : i ∈ is) : i < 127 := by have := fits i h; omega
  obtain ⟨z,F,k,user,run,cost,out,keep,clean⟩ := helperLabelProgram_exec size positive capacity body
    headers owner is valid (fun i _ => separate i) word u S (fun i h j => by
      have e : Fin.ofNat 127 i = ⟨i,valid i h⟩ := Fin.ext (Nat.mod_eq_of_lt (valid i h))
      dsimp only; rw [e]; exact stored ⟨i,valid i h⟩ j) payload free
  refine ⟨z,F,k,_,user,run,?_,out,reads size word,keep,clean⟩
  let V : ℝ := volume prime v
  let unit := V*((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
  have vol : 1 ≤ V := by dsimp only [V]; exact_mod_cast (show 1 ≤ volume prime v from positive)
  have base : V ≤ unit := le_mul_of_one_le_right (by positivity : 0 ≤ (volume prime v : ℝ))
    (Real.one_le_rpow (by exact_mod_cast le_max_left 1 w) M8.Machine.BudgetBound.exponent_range.1.le)
  let bill := fun i : ℕ => (descriptorHeaderCost (helperAdjacentView w L W (Fin.ofNat 127 i)) : ℝ)+A*unit
  have each (i : ℕ) : bill i ≤ (110+A)*unit := by
    let d := helperAdjacentView w L W (Fin.ofNat 127 i)
    have eq : volume prime d = volume prime v := (helperAdjacent_volume ..).trans size.symm
    have bounded := descriptorHeaderCost_le d (LeafCore.positive_of_volume (eq.symm ▸ positive))
    rw [eq] at bounded
    have realBound : (descriptorHeaderCost d : ℝ) ≤ 110*V := by dsimp only [V]; exact_mod_cast bounded
    change (descriptorHeaderCost d : ℝ)+A*unit ≤ _
    linarith
  have total := List.sum_le_length_nsmul (is.map bill) ((110+A)*unit)
    (fun x hx => by obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx; exact each i)
  simp only [List.length_map,nsmul_eq_mul] at total
  change (k : ℝ) ≤ (is.map bill).sum+1 at cost
  change (k : ℝ) ≤ (_+1)*unit
  rw [add_mul,one_mul,mul_assoc]
  exact cost.trans (add_le_add total (vol.trans base))

end IntegerMultBounds.MathlibTM2.M6.BitNode
