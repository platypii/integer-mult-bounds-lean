module

public import IntegerMultBounds.MathlibTM2.M6.BitHelperFanRun
public import IntegerMultBounds.MathlibTM2.M6.BitHelperParentSeeds

/-! Execute the scheduled PR589 helper packing from the row descriptor and row registers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
local notation "N" => LeafCore.small
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

private theorem banksApart {a b : ℕ} (i : Fin a) (j : Fin b) : i.castAdd b ≠ j.natAdd a := by
  intro e
  have h := congrArg Fin.val e
  change i.val = a+j.val at h
  omega

private theorem parentHeader_ne {T : ℕ} (i : Fin 127) (j : Fin 6) (k : Fin T) :
    parentHelperHeaders T i j ≠ k.castAdd 273 := by
  intro eq
  have h := congrArg Fin.val eq
  have lt := k.isLt
  fin_cases j <;> simp [parentHelperHeaders,helperHeaderPorts,parentArchive] at h <;>
    first | omega | (split_ifs at h <;> simp only [Fin.val_natAdd] at h <;> omega)

private theorem placedParentHeaders {P U : Type} {T Q tail : ℕ}
    (body : P → Pr P ((T+273)+tail) Q prime U) (hdr : Fin 6 → Fin T) (regs : Fin 35 ↪ Fin T)
    (row : Descriptor) (w : ℕ) (pos : row.Positive) (u : HS ((T+273)+tail) Q prime U) (S : Stacks ((T+273)+tail) prime) :
    let bank := Fin.castAddEmb tail (n := T+273)
    let caller := (Fin.castAddEmb 273 (n := T)).trans bank
    let W := row.beforeRows*row.rows*row.between*row.afterD
    let M := prime^(w+1)
    S.R (caller (regs 2)) = binSyms M.size M → S.R (caller (regs 28)) = binSyms 1 1 →
    (S.R (caller (regs 33))).length = w →
    (∀ i, S.R (caller (hdr i)) = (Routines.hdr row i).map bitSymbol) →
    (∀ j : Fin 273, S.L (bank (j.natAdd T)) = [] ∧ S.R (bank (j.natAdd T)) = []) →
    ∃ y D m, Exec body (embProg bank (Empty.elim : Empty → P) (prepareHelperHeaders hdr regs)) (mk u S) m (mk y D) ∧
      y.user = u.user ∧ m ≤ 152402000*(M^128*(row.beforeH*W)) ∧
      (∀ i j, D.R (bank (parentHelperHeaders T i j)) = (Routines.hdr (helperAdjacentView (w+1) row.beforeH W i) j).map bitSymbol) ∧
      (∀ j : Fin T, D.L (caller j) = S.L (caller j) ∧ D.R (caller j) = S.R (caller j)) ∧
      ∀ j : Fin tail, D.L (j.natAdd (T+273)) = S.L (j.natAdd (T+273)) ∧ D.R (j.natAdd (T+273)) = S.R (j.natAdd (T+273)) := by
  intro bank caller W M base unit clock words free
  obtain ⟨y,D,m,same,setup,charge,ready,left,keep⟩ := prepareHelperHeaders_exec
    (P := Empty) Empty.elim hdr regs row w pos (embDn bank u) (embStk bank S) base unit clock words free
  obtain ⟨y',D',placed,_,same',project,off⟩ := exec_emb (ι := (Empty.elim : Empty → P)) (body' := body)
    bank.injective (fun f => nomatch f) setup u rfl S rfl
  have original (j : Fin T) : D'.L (caller j) = S.L (caller j) ∧ D'.R (caller j) = S.R (caller j) := by
    have left := congrArg Stacks.L project |>.trans left
    have keep (k : Fin T) := (congrFun (congrArg Stacks.R project) (k.castAdd 273)).trans (keep k)
    exact ⟨congrFun left (j.castAdd 273),keep j⟩
  have clean (j : Fin tail) := off (j.natAdd (T+273)) (fun i => banksApart i j)
  refine ⟨y',D',m,placed,same'.trans same,charge,?_,original,clean⟩
  intro i j
  exact (congrFun (congrArg Stacks.R project) (parentHelperHeaders T i j)).trans (ready i j)

/-- The entire preparation and packing cost is independent of the child-call budget.
All invocation controls and all caller tapes outside the owners keep their stacks. -/
theorem parentSlotChanges_exec [M8.Machine.Net] {P U : Type} {T Q : ℕ}
    (changes : List (Fin 142081 × Option (Fin 56) × Option (Fin 56)))
    (fan : Fin (142081+2) ↪ Fin T) (hdr : Fin 6 → Fin T) (regs : Fin 35 ↪ Fin T)
    (capacity : columnCapacity ≤ Q) (body : P → Pr P ((T+273)+N) Q prime U) :
    let bank := Fin.castAddEmb N (n := T+273)
    let caller := (Fin.castAddEmb 273 (n := T)).trans bank
    ∃ code, ∃ C : ℝ, ∀ (row : Descriptor) (w V : ℕ), row.Positive →
      let W := row.beforeRows*row.rows*row.between*row.afterD
      let M := prime^(w+1)
      V = M^16*(row.beforeH*(M^112*W)) →
      ∀ (data : Fin 142081 → Fin V → ZMod 2) u S,
      S.R (caller (regs 2)) = binSyms M.size M → S.R (caller (regs 28)) = binSyms 1 1 →
      (S.R (caller (regs 33))).length = w →
      (∀ i, S.R (caller (hdr i)) = (Routines.hdr row i).map bitSymbol) →
      (∀ j : Fin 273, S.L (bank (j.natAdd T)) = [] ∧ S.R (bank (j.natAdd T)) = []) →
      (∀ j : Fin N, S.L (j.natAdd (T+273)) = [] ∧ S.R (j.natAdd (T+273)) = []) →
      HelperFan (fan.trans caller) data S →
      ∃ z F t a, z.user = u.user ∧ Exec body code (mk u S) t (mk z F) ∧
        (t : ℝ) ≤ C*(V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) ∧
        HelperFan (fan.trans caller) a F ∧ HelperLabelTrace (w+1) row.beforeH W changes data a ∧
        ∀ j : Fin T, (∀ o : Fin 142081, j ≠ fan (o.castAdd 2)) →
          F.L (caller j) = S.L (caller j) ∧ F.R (caller j) = S.R (caller j) := by
  intro bank caller
  let shared := fan.trans (Fin.castAddEmb 273)
  let headers := fun i : ℕ => parentHelperHeaders T (Fin.ofNat 127 i)
  have distinct (i j o) : headers i j ≠ shared (Fin.castAdd 2 o) := parentHeader_ne (Fin.ofNat 127 i) j (fan (o.castAdd 2))
  let C := helperChangesRate changes
  obtain ⟨pack,run⟩ := helperFanChanges_exec shared changes capacity body headers distinct
  let prep : Pr Empty (T+273) Q prime U := prepareHelperHeaders hdr regs
  refine ⟨.seq (embProg bank Empty.elim prep) pack,152402000+C,?_⟩
  intro row w V pos W M size
  let view := helperAdjacentView (w+1) row.beforeH W 15
  have volumeEq : volume prime view = V := (helperAdjacent_volume ..).trans size.symm
  cases volumeEq
  intro data u S base unit clock words free scratch represented
  obtain ⟨y',D',m,placed,same,charge,ready,original,clean⟩ :=
    placedParentHeaders (tail := N) body hdr regs row w pos u S base unit clock words free
  have rep : HelperFan (fan.trans caller) data D' := by
    intro i z
    change _ = readAt blank (D'.L (caller (fan i))) (D'.R (caller (fan i))) _
    have h : D'.L (caller (fan i)) = S.L (caller (fan i)) ∧ D'.R (caller (fan i)) = S.R (caller (fan i)) := original (fan i)
    rw [h.1,h.2]
    exact represented i z
  have vol : M^128*(row.beforeH*W) = volume prime view := by rw [size,show M^128 = M^16*M^112 from (pow_add M 16 112)]; ring
  have positive : 0 < volume prime view := by
    rw [← vol]
    exact Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
      (Nat.mul_pos pos.2.2.1 (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos pos.1 pos.2.1) pos.2.2.2.1) pos.2.2.2.2))
  obtain ⟨z,F,k,a,user,exec,paid,done,trace,other,_⟩ := run size positive data y' D' (fun i j => by
    simpa only [W,embStk,Function.comp_apply,bank,Fin.castAddEmb_apply,headers,show Fin.ofNat 127 i.val = i from Fin.ext (Nat.mod_eq_of_lt i.isLt)] using ready i j)
    rep (fun j => ⟨(clean j).1.trans (scratch j).1,(clean j).2.trans (scratch j).2⟩)
  refine ⟨z,F,m+k,a,user.trans same,Exec.seq placed exec,?_,done,trace,?_⟩
  · change m ≤ 152402000*(M^128*(row.beforeH*W)) at charge
    rw [vol] at charge
    have bound : (m : ℝ) ≤ 152402000*(volume prime view : ℝ) := by exact_mod_cast charge
    have power := Real.one_le_rpow (by exact_mod_cast (Nat.le_add_left 1 w) : (1 : ℝ) ≤ (w+1 : ℕ))
      M8.Machine.BudgetBound.exponent_range.1.le
    simp only [Nat.max_eq_right (by omega : 1 ≤ w+1)] at paid
    rw [Nat.cast_add,add_mul]
    exact add_le_add (bound.trans (by rw [← mul_assoc]; exact le_mul_of_one_le_right (by positivity) power)) paid
  · intro j hj
    have unchanged := other (j.castAdd 273) (fun o => (Fin.castAddEmb 273).injective.ne (hj o))
    exact ⟨unchanged.1.trans (original j).1,unchanged.2.trans (original j).2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
