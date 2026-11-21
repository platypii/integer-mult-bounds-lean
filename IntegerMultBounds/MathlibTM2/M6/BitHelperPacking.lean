module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPackSchedule
public import IntegerMultBounds.MathlibTM2.M6.BitRouteFactors
import Mathlib.Data.List.FinRange

/-! Reorder the two packed parent fields when an owner changes helper slots. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open IntegerMultBounds.Networks.Certificates.PR589.Nine
open Cover.Fallback
open scoped Matrix

private theorem adjacentSchedule {α : Type*} {xs ys : List α} (perm : xs.Perm ys) :
    ∃ is : List ℕ, (∀ i ∈ is, i+1 < xs.length) ∧
      is.foldl (fun as i => swapAtomAt i as) xs = ys := by
  induction perm with
  | nil => exact ⟨[],by simp,rfl⟩
  | cons a _ ih =>
    obtain ⟨is,fits,run⟩ := ih
    refine ⟨is.map (1+·),?_,?_⟩
    · intro i hi
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
      have := fits j hj
      simp only [List.length_cons]; omega
    · rw [List.foldl_map]
      exact (fold_swapAtomAt_prefix [a] is _).trans (congrArg ([a]++·) run)
  | swap a b xs => exact ⟨[0],by simp,rfl⟩
  | trans h _ ih ih' =>
    obtain ⟨is,fits,run⟩ := ih
    obtain ⟨js,fits',run'⟩ := ih'
    exact ⟨is++js,fun i hi => (List.mem_append.mp hi).elim (fits i)
      (fun hj => h.length_eq.symm ▸ fits' i hj),by rw [List.foldl_append,run,run']⟩

private theorem fieldSchedule {d : ℕ} (order : Equiv.Perm (Fin d)) :
    ∃ is : List ℕ, (∀ i ∈ is, i+1 < d) ∧
      ∀ {α : Type} (x : Fin d → α), is.foldl adjacentFields x = x ∘ order := by
  obtain ⟨is,fits,run⟩ := adjacentSchedule (order.ofFn_comp_perm id).symm
  simp only [List.length_ofFn] at fits
  have acts : is.foldl adjacentFields id = ⇑order := by
    apply List.ofFn_injective
    exact (fold_adjacentFields is id fits).trans run
  refine ⟨is,fits,?_⟩
  intro α x
  suffices natural : ∀ (js : List ℕ) (a : Fin d → Fin d),
      js.foldl adjacentFields (x ∘ a) = x ∘ js.foldl adjacentFields a by
    simpa only [Function.comp_id,acts] using natural is id
  intro js
  induction js with
  | nil => intro a; rfl
  | cons i js ih =>
    intro a
    simp only [List.foldl_cons,adjacentFields]
    split <;> apply ih

/-- The tape orders both live halves before the two exterior halves. -/
def helperDigits : Fin 128 ≃ Axis ⊕ Axis :=
  let exterior : Fin 56 ≃ Exterior := (@finProdFinEquiv 8 7).symm
  let live : Fin 16 ≃ Fin 8 ⊕ Fin 8 := (@finSumFinEquiv 8 8).symm
  let tail : Fin 112 ≃ Exterior ⊕ Exterior :=
    (@finSumFinEquiv 56 56).symm.trans (Equiv.sumCongr exterior exterior)
  (@finSumFinEquiv 16 112).symm.trans ((Equiv.sumCongr live tail).trans (Equiv.sumSumSumComm ..))

/-- The address obtained by the tape permutation reads precisely the next
slot chart, including the digits that used to belong to the exterior. -/
theorem helperDigits_reindex (c : PortCertificate) (x y : ℕ) (hx : x ≤ 55) (hy : y ≤ 55)
    (w : ℕ) (s : IntegerMultBounds.Swap.Shear.State Axis (ZMod (prime^w))) :
    let field := fun k hk =>
      let H := (IntegerMultBounds.Swap.Modular.reduce (prime^w) (c.helperChart k hk)).transpose
      (Sum.elim (H *ᵥ s.1) (H *ᵥ s.2)) ∘ helperDigits
    let order := (helperSlotOrder y hy).trans (helperSlotOrder x hx).symm
    field x hx ∘ helperDigits.trans ((Equiv.sumCongr order order).trans helperDigits.symm) = field y hy := by
  intro field order
  funext i
  simp only [field,Function.comp_apply,Equiv.trans_apply,Equiv.apply_symm_apply]
  cases helperDigits i with
  | inl j => exact (congrFun (helperSlot_reindex c x y hx hy w s.1) j).symm
  | inr j => exact (congrFun (helperSlot_reindex c x y hx hy w s.2) j).symm

variable [M8.Machine.Net] {P U : Type}
local notation "N" => rowSwapBlock.tapes
local notation "Q" => rowSwapBlock.states
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos prime_prime.pos _).ne'⟩

/-- The same machine works at every positive digit width. It permutes the
coordinates of both fields and leaves the trailing spectator in place. -/
theorem helperSlotPack_exec [Fintype P] (body : P → Pr P (N+35) Q prime U)
    (x y : ℕ) (hx : x ≤ 55) (hy : y ≤ 55) :
    let order := (helperSlotOrder y hy).trans (helperSlotOrder x hx).symm
    let perm := helperDigits.trans ((Equiv.sumCongr order order).trans helperDigits.symm)
    ∃ (code : Pr P (N+35) Q prime U) (setup swaps : ℕ), ∀ w W, 0 < W →
      let M := prime^(w+1)
      let bank := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
      let clean := fun (S : Stacks (N+35) prime) => ∀ k : Fin (N+35), 35 ≤ k.val → S.L k = [] ∧ S.R k = []
      ∀ (v : HS (N+35) Q prime U) (S : Stacks (N+35) prime)
        (record : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
        (original : Fin (M^128*W) → ZMod 2) (addr : (Fin 128 → ZMod M) → Fin 128 → ZMod M),
      let ready := ColumnRecordReady bank M.size W.size record SparseRoleCircuit.encode
        (fun _ => blank) dest 0 q original
      ready addr S → clean S → ∃ z F n, z.user = v.user ∧
        n ≤ (setup+swaps*swapVolumeRate w)*(M^128*W) ∧
        Exec body code (mk v S) n (mk z F) ∧ ready (fun a => addr a ∘ perm) F ∧ clean F := by
  intro order perm
  obtain ⟨is,fits,acts⟩ := fieldSchedule perm
  obtain ⟨setup,swaps,bound⟩ := packTime_le body 128 is (by decide)
  refine ⟨packSchedule 128 is,setup,swaps,?_⟩
  intro w W hW M bank clean v S record dest q original addr ready start free
  obtain ⟨z,F,n,user,cost,run,placed,clear⟩ := packSchedule_exec is fits M.size W.size
    (Nat.size_le.mp le_rfl) (Nat.size_le.mp le_rfl) hW body v S record dest q original addr start free
  exact ⟨z,F,n,user,cost.trans (bound w W hW),run,by simpa only [acts] using placed,clear⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
