module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryResizeBatchScope

/-! Resize compact stride/residue inputs into the live compiler width, execute
a framed call and erase both installed words. Original input widths may differ. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def matchingControlResizeSlot (j : Fin 2) : Fin 9 → Fin 11 :=
  ![7, (if j = 0 then 0 else 1), 8, (if j = 0 then 2 else 3), 9, 4, 5, 6, 10]

theorem matchingControlResizeSlot_injective (j : Fin 2) : Function.Injective (matchingControlResizeSlot j) := by
  fin_cases j <;> decide +kernel

def matchingControlBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 11 → Fin T)
    (L K r : ℕ) : Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update R (rg 3) (binSyms L r)) (rg 2) (binSyms L K)

def matchingControlScope (rg : Fin 11 → Fin T) (call : Pr P T Q A U) : Pr P T Q A U :=
  binaryResizeBatchScope (fun j => rg ∘ matchingControlResizeSlot j) [0,1] call

theorem matchingControlScope_exec (body : P → Pr P T Q A U)
    (rg : Fin 11 → Fin T) (hrg : Function.Injective rg) (M Lin L K r : ℕ)
    (hL : L < 2 ^ M) (hK : K < 2 ^ Lin) (hr : r < 2 ^ Lin)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg 7) = binSyms M L)
    (hstride : S.R (rg 0) = binSyms Lin K) (hresidue : S.R (rg 1) = binSyms Lin r)
    (hblank : ∀ j : Fin 11, j ≠ 0 → j ≠ 1 → j ≠ 7 → S.R (rg j) = [])
    (str : Fin T) (hstr : str ≠ rg 2 ∧ str ≠ rg 3) (output : List (Fin (A + 4)))
    (call : Pr P T Q A U) (price : ℕ)
    (hcall : ∀ u : HS T Q A U,
      let C : Stacks T A := { S with R := matchingControlBank S.R rg L K r }
      ∃ (u' : HS T Q A U) (m : ℕ), u'.user = u.user ∧ m ≤ price ∧
        Exec body call (mk u C) m (mk u' { C with R := Function.update C.R str output })) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ price + 4 * M * (4 * L + 11) + 24 * Lin + 56 * L + 90 ∧
      Exec body (matchingControlScope rg call) (mk v S) m
        (mk v' { S with R := Function.update S.R str output }) := by
  let slots := fun j => rg ∘ matchingControlResizeSlot j
  let values := fun j : Fin 2 => if j = 0 then K else r
  have hsep : ∀ j i, i ≠ 3 → ∀ k, matchingControlResizeSlot j i ≠ matchingControlResizeSlot k 3 := by decide +kernel
  have hbsep : ∀ j i, i ≠ 0 → i ≠ 1 → i ≠ 3 →
      matchingControlResizeSlot j i ≠ 0 ∧ matchingControlResizeSlot j i ≠ 1 ∧ matchingControlResizeSlot j i ≠ 7 := by decide +kernel
  obtain ⟨v', m, hu, hm, he⟩ := binaryResizeBatchScope_exec body slots
    (fun j => hrg.comp (matchingControlResizeSlot_injective j))
    (fun _ => M) (fun _ => Lin) (fun _ => L) values (fun _ => hL)
    (by intro j; fin_cases j <;> simp [values, hK, hr]) [0,1]
    (by simp [slots, matchingControlResizeSlot, hrg.eq_iff])
    (fun j i hi k => hrg.ne (hsep j i hi k)) L (by intro j hj; exact le_rfl) v S
    (by intro j; fin_cases j <;> simpa [slots, matchingControlResizeSlot] using hwidth)
    (by intro j; fin_cases j <;> simp [slots, matchingControlResizeSlot, values, hstride, hresidue])
    (by intro j hj; fin_cases j <;> apply hblank <;> decide)
    (by intro j i hi0 hi1 hi3
        obtain ⟨h0,h1,h7⟩ := hbsep j i hi0 hi1 hi3
        exact hblank _ h0 h1 h7)
    str (by simp [slots, matchingControlResizeSlot, hstr.1, hstr.2]) output call price
    (by intro u; simpa [binaryResizeBatchBank, slots, matchingControlResizeSlot, values, matchingControlBank] using hcall u)
  refine ⟨v', m, hu, ?_, he⟩
  simp only [binaryResizeBatchCost, List.length_cons, List.length_nil] at hm
  nlinarith only [hm]

end IntegerMultBounds.MathlibTM2.Routing
