import IntegerMultBounds.Machine.RoleArrayStackMoves

/-! Destructive parking and recovery of one arbitrary-symbol role array.
The vacated role and work clock are physically blank/head-zero between calls;
only the payload stack's runtime position and the immutable count survive. -/
namespace IntegerMultBounds.Machine.RoleArrayStack
open RoleArrayStackMoves
variable {a : ℕ}
noncomputable section

def Supported (f : ℤ → Fin (a+4)) (n : ℕ) : Prop :=
  ∀ z, z < 0 ∨ (n : ℤ) ≤ z → f z = blank

/-- Ordinary raw payload words satisfy the support condition, including
arbitrary blank/separator symbols inside the finite array. -/
theorem supported_word (xs : List (Fin (a+4))) (n : ℕ) (hn : xs.length ≤ n) :
    Supported (putWord (fun _ => blank) 0 xs) n := by
  intro z hz
  exact putWord_outside _ _ _ _ (by omega)

def parked (f role : ℤ → Fin (a+4)) (p : ℤ) (n : ℕ) : ℤ → Fin (a+4) :=
  fun z => if p ≤ z ∧ z < p+n then role (z-p) else f z

private theorem push_result (role f : ℤ → Fin (a+4)) (p : ℤ) (n : ℕ) (hr : Supported role n) :
    StackPush.result (StackPop.bank role f 0 p) n = StackPop.bank (fun _ => blank) (parked f role p n) n (p+n) := by
  apply congrArg₂ Tapes.mk
  · funext i
    change (StackPush.result (StackPop.bank role f 0 p) n).head i = _
    rw [StackPush.heads]; fin_cases i <;> simp [StackPop.bank]
  · funext i z; fin_cases i
    · change (StackPush.result (StackPop.bank role f 0 p) n).tape 0 z = blank
      rw [StackPush.source]
      simp only [StackPop.bank,ite_true,zero_add]
      split_ifs with hz
      · rfl
      · exact hr z (by omega)
    · change (StackPush.result (StackPop.bank role f 0 p) n).tape 1 z = parked f role p n z
      rw [StackPush.destination]
      simp [StackPop.bank,parked]

private theorem recover_result (role f : ℤ → Fin (a+4)) (p : ℤ) (n : ℕ) (hr : Supported role n)
    (hf : ∀ z, p ≤ z → z < p+n → f z = blank) :
    swapped (StackPop.transfer (swapped (StackPop.bank (fun _ => blank) (parked f role p n) (n-1) (p+n-1))) n) =
      StackPop.bank role f (-1) (p-1) := by
  have ht := StackPop.transfer_region (parked f role p n) (fun _ => blank) p 0 n
  simp only [zero_add,sub_zero] at ht
  change swapped (StackPop.transfer (StackPop.bank (parked f role p n) (fun _ => blank) (p+n-1) (n-1)) n) = _
  rw [ht]
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> rfl
  · funext i z; fin_cases i
    · change (if (0 : ℤ) ≤ z ∧ z < n then parked f role p n (p+z) else blank) = role z
      by_cases hz : (0 : ℤ) ≤ z ∧ z < n
      · simp [parked,hz,show p ≤ p+z ∧ p+z < p+n by omega]
      · simp [hz,hr z (by omega)]
    · change (if p ≤ z ∧ z < p+n then blank else parked f role p n z) = f z
      by_cases hz : p ≤ z ∧ z < p+n
      · simp [hz,hf z hz.1 hz.2]
      · simp [parked,hz]

def roleLeft : Fin 2 → Move := ![Move.left,Move.stay]
def roleRight : Fin 2 → Move := ![Move.right,Move.stay]
def bothLeft : Fin 2 → Move := fun _ => Move.left
def bothRight : Fin 2 → Move := fun _ => Move.right

def pushProgram (a : ℕ) :=
  seq (seq (seq (initializeProgram a) StackPush.program) (moveProgram roleLeft)) (cleanupProgram a)

def popProgram (a : ℕ) :=
  seq (seq (seq (seq (seq (initializeProgram a) (moveProgram roleRight)) (stepProgram bothLeft))
    (RoleArrayStackMoves.popProgram a)) (stepProgram bothRight)) (cleanupProgram a)

/-- Every payload symbol, including blanks and delimiters, is copied by the
independent count. A second real counted traversal resets the vacated role head. -/
theorem push_hoare (role f : ℤ → Fin (a+4)) (p : ℤ) (n : ℕ) (bs : List Bool)
    (hc : Counter.value bs = n) (hr : Supported role n) :
    HoareTime (pushProgram a) (fun v => v = idle (StackPop.bank role f 0 p) bs)
      (fun v => v = idle (StackPop.bank (fun _ => blank) (parked f role p n) 0 (p+n)) bs)
      (14*n+14*bs.length+45) := by
  have hp := StackPush.push_hoare (StackPop.bank role f 0 p) bs n hc
  rw [push_result role f p n hr] at hp
  have hm := move_hoare (StackPop.bank (fun _ => blank) (parked f role p n) n (p+n)) roleLeft bs n hc
  have he : shifted (StackPop.bank (fun _ => blank) (parked f role p n) n (p+n)) roleLeft n =
      StackPop.bank (fun _ => blank) (parked f role p n) 0 (p+n) := by
    apply congrArg₂ Tapes.mk
    · funext i; fin_cases i <;> simp [StackPop.bank,roleLeft,Move.offset]
    · rfl
  rw [he] at hm
  exact ((((initialize_hoare _ bs).seq hp).seq hm).seq (cleanup_hoare _ bs)).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

/-- Reconstruct the original role/head and exact older stack/head, erasing the
popped frame. Both positioning passes, clock operations and joins are charged. -/
theorem pop_hoare (role f : ℤ → Fin (a+4)) (p : ℤ) (n : ℕ) (bs : List Bool)
    (hc : Counter.value bs = n) (hr : Supported role n)
    (hf : ∀ z, p ≤ z → z < p+n → f z = blank) :
    HoareTime (popProgram a)
      (fun v => v = idle (StackPop.bank (fun _ => blank) (parked f role p n) 0 (p+n)) bs)
      (fun v => v = idle (StackPop.bank role f 0 p) bs) (14*n+14*bs.length+49) := by
  have hm := move_hoare (StackPop.bank (fun _ => blank) (parked f role p n) 0 (p+n)) roleRight bs n hc
  have he : shifted (StackPop.bank (fun _ => blank) (parked f role p n) 0 (p+n)) roleRight n =
      StackPop.bank (fun _ => blank) (parked f role p n) n (p+n) := by
    apply congrArg₂ Tapes.mk
    · funext i; fin_cases i <;> simp [StackPop.bank,roleRight,Move.offset]
    · rfl
  rw [he] at hm
  have hb := step_hoare (StackPop.bank (fun _ => blank) (parked f role p n) n (p+n)) bothLeft bs
  have hb' : shifted (StackPop.bank (fun _ => blank) (parked f role p n) n (p+n)) bothLeft 1 =
      StackPop.bank (fun _ => blank) (parked f role p n) (n-1) (p+n-1) := by
    apply congrArg₂ Tapes.mk
    · funext i; fin_cases i <;> simp [StackPop.bank,bothLeft,Move.offset,sub_eq_add_neg]
    · rfl
  rw [hb'] at hb
  have hp := RoleArrayStackMoves.pop_hoare (StackPop.bank (fun _ => blank) (parked f role p n) (n-1) (p+n-1)) bs n hc
  rw [recover_result role f p n hr hf] at hp
  have he := step_hoare (StackPop.bank role f (-1) (p-1)) bothRight bs
  have he' : shifted (StackPop.bank role f (-1) (p-1)) bothRight 1 = StackPop.bank role f 0 p := by
    apply congrArg₂ Tapes.mk
    · funext i; fin_cases i <;> simp [StackPop.bank,bothRight,Move.offset]
    · rfl
  rw [he'] at he
  exact ((((((initialize_hoare _ bs).seq hm).seq hb).seq hp).seq he).seq (cleanup_hoare _ bs)).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

theorem parked_outside (role f : ℤ → Fin (a+4)) (p z : ℤ) (n : ℕ)
    (hz : z < p ∨ p+n ≤ z) : parked f role p n z = f z := by
  simp [parked,show ¬ (p ≤ z ∧ z < p+n) by omega]

end
end IntegerMultBounds.Machine.RoleArrayStack
