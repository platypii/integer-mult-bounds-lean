import IntegerMultBounds.Machine.RadixDigitMoveRows
import IntegerMultBounds.Machine.CyclicRowRewind
import IntegerMultBounds.Machine.Shared50RecursiveBank

/-! Actual split/rewind/merge/rewind redistribution on one fixed role bank.
This core exposes marked count clocks; initialization and physical role cleanup
belong to its initialized execution wrapper. -/
namespace IntegerMultBounds.Machine.RadixDigitMoveCore
variable {Q a n m : ℕ}
noncomputable section
open CountedLoopReuseAlphabet (binary empty)

abbrev count (Q : ℕ) := (1+Q)+6

def controls (bs gs cs hs : List Bool) : Tapes 6 a :=
  ⟨fun _ => 1,![empty,binary bs,empty,binary gs,binary cs,binary hs]⟩

def bank (source : ℤ → Fin (a+4)) (roles : Fin Q → ℤ → Fin (a+4))
    (p : ℤ) (origins : Fin Q → ℤ) (bs gs cs hs : List Bool) : Tapes (count Q) a :=
  (CyclicRowCopy.payload source roles p origins).append (controls bs gs cs hs)

def extra (cs hs : List Bool) : Tapes 2 a := ⟨fun _ => 1,![binary cs,binary hs]⟩

private theorem cyclic_bank (source : ℤ → Fin (a+4)) (roles : Fin Q → ℤ → Fin (a+4))
    (p : ℤ) (origins : Fin Q → ℤ) (bs gs cs hs : List Bool) :
    (CyclicRowSplit.bank (CyclicRowCopy.bank source roles p origins bs) gs).append (extra cs hs) =
      bank source roles p origins bs gs cs hs := by
  unfold CyclicRowSplit.bank CyclicRowCopy.bank CountedLoopReuseAlphabet.bank bank
  unfold Tapes.append
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    change Fin.append (Fin.append (Fin.append _ _) _) _ i = _
    rw [Fin.append_assoc,Fin.append_assoc]
    change Fin ((1+Q)+6) at i
    refine Fin.addCases (m := 1+Q) (n := 6) ?_ ?_ i
    · intro j; simp [Fin.append]
    · intro j; simp only [Function.comp_apply,Fin.cast_eq_self,Fin.append,Fin.addCases_right]
      fin_cases j <;> rfl

def swapControls : Equiv.Perm (Fin 6) where
  toFun := ![0,4,2,5,1,3]
  invFun := ![0,4,2,5,1,3]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def swap : Equiv.Perm (Fin (count Q)) := Shared50RecursiveBank.join (Equiv.refl _) swapControls

private theorem swapped (source : ℤ → Fin (a+4)) (roles : Fin Q → ℤ → Fin (a+4))
    (p : ℤ) (origins : Fin Q → ℤ) (bs gs cs hs : List Bool) :
    (bank source roles p origins cs hs bs gs).reindex swap = bank source roles p origins bs gs cs hs := by
  rw [bank,swap,Shared50RecursiveBank.append_reindex]
  have hh : (controls (a := a) cs hs bs gs).reindex swapControls = controls bs gs cs hs := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [hh]
  rfl

def splitProgram (Q a : ℕ) := extend (CyclicRowSplit.program Q a) 2
def rewindProgram (Q a : ℕ) := extend (CyclicRowRewind.program Q a) 2
def mergeProgram (Q a : ℕ) := reindex (extend (CyclicRowMerge.program Q a) 2) (swap (Q := Q))
def rewindOther (Q a : ℕ) := reindex (rewindProgram Q a) (swap (Q := Q))
def program (Q a : ℕ) := seq (seq (seq (splitProgram Q a) (rewindProgram Q a)) (mergeProgram Q a)) (rewindOther Q a)

private theorem overwrite (f : ℤ → Fin (a+4)) (p : ℤ) (xs ys : List (Fin (a+4)))
    (hlen : xs.length = ys.length) : putWord (putWord f p xs) p ys = putWord f p ys := by
  funext z
  by_cases hi : p ≤ z ∧ z < p+ys.length
  · let i := (z-p).toNat
    have hp : p+(i : ℤ) = z := by dsimp [i]; omega
    have hil : i < ys.length := by dsimp [i]; omega
    rw [← hp,WordSegments.get _ _ _ i hil,WordSegments.get _ _ _ i hil]
  · rw [putWord_outside _ p z ys (by omega),putWord_outside _ p z ys (by omega)]
    exact putWord_outside _ _ _ xs (by omega)

/-- Arbitrary payload symbols and equal physical role words connect the two
streaming stages; source and role heads physically return to their origins. -/
theorem redistribute_hoare (source : ℤ → Fin (a+4))
    (rows : Fin n → Fin Q → List (Fin (a+4))) (rows' : Fin m → Fin Q → List (Fin (a+4)))
    (B C : ℕ) (bs gs cs hs : List Bool)
    (hlen : ∀ i j, (rows i j).length = B) (hlen' : ∀ i j, (rows' i j).length = C)
    (hb : Counter.value bs = B) (hg : Counter.value gs = n)
    (hc : Counter.value cs = C) (hh : Counter.value hs = m)
    (hroles : ∀ j, CyclicRowSplit.roleWord rows j = CyclicRowSplit.roleWord rows' j)
    (hwords : (CyclicRowSplit.sourceWord rows).length = (CyclicRowSplit.sourceWord rows').length) :
    HoareTime (program Q a)
      (fun v => v = bank (putWord source 0 (CyclicRowSplit.sourceWord rows)) (fun _ _ => blank) 0 (fun _ => 0) bs gs cs hs)
      (fun v => v = bank (putWord source 0 (CyclicRowSplit.sourceWord rows'))
        (fun j => putWord (fun _ => blank) 0 (CyclicRowSplit.roleWord rows j)) 0 (fun _ => 0) bs gs cs hs)
      (2*(n*(7*(Q*B)+Q*(7*bs.length+17))+6*n+7*gs.length+16)+
       2*(m*(7*(Q*C)+Q*(7*cs.length+17))+6*m+7*hs.length+16)+3) := by
  let initial := putWord source 0 (CyclicRowSplit.sourceWord rows)
  let streams := fun j => putWord (fun _ => (blank : Fin (a+4))) 0 (CyclicRowSplit.roleWord rows j)
  have hsplit := hoare_extend_eq (CyclicRowSplit.split_hoare source (fun _ _ => blank) 0 (fun _ => 0)
    rows B hlen bs gs hb hg) (extra cs hs)
  simp only [cyclic_bank,zero_add] at hsplit
  have hr1 := hoare_extend_eq (CyclicRowRewind.rewind_hoare initial streams 0 (fun _ => 0) n B bs gs hb hg) (extra cs hs)
  simp only [cyclic_bank,zero_add] at hr1
  have hmerge := hoare_reindex_eq (hoare_extend_eq
    (CyclicRowMerge.merge_hoare initial (fun _ _ => blank) 0 (fun _ => 0) rows' C hlen' cs hs hc hh)
    (extra bs gs)) (swap (Q := Q))
  simp only [cyclic_bank,swapped,zero_add] at hmerge
  have hm : (fun j => putWord (fun _ => (blank : Fin (a+4))) 0 (CyclicRowSplit.roleWord rows' j)) = streams := by
    funext j
    rw [← hroles j]
  rw [hm,show putWord initial 0 (CyclicRowSplit.sourceWord rows') = putWord source 0 (CyclicRowSplit.sourceWord rows') from
    overwrite source 0 _ _ hwords] at hmerge
  have hr2 := hoare_reindex_eq (hoare_extend_eq (CyclicRowRewind.rewind_hoare
    (putWord source 0 (CyclicRowSplit.sourceWord rows')) streams 0 (fun _ => 0) m C cs hs hc hh)
    (extra bs gs)) (swap (Q := Q))
  simp only [cyclic_bank,swapped,zero_add] at hr2
  exact (((hsplit.seq hr1).seq hmerge).seq hr2).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.RadixDigitMoveCore
