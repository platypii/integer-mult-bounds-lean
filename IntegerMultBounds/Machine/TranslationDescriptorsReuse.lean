import IntegerMultBounds.Machine.TranslationDescriptors

/-! Physical erasure of translation metadata and synthesis from a reusable
marked workspace. Every scan and join is charged, and Q, a, B stay immutable. -/

namespace IntegerMultBounds.Machine.TranslationDescriptorsReuse

open CountedCopyReuse (empty binary)
open TranslationDescriptors (bank descriptors)

private def packed (ds : Fin 4 → List Bool) (bs qs as : List Bool) : Tapes 10 0 :=
  bank (fun i => ds (Fin.castAdd 1 i)) bs qs as (binary (ds 3)) 1

private def slot (j : Fin 4) : Fin 10 := ![1,2,3,9] j

private def placement (j : Fin 4) : Fin (2+8) ≃ Fin 10 :=
  (Equiv.swap 1 5).trans (Equiv.swap 0 (slot j))

/-- Erase one generated word, using the preserved B descriptor as a frame. -/
def clearProgram (j : Fin 4) : Program 10 4 0 :=
  Placement.placed CountedLoopReuse.cleanControls (placement j)

private theorem active_packed (ds : Fin 4 → List Bool) (bs qs as : List Bool) (j : Fin 4) :
    Placement.active (placement j) (packed ds bs qs as) =
      CountedLoopReuse.controls (binary (ds j)) (binary bs) 1 1 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases j <;> fin_cases i <;> rfl

private theorem replace_packed (ds : Fin 4 → List Bool) (bs qs as : List Bool) (j : Fin 4) :
    Placement.replace (placement j) (packed ds bs qs as)
      (CountedLoopReuse.controls empty (binary bs) 1 1) =
      packed (Function.update ds j []) bs qs as := by
  have he : Placement.extra (placement j) (packed ds bs qs as) =
      Placement.extra (placement j) (packed (Function.update ds j []) bs qs as) := by
    unfold Placement.extra placement packed bank TranslationProduct.bank ScalingDescriptors.innerBank
      ScalingDescriptors.counters CountedLoopReuse.bank CountedLoopReuse.controls Tapes.append
    congr 1; funext i; fin_cases j <;> fin_cases i <;> rfl
  have ha := active_packed (Function.update ds j []) bs qs as j
  simp only [Function.update_self] at ha
  change Placement.active (placement j) (packed (Function.update ds j []) bs qs as) =
    CountedLoopReuse.controls empty (binary bs) 1 1 at ha
  rw [Placement.replace,he]
  simpa only [ha] using Placement.view (placement j) (packed (Function.update ds j []) bs qs as)

private theorem clear_hoare (ds : Fin 4 → List Bool) (bs qs as : List Bool) (j : Fin 4) :
    HoareTime (clearProgram j) (fun v => v = packed ds bs qs as)
      (fun v => v = packed (Function.update ds j []) bs qs as) (2*(ds j).length+4) := by
  have h := Placement.hoare_at (CountedLoopReuse.clean_controls_hoare (ds j) bs)
    (placement j) (packed ds bs qs as) (active_packed ds bs qs as j)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  exact replace_packed _ _ _ _ _

/-- Erase the three product descriptors and the padded subtraction result. -/
def clearAllProgram : Program 10 16 0 :=
  seq (seq (seq (clearProgram 0) (clearProgram 1)) (clearProgram 2)) (clearProgram 3)

private theorem clear_all_hoare (ds : Fin 4 → List Bool) (bs qs as : List Bool) :
    HoareTime clearAllProgram (fun v => v = packed ds bs qs as)
      (fun v => v = packed (fun _ => []) bs qs as)
      (2*((ds 0).length+(ds 1).length+(ds 2).length+(ds 3).length)+19) := by
  let d₁ := Function.update ds 0 []
  let d₂ := Function.update d₁ 1 []
  let d₃ := Function.update d₂ 2 []
  have h₀ := clear_hoare ds bs qs as 0
  have h₁ := clear_hoare d₁ bs qs as 1
  have h₂ := clear_hoare d₂ bs qs as 2
  have h₃ := clear_hoare d₃ bs qs as 3
  have hf : Function.update d₃ 3 [] = fun _ => [] := by
    funext j
    fin_cases j <;> simp [d₃,d₂,d₁]
  rw [hf] at h₃
  apply (((h₀.seq h₁).seq h₂).seq h₃).consequence (fun _ h => h) (fun _ h => h) _
  simp [d₃,d₂,d₁]
  omega

private def moved (v : Tapes 10 0) : Tapes 10 0 :=
  ⟨Function.update v.head 9 0,v.tape⟩

private def unmarked (v : Tapes 10 0) : Tapes 10 0 :=
  ⟨Function.update v.head 9 0,Function.update v.tape 9 (fun _ => blank)⟩

/-- Move the scratch head to its sentinel and physically erase that sentinel. -/
def unmarkProgram : Program 10 3 0 where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols =>
    if state = 0 then some (1,fun i => (symbols i,if i = 9 then Move.left else Move.stay))
    else if state = 1 then some (2,fun i => (if i = 9 then blank else symbols i,Move.stay))
    else none

private theorem unmark_hoare (v : Tapes 10 0) (hh : v.head 9 = 1) (ht : v.tape 9 = empty) :
    HoareTime unmarkProgram (fun w => w = v) (fun w => w = unmarked v) 2 := by
  intro w hw
  subst w
  refine ⟨2,⟨2,(unmarked v).head,(unmarked v).tape⟩,le_rfl,?_,?_,rfl⟩
  · have hs : step unmarkProgram (v.start unmarkProgram) =
        some ⟨1,(moved v).head,(moved v).tape⟩ := by
      simp only [step,unmarkProgram,Tapes.start,ite_true]
      congr 1
      congr 1
      · funext i
        by_cases hi : i = 9 <;> simp [hi,moved,Move.offset,hh]
      · funext i z
        by_cases hz : z = v.head i <;> simp [moved,hz]
    rw [run_add unmarkProgram 1 1,run_one,hs]
    simp only [Option.bind_some,run_one,step,unmarkProgram,show (1 : Fin 3) ≠ 0 by decide,ite_false,ite_true]
    congr 1
    congr 1
    · funext i
      simp [moved,unmarked,Move.offset]
    · funext i z
      by_cases hi : i = 9
      · subst i
        by_cases hz : z = 0 <;> simp [moved,unmarked,ht,empty,hz]
      · by_cases hz : z = v.head i <;> simp [hi,moved,unmarked,hz]
  · simp [step,unmarkProgram]

private theorem unmarked_packed (bs qs as : List Bool) :
    unmarked (packed (fun _ => []) bs qs as) = bank (fun _ => []) bs qs as (fun _ => blank) 0 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

/-- Complete cleanup restores the exact marked workspace expected by synthesis. -/
def cleanupProgram : Program 10 19 0 := seq clearAllProgram unmarkProgram

/-- Arbitrary binary metadata is physically erased, including its scratch
sentinel; canonical metadata is not required by the cleanup routine. -/
theorem cleanup_hoare (ds : Fin 3 → List Bool) (diff bs qs as : List Bool) :
    HoareTime cleanupProgram (fun v => v = bank ds bs qs as (binary diff) 1)
      (fun v => v = bank (fun _ => []) bs qs as (fun _ => blank) 0)
      (2*((ds 0).length+(ds 1).length+(ds 2).length+diff.length)+22) := by
  let all : Fin 4 → List Bool := ![ds 0,ds 1,ds 2,diff]
  have hp : packed all bs qs as = bank ds bs qs as (binary diff) 1 := by
    have h : (fun i : Fin 3 => all (Fin.castAdd 1 i)) = ds := by
      funext i
      fin_cases i <;> rfl
    change bank _ _ _ _ _ _ = _
    rw [h]
    rfl
  have hc := clear_all_hoare all bs qs as
  rw [hp] at hc
  have hu := unmark_hoare (packed (fun _ => []) bs qs as) rfl rfl
  rw [unmarked_packed] at hu
  apply (hc.seq hu).consequence (fun _ h => h) (fun _ h => h) _
  dsimp [all]
  omega

/-- Repeated synthesis skips the one-time work-counter marker installation. -/
def program : Program 10 118 0 := seq TranslationDescriptors.subtractionProgram TranslationDescriptors.productsProgram

theorem descriptors_hoare (Q a B : ℕ) (ha : a ≤ Q) (hB : 0 < B) (bs qs as : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (ha' : Counter.value as = a)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (ca : GrowingCounterData.Canonical as) :
    HoareTime program (fun v => v = bank (fun _ => []) bs qs as (fun _ => blank) 0)
      (fun v => v = bank (descriptors Q a B) bs qs as (binary (BinarySubReuse.difference qs as)) 1)
      (163*(Q*B)+90) := by
  have wb := GrowingCounterData.canonical_width bs cb
  have wq := GrowingCounterData.canonical_width qs cq
  have wa := GrowingCounterData.canonical_width as ca
  rw [hb] at wb
  rw [hq] at wq
  rw [ha'] at wa
  have lb := Nat.log2_le_self B
  have lq := Nat.log2_le_self Q
  have la := Nat.log2_le_self a
  have wd : (BinarySubReuse.difference qs as).length ≤ Q+1 := by
    rw [BinarySubReuse.difference_length]
    exact max_le (by omega) (by omega)
  have hd : Counter.value (BinarySubReuse.difference qs as) = Q-a := by
    rw [BinarySubReuse.difference_value qs as (by simpa only [hq,ha'] using ha),hq,ha']
  have hs := TranslationDescriptors.subtraction_hoare (fun _ => []) bs qs as
  have hp := TranslationDescriptors.products_hoare Q a B ha hB bs qs as (BinarySubReuse.difference qs as)
    hb hq ha' hd (by omega) (by omega) (by omega) wd
  apply (hs.seq hp).consequence (fun _ h => h) (fun _ h => h) _
  have hw : BinarySubReuse.width qs as ≤ Q+1 := max_le (by omega) (by omega)
  have hQB : Q ≤ Q*B := by nlinarith
  omega

/-- Cleanup is linear in the physical payload size, including padded difference
bits. This wrapper is intended after an execution preserving descriptor tapes. -/
theorem cleanup_hoare_linear (Q a B : ℕ) (ha : a ≤ Q) (hB : 0 < B) (bs qs as : List Bool)
    (hq : Counter.value qs = Q) (ha' : Counter.value as = a)
    (cq : GrowingCounterData.Canonical qs) (ca : GrowingCounterData.Canonical as) :
    HoareTime cleanupProgram
      (fun v => v = bank (descriptors Q a B) bs qs as (binary (BinarySubReuse.difference qs as)) 1)
      (fun v => v = bank (fun _ => []) bs qs as (fun _ => blank) 0) (8*(Q*B)+30) := by
  apply (cleanup_hoare (descriptors Q a B) (BinarySubReuse.difference qs as) bs qs as).consequence
    (fun _ h => h) (fun _ h => h) _
  have hw (j : Fin 3) : (descriptors Q a B j).length ≤ Q*B+1 := by
    have h := GrowingCounterData.canonical_width _ (TranslationDescriptors.descriptors_canonical Q a B j)
    have hval : Counter.value (descriptors Q a B j) ≤ Q*B := by
      fin_cases j
      · change Counter.value (descriptors Q a B 0) ≤ Q*B
        rw [(TranslationDescriptors.descriptor_values Q a B).1]
        exact Nat.mul_le_mul_right B (Nat.sub_le Q a)
      · change Counter.value (descriptors Q a B 1) ≤ Q*B
        rw [(TranslationDescriptors.descriptor_values Q a B).2.1]
        exact Nat.mul_le_mul_right B ha
      · exact le_of_eq (TranslationDescriptors.descriptor_values Q a B).2.2
    have := Nat.log2_le_self (Counter.value (descriptors Q a B j))
    omega
  have wq := GrowingCounterData.canonical_width qs cq
  have wa := GrowingCounterData.canonical_width as ca
  rw [hq] at wq
  rw [ha'] at wa
  have lq := Nat.log2_le_self Q
  have la := Nat.log2_le_self a
  have hQB : Q ≤ Q*B := by nlinarith
  have wd : (BinarySubReuse.difference qs as).length ≤ Q*B+1 := by
    rw [BinarySubReuse.difference_length]
    exact max_le (by omega) (by omega)
  have h₀ := hw 0
  have h₁ := hw 1
  have h₂ := hw 2
  omega

end IntegerMultBounds.Machine.TranslationDescriptorsReuse
