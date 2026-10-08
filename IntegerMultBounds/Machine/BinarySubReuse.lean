import IntegerMultBounds.Machine.BinarySub
import IntegerMultBounds.Machine.CountedCopyReuse
import IntegerMultBounds.Machine.Placement
import IntegerMultBounds.Machine.GrowingCounterData

/-! Immutable arbitrary-width binary subtraction. The literal ripple machine
reads missing high bits as zero until both source tapes end. It creates an
output sentinel on blank work, preserves both operands, and physically restores
all three heads. No padded operand copies or size-dependent control are needed. -/

namespace IntegerMultBounds.Machine.BinarySubReuse

open CountedCopyReuse (empty binary)

/-- Right zero extension is performed by scanned-symbol decoding, not padding writes. -/
def columns : List Bool → List Bool → List (Bool × Bool)
  | [],[] => []
  | [],y::ys => (false,y)::columns [] ys
  | x::xs,[] => (x,false)::columns xs []
  | x::xs,y::ys => (x,y)::columns xs ys

def width (xs ys : List Bool) : ℕ := max xs.length ys.length

def digits (borrow : Bool) (xs ys : List Bool) : List Bool := BinarySub.digits borrow (columns xs ys)
def overflow (borrow : Bool) (xs ys : List Bool) : Bool := BinarySub.overflow borrow (columns xs ys)
def difference (xs ys : List Bool) : List Bool := digits false xs ys

theorem columns_length (xs ys : List Bool) : (columns xs ys).length = width xs ys := by
  fun_induction columns xs ys <;> simp_all [width]

theorem digits_length (borrow : Bool) (xs ys : List Bool) : (digits borrow xs ys).length = width xs ys := by
  rw [digits,BinarySub.digits_length,columns_length]

theorem digits_value (borrow : Bool) (xs ys : List Bool) :
    Counter.value xs+2^width xs ys*BinarySub.bitValue (overflow borrow xs ys) =
      Counter.value ys+Counter.value (digits borrow xs ys)+BinarySub.bitValue borrow := by
  fun_induction columns xs ys generalizing borrow
  · simp [digits,overflow,columns,width,BinarySub.digits,BinarySub.overflow,Counter.value]
  · rename_i y ys ih
    have hi := ih (BinarySub.borrowBit borrow false y)
    have ha := BinarySub.full_subtractor borrow false y
    simp only [digits,overflow,columns,BinarySub.digits,BinarySub.overflow,Counter.value,
      width,List.length_nil,List.length_cons,Nat.zero_max,pow_succ] at ⊢
    simp only [digits,overflow,width,List.length_nil,Nat.zero_max] at hi
    simp only [BinarySub.bitValue,BinaryAdd.bitValue,Counter.value,Bool.false_eq_true,ite_false] at ha hi ⊢
    nlinarith
  · rename_i x xs ih
    have hi := ih (BinarySub.borrowBit borrow x false)
    have ha := BinarySub.full_subtractor borrow x false
    simp only [digits,overflow,columns,BinarySub.digits,BinarySub.overflow,Counter.value,
      width,List.length_nil,List.length_cons,Nat.max_zero,pow_succ] at ⊢
    simp only [digits,overflow,width,List.length_nil,Nat.max_zero] at hi
    simp only [BinarySub.bitValue,BinaryAdd.bitValue,Counter.value,Bool.false_eq_true,ite_false] at ha hi ⊢
    nlinarith
  · rename_i x xs y ys ih
    have hi := ih (BinarySub.borrowBit borrow x y)
    have ha := BinarySub.full_subtractor borrow x y
    simp only [digits,overflow,columns,BinarySub.digits,BinarySub.overflow,Counter.value,
      width,List.length_cons,max_add_add_right,pow_succ] at ⊢
    simp only [digits,overflow,width] at hi
    simp only [BinarySub.bitValue,BinaryAdd.bitValue] at ha hi ⊢
    nlinarith

/-- The padded output encodes natural subtraction when no unsigned underflow occurs. -/
theorem difference_value (xs ys : List Bool) (hle : Counter.value ys ≤ Counter.value xs) :
    Counter.value (difference xs ys) = Counter.value xs-Counter.value ys := by
  have hv := digits_value false xs ys
  have hx := Counter.value_lt xs
  have hy := Counter.value_lt (digits false xs ys)
  rw [digits_length] at hy
  have hx' : Counter.value xs < 2^width xs ys :=
    hx.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
  cases ho : overflow false xs ys <;>
    simp only [ho,BinarySub.bitValue,BinaryAdd.bitValue,Bool.false_eq_true,ite_false,
      ite_true,Nat.mul_zero,Nat.mul_one,Nat.add_zero] at hv <;> dsimp [difference] <;> omega

/-- A borrow bit is the only finite state. Blank missing operands decode as zero. -/
def subtractProgram : Program 3 2 0 where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols =>
    if symbols 0 = blank ∧ symbols 1 = blank then none else
      let b := decide (state = 1)
      let x := decide (symbols 0 = bitSymbol true)
      let y := decide (symbols 1 = bitSymbol true)
      some (BinarySub.borrowState (BinarySub.borrowBit b x y),fun i =>
        (if i = 2 then bitSymbol (BinarySub.diffBit b x y) else symbols i,Move.right))

abbrev cfg := BinarySub.cfg (a := 0)

private theorem bit_step (b x y : Bool) (f g out : ℤ → Fin 4) (p q r : ℤ)
    (hx : f p = bitSymbol x ∨ x = false ∧ f p = blank)
    (hy : g q = bitSymbol y ∨ y = false ∧ g q = blank)
    (hnon : f p ≠ blank ∨ g q ≠ blank) :
    step subtractProgram (cfg f g out p q r (BinarySub.borrowState b)) =
      some (cfg f g (Function.update out r (bitSymbol (BinarySub.diffBit b x y)))
        (p+1) (q+1) (r+1) (BinarySub.borrowState (BinarySub.borrowBit b x y))) := by
  have ht : subtractProgram.transition (BinarySub.borrowState b)
      (fun i => (cfg f g out p q r (BinarySub.borrowState b)).tape i
        ((cfg f g out p q r (BinarySub.borrowState b)).head i)) =
      some (BinarySub.borrowState (BinarySub.borrowBit b x y),fun i =>
        (if i = 2 then bitSymbol (BinarySub.diffBit b x y)
          else (cfg f g out p q r (BinarySub.borrowState b)).tape i
            ((cfg f g out p q r (BinarySub.borrowState b)).head i),Move.right)) := by
    cases b <;> cases x <;> cases y <;> rcases hx with hx | ⟨hx,hf⟩ <;>
      rcases hy with hy | ⟨hy,hg⟩ <;>
      simp_all [subtractProgram,cfg,BinarySub.cfg,BinarySub.borrowState,bitSymbol,blank]
  unfold step
  simp only [cfg,BinarySub.cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i z; fin_cases i <;> simp [Function.update_apply,eq_comm] <;> intro hz <;> rw [hz]

private theorem bits_nil (f : ℤ → Fin 4) (p : ℤ) : putBits f p [] = f := rfl

private theorem update_tail (f : ℤ → Fin 4) (p : ℤ) (xs : List Bool) (b : Bool)
    (hf : ∀ z, p+(b::xs).length ≤ z → f z = blank) :
    ∀ z, p+1+xs.length ≤ z → Function.update f p (bitSymbol b) z = blank := by
  intro z hz
  rw [Function.update_of_ne (by omega)]
  apply hf
  simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
  omega

/-- Exact width-many transitions, preserving unpadded operands literally. -/
theorem columns_run (xs ys : List Bool) (b : Bool) (f g out : ℤ → Fin 4) (p q r : ℤ)
    (hf : ∀ z, p+xs.length ≤ z → f z = blank)
    (hg : ∀ z, q+ys.length ≤ z → g z = blank) :
    run subtractProgram (width xs ys)
      (cfg (putBits f p xs) (putBits g q ys) out p q r (BinarySub.borrowState b)) =
      some (cfg (putBits f p xs) (putBits g q ys) (putBits out r (digits b xs ys))
        (p+width xs ys) (q+width xs ys) (r+width xs ys) (BinarySub.borrowState (overflow b xs ys))) := by
  fun_induction columns xs ys generalizing b f g out p q r
  · simp [width,run,digits,overflow,columns,BinarySub.digits,BinarySub.overflow,putBits]
  · rename_i y ys ih
    have hp : f p = blank := hf p (by simp)
    have hs := bit_step b false y f (putBits g q (y::ys)) out p q r
      (Or.inr ⟨rfl,hp⟩) (Or.inl (putBits_head _ _ _ _))
      (Or.inr (by rw [putBits_head]; cases y <;> decide))
    have hr := ih (BinarySub.borrowBit b false y) f (Function.update g q (bitSymbol y))
      (Function.update out r (bitSymbol (BinarySub.diffBit b false y))) (p+1) (q+1) (r+1)
      (by intro z hz; apply hf; simp only [List.length_nil,Nat.cast_zero,add_zero] at *; omega)
      (update_tail g q ys y hg)
    simp only [width,List.length_nil,List.length_cons,Nat.zero_max,run,bits_nil] at ⊢
    rw [hs]
    simp only [Option.bind_some]
    simpa only [width,List.length_nil,Nat.zero_max,digits,overflow,columns,BinarySub.digits,
      BinarySub.overflow,← putBits_cons,bits_nil,Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using hr
  · rename_i x xs ih
    have hq : g q = blank := hg q (by simp)
    have hs := bit_step b x false (putBits f p (x::xs)) g out p q r
      (Or.inl (putBits_head _ _ _ _)) (Or.inr ⟨rfl,hq⟩)
      (Or.inl (by rw [putBits_head]; cases x <;> decide))
    have hr := ih (BinarySub.borrowBit b x false) (Function.update f p (bitSymbol x)) g
      (Function.update out r (bitSymbol (BinarySub.diffBit b x false))) (p+1) (q+1) (r+1)
      (update_tail f p xs x hf)
      (by intro z hz; apply hg; simp only [List.length_nil,Nat.cast_zero,add_zero] at *; omega)
    simp only [width,List.length_nil,List.length_cons,Nat.max_zero,run,bits_nil] at ⊢
    rw [hs]
    simp only [Option.bind_some]
    simpa only [width,List.length_nil,Nat.max_zero,digits,overflow,columns,BinarySub.digits,
      BinarySub.overflow,← putBits_cons,bits_nil,Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using hr
  · rename_i x xs y ys ih
    have hs := bit_step b x y (putBits f p (x::xs)) (putBits g q (y::ys)) out p q r
      (Or.inl (putBits_head _ _ _ _)) (Or.inl (putBits_head _ _ _ _))
      (Or.inl (by rw [putBits_head]; cases x <;> decide))
    have hr := ih (BinarySub.borrowBit b x y) (Function.update f p (bitSymbol x))
      (Function.update g q (bitSymbol y)) (Function.update out r (bitSymbol (BinarySub.diffBit b x y)))
      (p+1) (q+1) (r+1) (update_tail f p xs x hf) (update_tail g q ys y hg)
    simp only [width,List.length_cons,max_add_add_right,run] at ⊢
    rw [hs]
    simp only [Option.bind_some]
    simpa only [width,digits,overflow,columns,BinarySub.digits,BinarySub.overflow,← putBits_cons,bits_nil,
      Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using hr

private theorem binary_end (bs : List Bool) (z : ℤ) (hz : 1+bs.length ≤ z) : binary bs z = blank := by
  rw [binary,putBits_outside _ _ _ _ (Or.inr hz)]
  simp [empty,show z ≠ 0 by omega]

private theorem binary_marker (bs : List Bool) : binary bs 0 = separator := by
  rw [binary,putBits_outside _ _ _ _ (Or.inl (by omega))]
  rfl

private theorem binary_ne_marker (bs : List Bool) (z : ℤ) (hz : 0 < z) : binary bs z ≠ separator := by
  by_cases he : z < 1+bs.length
  · exact putBits_ne_separator empty 1 z bs (by omega) he
  · rw [binary_end bs z (by omega)]
    decide

/-- The public three-tape layout is immutable xs, immutable ys, and output. -/
def bank (xs ys : List Bool) (out : ℤ → Fin 4) (p q r : ℤ) : Tapes 3 0 :=
  (cfg (binary xs) (binary ys) out p q r 0).tapes

theorem subtract_exact (xs ys : List Bool) :
    Placement.ExactRun subtractProgram (width xs ys) (bank xs ys empty 1 1 1)
      (bank xs ys (binary (difference xs ys)) (1+width xs ys) (1+width xs ys) (1+width xs ys)) := by
  have h := columns_run xs ys false empty empty empty 1 1 1
    (by intro z hz; simp [empty,show z ≠ 0 by omega])
    (by intro z hz; simp [empty,show z ≠ 0 by omega])
  refine ⟨cfg (binary xs) (binary ys) (binary (difference xs ys))
    (1+width xs ys) (1+width xs ys) (1+width xs ys) (BinarySub.borrowState (overflow false xs ys)),h,?_,rfl⟩
  have hx := binary_end xs (1+width xs ys) (by have := Nat.le_max_left xs.length ys.length; dsimp [width]; omega)
  have hy := binary_end ys (1+width xs ys) (by have := Nat.le_max_right xs.length ys.length; dsimp [width]; omega)
  simp [step,subtractProgram,cfg,BinarySub.cfg,hx,hy]

/-- Only the output starts unmarked, on its future sentinel cell. -/
def initialProgram : Program 3 2 0 where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols => if state = 0 then
    some (1,fun i => if i = 2 then (separator,Move.right) else (symbols i,Move.stay)) else none

private theorem initial_exact (xs ys : List Bool) :
    Placement.ExactRun initialProgram 1 (bank xs ys (fun _ => blank) 1 1 0) (bank xs ys empty 1 1 1) := by
  refine ⟨⟨1,(bank xs ys empty 1 1 1).head,(bank xs ys empty 1 1 1).tape⟩,?_,?_,rfl⟩
  · rw [run_one]
    simp only [step,initialProgram,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> simp [bank,cfg,BinarySub.cfg,Config.tapes,Move.offset]
    · funext i z
      fin_cases i <;> simp [bank,cfg,BinarySub.cfg,Config.tapes,empty]
      all_goals intro h; subst z; rfl
  · simp [step,initialProgram]

private def one (f : ℤ → Fin 4) (p : ℤ) : Tapes 1 0 := ⟨fun _ => p,fun _ => f⟩

private theorem right_exact (f : ℤ → Fin 4) (p : ℤ) :
    Placement.ExactRun CountedCopyReuse.rightProgram 1 (one f p) (one f (p+1)) := by
  refine ⟨⟨1,fun _ => p+1,fun _ => f⟩,?_,?_,rfl⟩
  · simp only [run_one,step,CountedCopyReuse.rightProgram,one,Tapes.start,ite_true,Move.offset]
    congr 1
    congr 1
    funext i z
    by_cases hz : z = p <;> simp [hz]
  · simp [step,CountedCopyReuse.rightProgram]

private theorem reset_exact (bs : List Bool) (n : ℕ) :
    Placement.ExactRun CountedCopyReuse.resetProgram (n+2) (one (binary bs) n) (one (binary bs) 1) := by
  obtain ⟨hr,hh⟩ := Rewind.rewind_exact separator (binary bs) n n
    (by intro j hj; exact binary_ne_marker bs _ (by omega))
    (by simpa using binary_marker bs)
  have h₁ : Placement.ExactRun (Rewind.program separator) n (one (binary bs) n) (one (binary bs) 0) := by
    refine ⟨Rewind.cfg (binary bs) 0,?_,?_,rfl⟩
    · simpa only [sub_self,one,Tapes.start,Rewind.cfg,Rewind.program] using hr
    · simpa only [sub_self] using hh
  simpa only [zero_add,CountedCopyReuse.resetProgram,Nat.add_assoc] using
    Placement.exact_seq h₁ (right_exact (binary bs) 0)

def resetProgram (i : Fin 3) : Program 3 3 0 :=
  Placement.placed (u := 2) CountedCopyReuse.resetProgram (Equiv.swap 0 i)

private def restored (v : Tapes 3 0) (i : Fin 3) : Tapes 3 0 :=
  ⟨Function.update v.head i 1,v.tape⟩

private theorem reset_at (v : Tapes 3 0) (i : Fin 3) (bs : List Bool) (n : ℕ)
    (hhead : v.head i = n) (htape : v.tape i = binary bs) :
    Placement.ExactRun (resetProgram i) (n+2) v (restored v i) := by
  have ha : Placement.active (s := 1) (u := 2) (Equiv.swap 0 i) v = one (binary bs) n := by
    unfold Placement.active one
    congr 1 <;> funext j <;> fin_cases j <;> simp [hhead,htape]
  have hx : Placement.ExactRun CountedCopyReuse.resetProgram (n+2)
      (Placement.active (s := 1) (u := 2) (Equiv.swap 0 i) v) (one (binary bs) 1) := by
    rw [ha]
    exact reset_exact bs n
  have h := Placement.placed_exact (s := 1) (u := 2) CountedCopyReuse.resetProgram
    (Equiv.swap 0 i) v (one (binary bs) 1) hx
  have he : Placement.replace (s := 1) (u := 2) (Equiv.swap 0 i) v (one (binary bs) 1) = restored v i := by
    unfold Placement.replace Placement.combine Placement.extra Tapes.append Tapes.reindex one restored
    congr 1
    · funext j; fin_cases i <;> fin_cases j <;> simp [Equiv.swap_apply_def,Fin.addCases]
    · funext j; fin_cases i <;> fin_cases j <;> simp [Equiv.swap_apply_def,Fin.addCases]
      all_goals exact htape.symm
  simpa only [resetProgram,he] using h

private theorem restored_zero (xs ys : List Bool) (out : ℤ → Fin 4) (p q r : ℤ) :
    restored (bank xs ys out p q r) 0 = bank xs ys out 1 q r := by
  unfold restored bank cfg BinarySub.cfg Config.tapes
  congr 1
  funext i; fin_cases i <;> simp

private theorem restored_one (xs ys : List Bool) (out : ℤ → Fin 4) (p q r : ℤ) :
    restored (bank xs ys out p q r) 1 = bank xs ys out p 1 r := by
  unfold restored bank cfg BinarySub.cfg Config.tapes
  congr 1
  funext i; fin_cases i <;> simp

private theorem restored_two (xs ys : List Bool) (out : ℤ → Fin 4) (p q r : ℤ) :
    restored (bank xs ys out p q r) 2 = bank xs ys out p q 1 := by
  unfold restored bank cfg BinarySub.cfg Config.tapes
  congr 1
  funext i; fin_cases i <;> simp

/-- Output-marker creation, variable-width subtraction, and three real rewinds. -/
def program : Program 3 13 0 :=
  seq (seq (seq (seq initialProgram subtractProgram) (resetProgram 0)) (resetProgram 1)) (resetProgram 2)

/-- All input cells and all final heads are specified; zero operands and a
zero difference are supported without a canonical-output assumption. -/
theorem sub_exact (xs ys : List Bool) :
    Placement.ExactRun program (4*width xs ys+14)
      (bank xs ys (fun _ => blank) 1 1 0) (bank xs ys (binary (difference xs ys)) 1 1 1) := by
  let w := width xs ys
  let diff := difference xs ys
  have hn : ((w+1 : ℕ) : ℤ) = 1+w := by omega
  have h₀ := reset_at (bank xs ys (binary diff) (1+w) (1+w) (1+w)) 0 xs (w+1) (by rw [hn]; rfl) rfl
  rw [restored_zero] at h₀
  have h₁ := reset_at (bank xs ys (binary diff) 1 (1+w) (1+w)) 1 ys (w+1) (by rw [hn]; rfl) rfl
  rw [restored_one] at h₁
  have h₂ := reset_at (bank xs ys (binary diff) 1 1 (1+w)) 2 diff (w+1) (by rw [hn]; rfl) rfl
  rw [restored_two] at h₂
  have h := Placement.exact_seq (Placement.exact_seq (Placement.exact_seq
    (Placement.exact_seq (initial_exact xs ys) (subtract_exact xs ys)) h₀) h₁) h₂
  simpa only [program,show 1+1+width xs ys+1+(w+1+2)+1+(w+1+2)+1+(w+1+2) =
    4*width xs ys+14 by dsimp [w]; omega] using h

/-- Reusable immutable-input subtraction with exact descriptor-width cost. -/
theorem sub_hoare (xs ys : List Bool) :
    HoareTime program
      (fun v => v = bank xs ys (fun _ => blank) 1 1 0)
      (fun v => v = bank xs ys (binary (difference xs ys)) 1 1 1)
      (4*width xs ys+14) := by
  rintro v rfl
  obtain ⟨last,hr,hh,hf⟩ := sub_exact xs ys
  exact ⟨_,last,le_rfl,hr,hh,hf⟩

/-- The output is width-bounded and represents exact natural subtraction. -/
theorem sub_hoare_value (xs ys : List Bool) (hle : Counter.value ys ≤ Counter.value xs) :
    HoareTime program
      (fun v => v = bank xs ys (fun _ => blank) 1 1 0)
      (fun v => ∃ diff : List Bool, Counter.value diff = Counter.value xs-Counter.value ys ∧
        diff.length = max xs.length ys.length ∧ v = bank xs ys (binary diff) 1 1 1)
      (4*max xs.length ys.length+14) := by
  apply (sub_hoare xs ys).consequence (fun _ hv => hv) _ le_rfl
  intro v hv
  exact ⟨difference xs ys,difference_value xs ys hle,digits_length false xs ys,hv⟩

theorem difference_length (xs ys : List Bool) : (difference xs ys).length = max xs.length ys.length :=
  digits_length false xs ys

/-- Canonical immutable inputs bound all subtraction work linearly in the
minuend value; the result may retain harmless high zero bits. -/
theorem sub_hoare_linear (xs ys : List Bool) (hle : Counter.value ys ≤ Counter.value xs)
    (cx : GrowingCounterData.Canonical xs) (cy : GrowingCounterData.Canonical ys) :
    HoareTime program
      (fun v => v = bank xs ys (fun _ => blank) 1 1 0)
      (fun v => v = bank xs ys (binary (difference xs ys)) 1 1 1)
      (4*Counter.value xs+18) := by
  apply (sub_hoare xs ys).consequence (fun _ hv => hv) (fun _ hv => hv)
  have hx := GrowingCounterData.canonical_width xs cx
  have hy := GrowingCounterData.canonical_width ys cy
  have lx := Nat.log2_le_self (Counter.value xs)
  have ly := Nat.log2_le_self (Counter.value ys)
  dsimp [width]
  omega

end IntegerMultBounds.Machine.BinarySubReuse
