import IntegerMultBounds.Machine.DescriptorStackControl

/-! Variable-length binary descriptor frames on a separate stack tape. A frame
stores a sentinel followed by reversed bits. Its length is discovered by actual
scans; finite control and tape count are independent of descriptor length/depth. -/
namespace IntegerMultBounds.Machine.BinaryDescriptorStack
open DescriptorStackControl
variable {a : ℕ}

def empty (z : ℤ) : Fin (a+4) := if z = 0 then separator else blank
def descriptor (xs : List Bool) : ℤ → Fin (a+4) := putWord empty 1 (xs.map bitSymbol)
def frame (f : ℤ → Fin (a+4)) (p : ℤ) (xs : List Bool) : ℤ → Fin (a+4) :=
  putWord (Function.update f p separator) (p+1) (xs.reverse.map bitSymbol)

private theorem bits_ne (xs : List Bool) : ∀ x ∈ xs.map (bitSymbol (a := a)), x ≠ separator ∧ x ≠ blank := by
  intro x hx
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
  cases b <;> simp [bitSymbol,separator,blank,Fin.ext_iff]

private theorem descriptor_inside (xs : List Bool) (z : ℤ) (hz : 1 ≤ z ∧ z < 1+xs.length) :
    descriptor (a := a) xs z ≠ separator ∧ descriptor (a := a) xs z ≠ blank :=
  bits_ne xs _ (ReturnOrigin.putWord_mem empty 1 (xs.map bitSymbol) z (by simpa using hz))

private theorem descriptor_origin (xs : List Bool) : descriptor (a := a) xs 0 = separator := by
  rw [descriptor,putWord_outside _ _ _ _ (Or.inl (by omega))]
  rfl

private theorem descriptor_end (xs : List Bool) : descriptor (a := a) xs (1+xs.length) = blank := by
  rw [descriptor,putWord_outside _ _ _ _ (Or.inr (by simp))]
  simp [empty,show (1 : ℤ)+xs.length ≠ 0 by omega]

def moveAction (m n : Move) (sy : Fin 2 → Fin (a+4)) (i : Fin 2) := (sy i,if i = 0 then m else n)
def move (m n : Move) : Program 2 2 a := once (by decide) (moveAction m n)

private theorem move_hoare (f g : ℤ → Fin (a+4)) (p q : ℤ) (m n : Move) :
    HoareTime (move m n) (fun v => v = Copy.tapes f g p q)
      (fun v => v = Copy.tapes f g (p+m.offset) (q+n.offset)) 1 := by
  apply (once_hoare (by decide) (moveAction m n) (Copy.tapes f g p q)).consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> rfl
  · funext i z; fin_cases i <;> by_cases hz : z = p <;> by_cases hq : z = q <;>
      simp_all [moveAction,Copy.tapes,Copy.cfg,Config.tapes]

def pushInit : Program 2 2 a := once (by decide)
  (fun sy i => if i = 0 then (sy i,Move.stay) else (separator,Move.right))

private theorem push_init (f g : ℤ → Fin (a+4)) (p q : ℤ) :
    HoareTime pushInit (fun v => v = Copy.tapes f g p q)
      (fun v => v = Copy.tapes f (Function.update g q separator) p (q+1)) 1 := by
  apply (once_hoare (by decide) _ (Copy.tapes f g p q)).consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> simp [Copy.tapes,Copy.cfg,Config.tapes,Move.offset]
  · funext i z; fin_cases i <;> by_cases hz : z = p <;> by_cases hq : z = q <;>
      simp_all [Copy.tapes,Copy.cfg,Config.tapes]

private theorem positioned_zero (f g : ℤ → Fin (a+4)) (p q r : ℤ) :
    positioned (Copy.tapes f g p q) 0 r = Copy.tapes f g r q := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [Copy.tapes,Copy.cfg,Config.tapes]

private theorem positioned_one (f g : ℤ → Fin (a+4)) (p q r : ℤ) :
    positioned (Copy.tapes f g p q) 1 r = Copy.tapes f g p r := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [Copy.tapes,Copy.cfg,Config.tapes]

/-- Fixed eight-state push; every source scan, restoration and join is charged. -/
def push : Program 2 8 a :=
  seq (seq (seq (seq pushInit (seek 0 blank Move.right)) (move Move.left Move.stay))
    (DelimitedReverseCopy.program separator false)) (move Move.right Move.stay)

theorem push_hoare (xs : List Bool) (f : ℤ → Fin (a+4)) (p : ℤ) :
    HoareTime push (fun v => v = Copy.tapes (descriptor xs) f 1 p)
      (fun v => v = Copy.tapes (descriptor xs) (frame f p xs) 1 (p+1+xs.length)) (2*xs.length+7) := by
  let base := Function.update f p separator
  have hs := seek_hoare (Copy.tapes (descriptor xs) base 1 (p+1)) 0 blank Move.right xs.length
    (by intro j hj; simpa [Copy.tapes,Copy.cfg,Config.tapes,Move.offset] using (descriptor_inside (a := a) xs (1+j) (by omega)).2)
    (by simpa [Copy.tapes,Copy.cfg,Config.tapes,Move.offset] using descriptor_end (a := a) xs)
  have hhead : (Copy.tapes (descriptor xs) base 1 (p+1)).head 0 = 1 := rfl
  simp only [hhead, Move.offset, mul_one] at hs
  change HoareTime (seek 0 blank Move.right) (fun v => v = Copy.tapes (descriptor xs) base 1 (p+1))
    (fun v => v = positioned (Copy.tapes (descriptor xs) base 1 (p+1)) 0 (1+xs.length)) xs.length at hs
  rw [positioned_zero] at hs
  have hr := DelimitedReverseCopy.reverse_hoare separator false (empty (a := a)) base 1 (p+1)
    (xs.map bitSymbol) (fun x hx => (bits_ne xs x hx).1) (by simp [empty])
  have hm : (Copy.retained false : Fin (a+4) → Fin (a+4)) = id := rfl
  simp only [List.length_map,hm,List.map_id,← List.map_reverse] at hr
  have hp : (1 : ℤ)+xs.length-1 = xs.length := by omega
  rw [hp] at hr
  have hleft := move_hoare (descriptor xs) base (1+xs.length) (p+1) Move.left Move.stay
  simp only [Move.offset, add_zero] at hleft
  have hcoord : (1 : ℤ)+xs.length+(-1) = xs.length := by omega
  rw [hcoord] at hleft
  have hright := move_hoare (descriptor xs) (frame f p xs) 0 (p+1+xs.length) Move.right Move.stay
  simp only [Move.offset, zero_add, add_zero] at hright
  have hh := ((((push_init (descriptor xs) f 1 p).seq hs).seq
    hleft).seq hr).seq hright
  apply hh.consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- The output descriptor sentinel is physically written, while the stack head
moves from the next-free cell onto its last bit (or its marker for an empty word). -/
def popInit : Program 2 2 a := once (by decide)
  (fun sy i => if i = 0 then (sy i,Move.left) else (separator,Move.right))

private theorem pop_init (f : ℤ → Fin (a+4)) (p : ℤ) :
    HoareTime popInit (fun v => v = Copy.tapes f (fun _ => blank) p 0)
      (fun v => v = Copy.tapes f empty (p-1) 1) 1 := by
  apply (once_hoare (by decide) _ (Copy.tapes f (fun _ => blank) p 0)).consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> simp [Copy.tapes,Copy.cfg,Config.tapes,Move.offset]; omega
  · funext i z; fin_cases i <;> by_cases hz : z = p <;> by_cases hq : z = 0 <;>
      simp_all [Copy.tapes,Copy.cfg,Config.tapes,empty]

/-- Erase the discovered stack marker and position the output for its return scan. -/
def popMarker : Program 2 2 a := once (by decide)
  (fun sy i => if i = 0 then (blank,Move.stay) else (sy i,Move.left))

private theorem pop_marker (f g : ℤ → Fin (a+4)) (p q : ℤ) :
    HoareTime popMarker (fun v => v = Copy.tapes f g p q)
      (fun v => v = Copy.tapes (Function.update f p blank) g p (q-1)) 1 := by
  apply (once_hoare (by decide) _ (Copy.tapes f g p q)).consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> simp [Copy.tapes,Copy.cfg,Config.tapes,Move.offset]; omega
  · funext i z; fin_cases i <;> by_cases hz : z = p <;> by_cases hq : z = q <;>
      simp_all [Copy.tapes,Copy.cfg,Config.tapes]

private theorem cleared_word (f : ℤ → Fin (a+4)) (p : ℤ) (xs : List (Fin (a+4)))
    (hf : ∀ z, p ≤ z → z < p+xs.length → f z = blank) :
    putWord f p (xs.map (Copy.retained true)) = f := by
  funext z
  by_cases hz : p ≤ z ∧ z < p+xs.length
  · have hm := ReturnOrigin.putWord_mem f p (xs.map (Copy.retained true)) z (by simpa using hz)
    obtain ⟨x,_,he⟩ := List.mem_map.mp hm
    rw [hf z hz.1 hz.2]
    exact he.symm
  · exact putWord_outside _ _ _ _ (by simpa using (show z < p ∨ p+xs.length ≤ z by omega))

/-- Fixed eight-state pop into an initially blank output tape. -/
def pop : Program 2 8 a :=
  seq (seq (seq (seq popInit (DelimitedReverseCopy.program separator true)) popMarker)
    (seek 1 separator Move.left)) (move Move.stay Move.right)

theorem pop_hoare (xs : List Bool) (f : ℤ → Fin (a+4)) (p : ℤ)
    (hf : ∀ z, p ≤ z → z < p+1+xs.length → f z = blank) :
    HoareTime pop (fun v => v = Copy.tapes (frame f p xs) (fun _ => blank) (p+1+xs.length) 0)
      (fun v => v = Copy.tapes f (descriptor xs) p 1) (2*xs.length+7) := by
  let base := Function.update f p separator
  have hr := DelimitedReverseCopy.reverse_hoare separator true base (empty (a := a)) (p+1) 1
    (xs.reverse.map bitSymbol) (fun x hx => (bits_ne xs.reverse x hx).1)
    (by simp [base])
  have hc := cleared_word base (p+1) (xs.reverse.map bitSymbol) (by
    intro z hz he
    have hne : z ≠ p := by omega
    simp only [List.length_map,List.length_reverse] at he
    simpa [base,hne] using hf z (by omega) (by omega))
  rw [hc] at hr
  simp only [List.length_map,List.length_reverse,← List.map_reverse,List.reverse_reverse] at hr
  have hpos : p+1+(xs.length : ℤ)-1 = p+xs.length := by omega
  have hpred : p+1-1 = p := by omega
  rw [hpos,hpred] at hr
  have hi := pop_init (frame f p xs) (p+1+xs.length)
  rw [hpos] at hi
  have hm := pop_marker base (descriptor xs) p (1+xs.length)
  have hbase : Function.update base p blank = f := by
    funext z
    by_cases hz : z = p
    · subst z; simp [hf p (by omega) (by omega)]
    · simp [base,hz]
  rw [hbase] at hm
  have hout : (1 : ℤ)+xs.length-1 = xs.length := by omega
  rw [hout] at hm
  have hs := seek_hoare (Copy.tapes f (descriptor xs) p xs.length) 1 separator Move.left xs.length
    (by intro j hj; simpa [Copy.tapes,Copy.cfg,Config.tapes,Move.offset,sub_eq_add_neg] using (descriptor_inside (a := a) xs (xs.length-j) (by omega)).1)
    (by simpa [Copy.tapes,Copy.cfg,Config.tapes,Move.offset] using descriptor_origin (a := a) xs)
  have hhead : (Copy.tapes f (descriptor xs) p xs.length).head 1 = xs.length := rfl
  simp only [hhead,Move.offset,mul_neg_one,add_neg_cancel] at hs
  rw [positioned_one] at hs
  have hend := move_hoare f (descriptor xs) p 0 Move.stay Move.right
  simp only [Move.offset,add_zero,zero_add] at hend
  have hh := (((hi.seq hr).seq hm).seq hs).seq hend
  exact hh.consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- The whole older stack and the untouched suffix survive a push literally. -/
theorem frame_outside (f : ℤ → Fin (a+4)) (p : ℤ) (xs : List Bool) (z : ℤ)
    (hz : z < p ∨ p+1+xs.length ≤ z) : frame f p xs z = f z := by
  rw [frame,putWord_outside _ _ _ _ (by simp only [List.length_map,List.length_reverse]; omega)]
  have hne : z ≠ p := by omega
  simp [hne]

end IntegerMultBounds.Machine.BinaryDescriptorStack
