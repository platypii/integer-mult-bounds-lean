import IntegerMultBounds.Machine.Copy
import IntegerMultBounds.Machine.Reflection

/-! Delimiter-driven backward reading with forward output, with no supplied
length descriptor. The source delimiter is retained and all exterior cells are
framed; optionally every copied source symbol is erased. -/
namespace IntegerMultBounds.Machine.DelimitedReverseCopy
variable {a : ℕ}

def mask (i : Fin 2) : Bool := decide (i = 0)
def program (stop : Fin (a+4)) (erase : Bool) := Reflection.program (Copy.program stop erase) mask

private theorem reflected_cfg (f g : ℤ → Fin (a+4)) (p q : ℤ) :
    Reflection.config mask (Copy.cfg f g p q) = Copy.cfg (fun z => f (-z)) g (-p) q := by
  simp only [Reflection.config,Reflection.tapes,Copy.cfg,Config.tapes]
  congr 1
  · funext i; fin_cases i <;> simp [mask,Reflection.coord]
  · funext i z; fin_cases i <;> simp [mask,Reflection.coord]

theorem reverse_exact (stop : Fin (a+4)) (erase : Bool) (f g : ℤ → Fin (a+4))
    (p q : ℤ) (xs : List (Fin (a+4))) (hx : ∀ x ∈ xs, x ≠ stop) (he : f (p-1) = stop) :
    run (program stop erase) xs.length (Copy.cfg (putWord f p xs) g (p+xs.length-1) q) =
      some (Copy.cfg (putWord f p (xs.map (Copy.retained erase))) (putWord g q xs.reverse)
        (p-1) (q+xs.length)) ∧
    step (program stop erase) (Copy.cfg (putWord f p (xs.map (Copy.retained erase)))
      (putWord g q xs.reverse) (p-1) (q+xs.length)) = none := by
  obtain ⟨hr,hh⟩ := Copy.copy_exact stop erase (fun z => f (-z)) g (-p-xs.length+1) q xs.reverse
    (by simpa using hx) (by simpa only [List.length_reverse] using (show f (-(-p-xs.length+1+xs.length)) = stop by convert he using 1; congr 1; omega))
  have hw : (fun z => putWord (fun y => f (-y)) (-p-xs.length+1) xs.reverse (-z)) = putWord f p xs := by
    rw [Reflection.word,List.reverse_reverse,List.length_reverse]
    have hp : -(-p-(xs.length : ℤ)+1)-xs.length+1 = p := by omega
    rw [hp]
    simp only [neg_neg]
  have hout : (fun z => putWord (fun y => f (-y)) (-p-xs.length+1)
      (xs.reverse.map (Copy.retained erase)) (-z)) = putWord f p (xs.map (Copy.retained erase)) := by
    rw [Reflection.word,← List.map_reverse,List.reverse_reverse,List.length_map,List.length_reverse]
    have hp : -(-p-(xs.length : ℤ)+1)-xs.length+1 = p := by omega
    rw [hp]
    simp only [neg_neg]
  have hp : -(-p-(xs.length : ℤ)+1) = p+xs.length-1 := by omega
  have hp' : -(-p-(xs.length : ℤ)+1+xs.length) = p-1 := by omega
  have hrun := Reflection.run_eq (Copy.program stop erase) mask xs.reverse.length
    (Copy.cfg (putWord (fun y => f (-y)) (-p-xs.length+1) xs.reverse) g (-p-xs.length+1) q)
  rw [hr] at hrun
  have hhalt := Reflection.step_eq (Copy.program stop erase) mask
    (Copy.cfg (putWord (fun y => f (-y)) (-p-xs.length+1) (xs.reverse.map (Copy.retained erase)))
      (putWord g q xs.reverse) (-p-xs.length+1+xs.reverse.length) (q+xs.reverse.length))
  rw [hh] at hhalt
  constructor
  · simpa only [program,reflected_cfg,hw,hout,hp,hp',List.length_reverse,Option.map_some] using hrun
  · simpa only [program,reflected_cfg,hout,hp',List.length_reverse,Option.map_none] using hhalt

theorem reverse_hoare (stop : Fin (a+4)) (erase : Bool) (f g : ℤ → Fin (a+4))
    (p q : ℤ) (xs : List (Fin (a+4))) (hx : ∀ x ∈ xs, x ≠ stop) (he : f (p-1) = stop) :
    HoareTime (program stop erase)
      (fun v => v = Copy.tapes (putWord f p xs) g (p+xs.length-1) q)
      (fun v => v = Copy.tapes (putWord f p (xs.map (Copy.retained erase))) (putWord g q xs.reverse)
        (p-1) (q+xs.length)) xs.length := by
  intro v hv
  subst v
  obtain ⟨hr,hh⟩ := reverse_exact stop erase f g p q xs hx he
  exact ⟨xs.length,_,le_rfl,hr,hh,rfl⟩

end IntegerMultBounds.Machine.DelimitedReverseCopy
