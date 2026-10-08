import IntegerMultBounds.Machine.Frame

/-! One actual transition installs a fixed collection of sentinel cells and
zero/one head positions. Its template is compiled into finite control and may
not depend on input dimensions or payload. -/
namespace IntegerMultBounds.Machine.StaticMarkerInit
variable {t : ℕ}

def raw (template target : Tapes t 0) : Tapes t 0 :=
  ⟨fun _ => 0,fun i => if template.tape i 0 = separator then
    Function.update (target.tape i) 0 blank else target.tape i⟩

@[simp] theorem raw_head (template target : Tapes t 0) (i : Fin t) : (raw template target).head i = 0 := rfl

theorem raw_marker (template target : Tapes t 0) (i : Fin t) (hi : template.tape i 0 = separator) :
    (raw template target).tape i 0 = blank := by simp [raw,hi]

theorem raw_preserves_off_origin (template target : Tapes t 0) (i : Fin t) (z : ℤ) (hz : z ≠ 0) :
    (raw template target).tape i z = target.tape i z := by
  simp only [raw]
  split_ifs <;> simp [Function.update_of_ne hz]

def program (template : Tapes t 0) (ht : 0 < t) : Program t 2 0 where
  tapes_pos := ht
  start := 0
  transition := fun st symbols => if st = 0 then some (1,fun i =>
    (if template.tape i 0 = separator then separator else symbols i,
     if template.head i = 1 then .right else .stay)) else none

theorem initialize_hoare (template target : Tapes t 0) (ht : 0 < t)
    (hhead : target.head = template.head) (hpos : ∀ i, template.head i = 0 ∨ template.head i = 1)
    (hmarker : ∀ i, template.tape i 0 = separator → target.tape i 0 = separator) :
    HoareTime (program template ht) (fun v => v = raw template target) (fun v => v = target) 1 := by
  intro v hv
  subst v
  refine ⟨1,⟨1,target.head,target.tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,program,Tapes.start,ite_true,raw]
    congr 1
    congr 1
    · funext i
      rw [hhead]
      rcases hpos i with hh | hh <;> simp [hh,Move.offset]
    · funext i z
      by_cases hm : template.tape i 0 = separator
      · have hh := hmarker i hm
        by_cases hz : z = 0 <;> simp [hm,hz,hh]
      · by_cases hz : z = 0 <;> simp [hm,hz]
  · simp [step,program]

/-- A pointwise relation suited to decomposing complete finite tape banks. -/
def MarkerRel (v w : Tapes t 0) : Prop := ∀ i, v.tape i 0 = separator → w.tape i 0 = separator

theorem MarkerRel.append {s : ℕ} {v w : Tapes t 0} {x y : Tapes s 0}
    (h : MarkerRel v w) (h' : MarkerRel x y) : MarkerRel (v.append x) (w.append y) := by
  intro i
  induction i using Fin.addCases with
  | left i => simpa only [Tapes.append,Fin.addCases_left] using h i
  | right i => simpa only [Tapes.append,Fin.addCases_right] using h' i

def HeadPos (v : Tapes t 0) : Prop := ∀ i, v.head i = 0 ∨ v.head i = 1

theorem HeadPos.append {s : ℕ} {v : Tapes t 0} {w : Tapes s 0}
    (h : HeadPos v) (h' : HeadPos w) : HeadPos (v.append w) := by
  intro i
  induction i using Fin.addCases with
  | left i => simpa only [Tapes.append,Fin.addCases_left] using h i
  | right i => simpa only [Tapes.append,Fin.addCases_right] using h' i

def HeadEq (v w : Tapes t 0) : Prop := v.head = w.head

theorem HeadEq.append {s : ℕ} {v w : Tapes t 0} {x y : Tapes s 0}
    (h : HeadEq v w) (h' : HeadEq x y) : HeadEq (v.append x) (w.append y) := by
  unfold HeadEq Tapes.append
  rw [h,h']

end IntegerMultBounds.Machine.StaticMarkerInit
