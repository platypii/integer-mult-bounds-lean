import IntegerMultBounds.Machine.Copy
import IntegerMultBounds.Machine.Reflection
import IntegerMultBounds.Machine.WordMoves
import IntegerMultBounds.Machine.Frame

/-! A fixed parser for the literal multiplication input. It preserves the
packed input and physically copies both operands backwards onto blank tapes.
The copies are least-significant-bit first and their heads finish at their ends. -/
namespace IntegerMultBounds.Machine.MultiplicationInputSplit
noncomputable section
variable {a : ℕ}

def bank (f g h : ℤ → Fin (a+4)) (p q r : ℤ) : Tapes 3 a :=
  ⟨![p,q,r],![f,g,h]⟩
def scan (stop : Fin (a+4)) : Program 1 1 a where
  tapes_pos := by decide
  start := 0
  transition := fun _ sy => if sy 0 = stop then none else some (0,fun i => (sy i,.right))
def oneCfg (f : ℤ → Fin (a+4)) (p : ℤ) (st : Fin 1 := 0) : Config 1 1 a := ⟨st,fun _ => p,fun _ => f⟩

theorem scan_step (stop : Fin (a+4)) (f : ℤ → Fin (a+4)) (p : ℤ) (h : f p ≠ stop) :
    step (scan stop) (oneCfg f p) = some (oneCfg f (p+1)) := by
  simp only [step,scan,oneCfg,h,ite_false,Move.offset]
  congr 1
  congr 1
  funext i j
  by_cases hj : j = p
  · subst j; simp
  · simp [hj]

theorem scan_run (stop : Fin (a+4)) (f : ℤ → Fin (a+4)) (p : ℤ) (n : ℕ)
    (h : ∀ j : ℕ, j < n → f (p+j) ≠ stop) :
    run (scan stop) n (oneCfg f p) = some (oneCfg f (p+n)) := by
  induction n generalizing p with
  | zero => simp [run]
  | succ n ih =>
    rw [add_comm,run_add,run_one,scan_step stop f p (by simpa using h 0 (by omega))]
    simp only [Option.bind_some]
    rw [ih (p+1) (fun j hj => by
      rw [show p+1+(j : ℤ) = p+((j+1 : ℕ) : ℤ) by push_cast; ring]
      exact h (j+1) (by omega))]
    congr 2
    push_cast; ring

theorem scan_hoare (stop : Fin (a+4)) (f : ℤ → Fin (a+4)) (p : ℤ)
    (xs : List (Fin (a+4))) (hx : ∀ x ∈ xs, x ≠ stop) (hend : f (p+xs.length) = stop) :
    HoareTime (scan stop) (fun v => v = (oneCfg (putWord f p xs) p).tapes)
      (fun v => v = (oneCfg (putWord f p xs) (p+xs.length)).tapes) xs.length := by
  rintro v rfl
  refine ⟨xs.length,oneCfg (putWord f p xs) (p+xs.length),le_rfl,?_,?_,rfl⟩
  · exact scan_run stop _ _ _ (fun j hj => hx _
      (ReturnOrigin.putWord_mem f p xs (p+j) ⟨by omega,by omega⟩))
  · simp [step,scan,oneCfg,putWord_outside _ _ _ _ (Or.inr (le_refl _)),hend]

def shift (m : Move) : Program 1 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun st sy => if st = 0 then some (1,fun i => (sy i,m)) else none

theorem shifts (m : Move) (f : ℤ → Fin (a+4)) (p : ℤ) :
    HoareTime (shift m) (fun v => v = ⟨fun _ => p,fun _ => f⟩)
      (fun v => v = ⟨fun _ => p+m.offset,fun _ => f⟩) 1 := by
  rintro v rfl
  let c : Config 1 2 a := ⟨1,fun _ => p+m.offset,fun _ => f⟩
  refine ⟨1,c,le_rfl,?_,?_,rfl⟩
  · rw [run_one]
    simp only [step,Tapes.start,shift,ite_true]
    congr 1
    apply congrArg₂ (Config.mk 1)
    · rfl
    · funext i j
      by_cases hj : j = p <;> simp [hj]
  · simp [step,shift,c]

def mask (i : Fin 2) := decide (i = 0)
def reverseCopy (stop : Fin (a+4)) := Reflection.program (Copy.program stop false) mask

private theorem reflected_cfg (f g : ℤ → Fin (a+4)) (p q : ℤ) :
    Reflection.config mask (Copy.cfg f g p q) = Copy.cfg (fun j => f (-j)) g (-p) q := by
  simp only [Reflection.config,Reflection.tapes,Config.tapes,Copy.cfg]
  congr 1
  · funext i; fin_cases i <;> simp [mask,Reflection.coord]
  · funext i j; fin_cases i <;> simp [mask,Reflection.coord]

/-- Backward source motion and forward destination motion are real transitions. -/
theorem reverse_hoare (stop : Fin (a+4)) (f g : ℤ → Fin (a+4)) (p q : ℤ)
    (xs : List (Fin (a+4))) (hx : ∀ x ∈ xs, x ≠ stop) (hend : f (p-1) = stop) :
    HoareTime (reverseCopy stop) (fun v => v = Copy.tapes (putWord f p xs) g (p+xs.length-1) q)
      (fun v => v = Copy.tapes (putWord f p xs) (putWord g q xs.reverse)
        (p-1) (q+xs.length)) xs.length := by
  let pos := -p-xs.length+1
  have hboundary : (fun j => f (-j)) (pos+xs.reverse.length) = stop := by
    dsimp [pos]; simp only [List.length_reverse]
    rw [← hend]
    congr 1
    omega
  obtain ⟨hr,hh⟩ := Copy.copy_exact stop false (fun j => f (-j)) g pos q xs.reverse
    (fun x hx' => hx x (List.mem_reverse.mp hx')) hboundary
  have hretain : (Copy.retained (a := a) false) = id := rfl
  rw [hretain,List.map_id] at hr hh
  have hw : (fun j => putWord (fun z => f (-z)) pos xs.reverse (-j)) = putWord f p xs := by
    rw [Reflection.word,List.reverse_reverse,List.length_reverse]
    have hp : -pos-xs.length+1 = p := by dsimp [pos]; omega
    rw [hp]
    simp
  have hp : -pos = p+xs.length-1 := by dsimp [pos]; omega
  have hp' : -(pos+xs.reverse.length) = p-1 := by dsimp [pos]; simp only [List.length_reverse]; omega
  simp only [List.length_reverse] at hp'
  have hrun := Reflection.run_eq (Copy.program stop false) mask xs.length
    (Copy.cfg (putWord (fun j => f (-j)) pos xs.reverse) g pos q)
  simp only [List.length_reverse] at hr hh
  rw [hr] at hrun
  have hhalt := Reflection.step_eq (Copy.program stop false) mask
    (Copy.cfg (putWord (fun j => f (-j)) pos xs.reverse) (putWord g q xs.reverse)
      (pos+xs.length) (q+xs.length))
  rw [hh] at hhalt
  simp only [Option.map_some,reflected_cfg,hw,hp,hp'] at hrun
  rintro v rfl
  refine ⟨xs.length,Copy.cfg (putWord f p xs) (putWord g q xs.reverse) (p-1) (q+xs.length),le_rfl,?_,?_,rfl⟩
  · simpa only [reverseCopy,Option.map_some,reflected_cfg,hw,hp,hp',List.length_reverse,Copy.tapes,Tapes.start,Reflection.program,Copy.program,Copy.cfg,Config.tapes] using hrun
  · simpa only [reverseCopy,Option.map_none,reflected_cfg,hw,hp',List.length_reverse] using hhalt


def pair (g h : ℤ → Fin (a+4)) (q r : ℤ) : Tapes 2 a := ⟨![q,r],![g,h]⟩
def single (f : ℤ → Fin (a+4)) (p : ℤ) : Tapes 1 a := ⟨fun _ => p,fun _ => f⟩
theorem single_bank (f g h : ℤ → Fin (a+4)) (p q r : ℤ) :
    (⟨fun _ => p,fun _ => f⟩ : Tapes 1 a).append (pair g h q r) = bank f g h p q r := by
  unfold pair bank Tapes.append
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem copy_bank (f g h : ℤ → Fin (a+4)) (p q r : ℤ) :
    (Copy.tapes f g p q).append (single h r) = bank f g h p q r := by
  unfold Copy.tapes Copy.cfg Config.tapes single bank Tapes.append
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def yPlacement : Fin (2+1) ≃ Fin 3 := Equiv.swap 1 2

theorem y_bank (f g h : ℤ → Fin (a+4)) (p q r : ℤ) :
    ((Copy.tapes f h p r).append (single g q)).reindex yPlacement = bank f g h p q r := by
  unfold Copy.tapes Copy.cfg Config.tapes single bank Tapes.append Tapes.reindex yPlacement
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def scanPart (stop : Fin (a+4)) := extend (scan stop) 2
def shiftPart (m : Move) := extend (shift (a := a) m) 2
def copyX := extend (reverseCopy (a := a) blank) 1
def copyY := reindex (extend (reverseCopy (a := a) separator) 1) yPlacement
/-- The finite transition table depends on neither operand length. -/
def program (a : ℕ) : Program 3 13 a := seq (seq (seq (seq (seq (seq (seq (seq
  (scanPart separator) (shiftPart .left)) copyX) (shiftPart .right))
  (scanPart separator)) (shiftPart .right)) (scanPart blank)) (shiftPart .left)) copyY

def source (x y : List Bool) : ℤ → Fin (a+4) :=
  putWord (fun _ => blank) 0 (x.map bitSymbol ++ [separator] ++ y.map bitSymbol)
def input (x y : List Bool) := bank (source (a := a) x y) (fun _ => blank) (fun _ => blank) 0 0 0
def output (x y : List Bool) := bank (source (a := a) x y)
  (putWord (fun _ => blank) 0 (x.reverse.map bitSymbol))
  (putWord (fun _ => blank) 0 (y.reverse.map bitSymbol)) x.length x.length y.length

theorem source_wordTape (x y : List Bool) :
    source (a := a) x y = wordTape (x.map bitSymbol ++ [separator] ++ y.map bitSymbol) := by
  funext j
  simpa only [source,sub_zero] using putWord_blank (a := a) 0 j (x.map bitSymbol ++ [separator] ++ y.map bitSymbol)

private theorem bits_nonblank (x : List Bool) :
    ∀ b ∈ x.map (bitSymbol (a := a)), b ≠ blank := ReturnOrigin.bits_nonblank x
private theorem bits_noseparator (x : List Bool) :
    ∀ b ∈ x.map (bitSymbol (a := a)), b ≠ separator := by
  intro b hb
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hb
  cases b <;> simp [bitSymbol,separator,Fin.ext_iff]

/-- The two actual reverse copies preserve the whole packed input and halt
with both copy heads at their ends and the source head on the separator. -/
theorem splits (x y : List Bool) :
    HoareTime (program a) (fun v => v = input (a := a) x y)
      (fun v => v = output (a := a) x y) (3*x.length+2*y.length+12) := by
  let X := x.map (bitSymbol (a := a))
  let Y := y.map (bitSymbol (a := a))
  let F := source (a := a) x y
  let FX := putWord (fun _ => blank) (x.length : ℤ) ([separator]++Y)
  let FY := putWord (fun _ => blank) 0 (X++[separator])
  have hXlen : X.length = x.length := List.length_map _
  have hYlen : Y.length = y.length := List.length_map _
  have hFX : putWord FX 0 X = F := by
    dsimp [FX,F,source,X,Y]
    rw [List.append_assoc,putWord_append]
    simp only [List.length_map,zero_add,List.singleton_append]
  have hFY : putWord FY (x.length+1) Y = F := by
    have hpY : (x.length : ℤ)+1 = 0+(X++[separator]).length := by simp [X]
    rw [hpY]
    exact putWord_append_forward (fun _ => blank) 0 (X++[separator]) Y
  have hFXleft : FX (-1) = blank := by
    dsimp [FX]; rw [putWord_outside _ _ _ _ (Or.inl (by omega))]
  have hFXend : FX (0+X.length) = separator := by
    rw [hXlen]; dsimp [FX]; simp only [zero_add,putWord_head]
  have hFYend : FY (x.length+1+Y.length) = blank := by
    dsimp [FY]
    rw [putWord_outside _ _ _ _ (Or.inr (by simp [X,Y]))]
  have hFYleft : FY (x.length+1-1) = separator := by
    dsimp [FY]
    rw [← putWord_append_forward]
    simp only [hXlen,zero_add]
    rw [show (x.length : ℤ)+1-1 = x.length by omega,putWord_head]
  have h1 := hoare_extend_eq (scan_hoare separator FX 0 X (bits_noseparator x) hFXend)
    (pair (fun _ => blank) (fun _ => blank) 0 0)
  simp only [oneCfg,Config.tapes] at h1
  rw [single_bank,single_bank,hFX,hXlen] at h1
  have h2 := hoare_extend_eq (shifts .left F x.length)
    (pair (fun _ => blank) (fun _ => blank) 0 0)
  rw [single_bank,single_bank] at h2
  have h3 := hoare_extend_eq (reverse_hoare blank FX (fun _ => blank) 0 0 X
    (bits_nonblank x) (by simpa using hFXleft)) (single (fun _ => blank) 0)
  rw [copy_bank,copy_bank,hFX,hXlen] at h3
  have h4 := hoare_extend_eq (shifts .right F (-1))
    (pair (putWord (fun _ => blank) 0 X.reverse) (fun _ => blank) x.length 0)
  rw [single_bank,single_bank] at h4
  have h5 := hoare_extend_eq (scan_hoare separator FX 0 X (bits_noseparator x) hFXend)
    (pair (putWord (fun _ => blank) 0 X.reverse) (fun _ => blank) x.length 0)
  simp only [oneCfg,Config.tapes] at h5
  rw [single_bank,single_bank,hFX,hXlen] at h5
  have h6 := hoare_extend_eq (shifts .right F x.length)
    (pair (putWord (fun _ => blank) 0 X.reverse) (fun _ => blank) x.length 0)
  rw [single_bank,single_bank] at h6
  have h7 := hoare_extend_eq (scan_hoare blank FY (x.length+1) Y (bits_nonblank y) hFYend)
    (pair (putWord (fun _ => blank) 0 X.reverse) (fun _ => blank) x.length 0)
  simp only [oneCfg,Config.tapes] at h7
  rw [single_bank,single_bank,hFY,hYlen] at h7
  have h8 := hoare_extend_eq (shifts .left F (x.length+1+y.length))
    (pair (putWord (fun _ => blank) 0 X.reverse) (fun _ => blank) x.length 0)
  rw [single_bank,single_bank] at h8
  have h9 := hoare_place (reverse_hoare separator FY (fun _ => blank) (x.length+1) 0 Y
    (bits_noseparator y) hFYleft) yPlacement (single (putWord (fun _ => blank) 0 X.reverse) x.length)
  rw [y_bank,y_bank,hFY,hYlen] at h9
  simp only [Move.offset,zero_add,zero_sub,Int.add_neg_one,neg_add_cancel] at h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hall := (((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8).seq h9
  apply hall.consequence (fun _ h => h) _ (by omega)
  rintro v rfl
  simp only [output,X,Y,F,List.map_reverse,add_sub_cancel_right]


/-- The precondition is exactly the target theorem's original packed input,
without pre-split words or supplied runtime counts. -/
theorem input_start (x y : List Bool) :
    (input (a := a) x y).start (program a) = Machine.input (program a) x y := by
  apply congrArg₂ (Config.mk (program a).start)
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> simp [input,bank,source_wordTape]

theorem splits_original_input (x y : List Bool) :
    ∃ k ≤ 3*x.length+2*y.length+12, ∃ c : Config 3 13 a,
      run (program a) k (Machine.input (program a) x y) = some c ∧
      step (program a) c = none ∧ c.tapes = output (a := a) x y := by
  obtain ⟨k,c,hk,hr,hh,hout⟩ := splits (a := a) x y _ rfl
  exact ⟨k,hk,c,by simpa only [input_start] using hr,hh,hout⟩

end
end IntegerMultBounds.Machine.MultiplicationInputSplit
