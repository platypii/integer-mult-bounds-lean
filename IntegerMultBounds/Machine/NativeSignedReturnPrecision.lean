import IntegerMultBounds.Machine.NativeSignedReturnReuse

/-! An original-count driven fixed machine repeats the executable native
precision-return pass. Every pass restores its source, scratch and private
controls, so actual returned words can feed the next sibling at the certified
coarser exponent. Repetition cost is explicit; no asymptotic absorption is
asserted here. -/
namespace IntegerMultBounds.Machine.NativeSignedReturnPrecision
noncomputable section
open RadixSignedShiftRight (Word shifted)
open NativeSignedReturnStream (volume work)

def words (ws : List Word) (d : ℕ) := ws.map (shifted^[d])
def state (ws : List Word) (bs ds : List Bool) (d : ℕ) : Tapes 6 2 :=
  (CountedLoopHeaderClean.bank (NativeSignedReturnClean.input (words ws d) bs)).append
    (NativeSignedReturnClean.header ds)
def program := CountedLoopHeaderClean.program (extend NativeSignedReturnReuse.program 1) (5:Fin 6)
def cost (ws : List Word) (bs ds : List Bool) (d : ℕ) :=
  d*NativeSignedReturnReuse.cost ws bs+6*d+11*ds.length+35

theorem word_length (w : Word) (hn : w≠[]) (d : ℕ) : ((shifted^[d]) w).length=w.length := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Nat.add_one,Function.iterate_succ']
    exact (RadixSignedShiftRight.shifted_length _ (by intro h; rw [h] at ih; simp at ih; exact hn (List.eq_nil_of_length_eq_zero ih.symm))).trans ih

theorem words_nonempty (ws : List Word) (hn : ∀ w∈ws,w≠[]) (d : ℕ) :
    ∀ w∈words ws d,w≠[] := by
  intro w hw
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hw
  intro he
  have hl := word_length x (hn x hx) d
  rw [he] at hl
  exact hn x hx (List.eq_nil_of_length_eq_zero hl.symm)

theorem words_volume (ws : List Word) (hn : ∀ w∈ws,w≠[]) (d : ℕ) :
    volume (words ws d)=volume ws := by
  induction d with
  | zero => simp [words]
  | succ d ih =>
    have hs : words ws (d+1)=(words ws d).map shifted := by
      simp only [words,List.map_map,Function.comp_def,Nat.add_one,Function.iterate_succ']
    rw [hs,NativeSignedReturnStream.volume_shifted _ (words_nonempty ws hn d),ih]

theorem words_cost (ws : List Word) (hn : ∀ w∈ws,w≠[]) (bs : List Bool) (d : ℕ) :
    NativeSignedReturnReuse.cost (words ws d) bs=NativeSignedReturnReuse.cost ws bs := by
  simp only [NativeSignedReturnReuse.cost,work,words_volume ws hn d]
  simp only [words,List.length_map]

/-- Literal restoration of an arbitrary runtime exponent gap, with retained
length/count headers and all four generated controls blank at both endpoints. -/
theorem runs (ws : List Word) (hn : ∀ w∈ws,w≠[]) (bs ds : List Bool) (d : ℕ)
    (hlen : Counter.value bs=volume ws) (hcount : Counter.value ds=d) :
    HoareTime program
      (fun v => v=CountedLoopHeaderClean.bank (state ws bs ds 0))
      (fun v => v=CountedLoopHeaderClean.bank (state ws bs ds d)) (cost ws bs ds d) := by
  have hh := CountedLoopHeaderClean.runs (extend NativeSignedReturnReuse.program 1) (5:Fin 6) ds d
    (state ws bs ds) (fun _ => NativeSignedReturnReuse.cost ws bs)
    (by constructor <;> rfl) hcount (by
      intro i _
      have hb := NativeSignedReturnReuse.runs (words ws i) (words_nonempty ws hn i) bs
        (by rw [words_volume ws hn i]; exact hlen)
      have hs : (words ws i).map shifted=words ws (i+1) := by
        simp only [words,List.map_map,Function.comp_def,Nat.add_one,Function.iterate_succ']
      rw [hs,words_cost ws hn bs i] at hb
      exact hoare_extend_eq hb (NativeSignedReturnClean.header ds))
  simpa only [program,cost,CountedLoopHeaderClean.cost,Finset.sum_const,
    Finset.card_range,smul_eq_mul] using hh

theorem cost_linear (ws : List Word) (bs ds : List Bool) (d : ℕ)
    (hlen : Counter.value bs=volume ws) (hc : GrowingCounterData.Canonical bs) :
    cost ws bs ds d≤d*(111*volume ws+284)+6*d+11*ds.length+35 := by
  have hw := GrowingCounterData.canonical_width bs hc
  rw [hlen] at hw
  have hh := Nat.log2_le_self (volume ws)
  have hs := NativeSignedReturnStream.work_linear ws
  have hb : NativeSignedReturnReuse.cost ws bs≤111*volume ws+284 := by
    unfold NativeSignedReturnReuse.cost
    omega
  unfold cost
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.mul_le_mul_left d hb) (6*d)) (11*ds.length)) 35

/-- Exact caller endpoints: source and scratch heads are at zero, the scratch
and all four generated controls are blank, and only original headers remain. -/
theorem endpoint (ws : List Word) (bs ds : List Bool) (d : ℕ) :
    let v := CountedLoopHeaderClean.bank (state ws bs ds d)
    v.head 0=0 ∧ v.tape 0=putWord (fun _ => blank) 0 (NativeSignedReturnStream.encode (words ws d)) ∧
    v.head 1=0 ∧ v.tape 1=(fun _ => blank) ∧
    (∀ i:Fin 8,i∈[3,4,6,7] → v.head i=0 ∧ v.tape i=(fun _ => blank)) := by
  simp only [state,CountedLoopHeaderClean.bank,NativeSignedReturnClean.input,
    RadixSignedShiftRight.tapes,RadixSignedShiftRight.cfg,Config.tapes,Tapes.append,
    Fin.addCases,SharedBank.empty,NativeSignedReturnClean.header]
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  intro i hi
  fin_cases i <;> simp at hi ⊢

abbrev Coefficient := Word × Word
def fields (cs : List Coefficient) := cs.flatMap (fun c => [c.1,c.2])
def returned (cs : List Coefficient) (d : ℕ) :=
  cs.map (fun c => ((shifted^[d]) c.1,(shifted^[d]) c.2))
def decoded (b n : ℕ) (c : Coefficient) :=
  ButterflySigned.complexValue (ButterflySigned.signedValue b c.1)
    (ButterflySigned.signedValue b c.2) n

theorem words_fields (cs : List Coefficient) (d : ℕ) :
    words (fields cs) d=fields (returned cs d) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [words,fields,returned] at *; exact ih

theorem native_serialization (cs : List Coefficient) :
    NativeSignedReturnStream.encode (fields cs)=
      cs.flatMap (fun c => DelimitedRadixRecord.complex c.1 c.2) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [fields,List.flatMap_cons,NativeSignedReturnStream.encode,
      List.map_append,List.map_cons,List.map_nil,List.flatten_append,List.flatten_cons,
      List.flatten_nil,List.append_nil,DelimitedRadixRecord.complex,List.append_assoc] at *
    rw [ih]

theorem fields_nonempty (cs : List Coefficient) (b : ℕ)
    (hw : ∀ c∈cs,c.1.length=b+1 ∧ c.2.length=b+1) : ∀ w∈fields cs,w≠[] := by
  intro w hwf
  obtain ⟨c,hc,hwm⟩ := List.mem_flatMap.mp hwf
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hwm
  rcases hwm with rfl|rfl
  · intro h; have hlen := (hw c hc).1; simp [h] at hlen
  · intro h; have hlen := (hw c hc).2; simp [h] at hlen

theorem coefficient_exact (cs : List Coefficient) (b n d M : ℕ)
    (hw : ∀ c∈cs,c.1.length=b+1 ∧ c.2.length=b+1)
    (hg : ∀ c∈cs,Networks.GaussianPrecision.BoundedGrid n M (decoded b (n+d) c)) :
    ∀ c∈cs, ((shifted^[d]) c.1).length=b+1 ∧ ((shifted^[d]) c.2).length=b+1 ∧
      decoded b n ((shifted^[d]) c.1,(shifted^[d]) c.2)=decoded b (n+d) c := by
  intro c hc
  exact SignedRadixExactReturn.exact_return_iterate b n d M c.1 c.2
    (hw c hc).1 (hw c hc).2 (hg c hc)

/-- The actual repeated field machine returns the original Gaussian stream
layout at the certified lower exponent, with genuine source/scratch/control
restoration. Grid membership alone provides divisibility, never word width. -/
theorem gaussian_return (cs : List Coefficient) (b n d M : ℕ) (bs ds : List Bool)
    (hw : ∀ c∈cs,c.1.length=b+1 ∧ c.2.length=b+1)
    (hg : ∀ c∈cs,Networks.GaussianPrecision.BoundedGrid n M (decoded b (n+d) c))
    (hlen : Counter.value bs=volume (fields cs)) (hcount : Counter.value ds=d) :
    HoareTime program
      (fun v => v=CountedLoopHeaderClean.bank (state (fields cs) bs ds 0))
      (fun v => v=CountedLoopHeaderClean.bank
        ((CountedLoopHeaderClean.bank (NativeSignedReturnClean.input (fields (returned cs d)) bs)).append
          (NativeSignedReturnClean.header ds))) (cost (fields cs) bs ds d) ∧
    (∀ c∈cs, ((shifted^[d]) c.1).length=b+1 ∧ ((shifted^[d]) c.2).length=b+1 ∧
      decoded b n ((shifted^[d]) c.1,(shifted^[d]) c.2)=decoded b (n+d) c) := by
  constructor
  · have hh := runs (fields cs) (fields_nonempty cs b hw) bs ds d hlen hcount
    simpa only [state,words_fields] using hh
  · exact coefficient_exact cs b n d M hw hg

end
end IntegerMultBounds.Machine.NativeSignedReturnPrecision
