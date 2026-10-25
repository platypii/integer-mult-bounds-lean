module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankCopies
public import IntegerMultBounds.MathlibTM2.Mult.ChirpUnaryCopies
public import IntegerMultBounds.MathlibTM2.Node.Params

/-! # Initialize a complete table bank from caller counters and binary words

The caller supplies only two length counters and ordinary input words. Zero
variables may all read the same empty source. Every table slot, header and scratch
condition is established by an executed program; no initialized table bank is assumed.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A n : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def chirpBankInputAssignments (rg : TblR n → Fin T) (input : Fin n → Fin T) : List (Fin T × Fin T) :=
  List.ofFn fun i => (input i, rg (.v i))

def chirpBankLoad (rg : TblR n → Fin T) (input : Fin n → Fin T) (width symbols : Fin T) : Pr P T Q A U :=
  .seq (ucopy width (rg .wr) (rg (.z 0)))
    (.seq (ucopy symbols (rg .wn) (rg (.z 0)))
      (chirpBankCopies (rg .wr) (rg (.z 0)) (rg (.z 1)) (rg (.z 2)) (chirpBankInputAssignments rg input)))

def chirpBankLoadR (rg : TblR n → Fin T) (input : Fin n → Fin T) (W e : ℕ)
    (value : Fin T → ℕ) (R : Fin T → List (Fin (A + 4))) : Fin T → List (Fin (A + 4)) :=
  chirpBankCopiesR W value
    (Function.update (Function.update R (rg .wr) (List.replicate W tick)) (rg .wn) (List.replicate e tick))
    (chirpBankInputAssignments rg input)

def chirpBankLoadCost (rg : TblR n → Fin T) (input : Fin n → Fin T) (W e : ℕ) (bits : Fin T → ℕ) : ℕ :=
  (4 * W + 4) + ((4 * e + 4) + chirpBankCopiesCost W bits (chirpBankInputAssignments rg input))

/-- Initialize the actual binary variables and both unary bank headers, preserving all sources. -/
theorem chirpBankLoad_exec (rg : TblR n → Fin T) (hrg : Function.Injective rg) (input : Fin n → Fin T)
    (width symbols : Fin T) (hwidth : ∀ r, rg r ≠ width) (hsymbols : ∀ r, rg r ≠ symbols)
    (hinput : ∀ i r, rg r ≠ input i) (W e : ℕ) (bits value : Fin T → ℕ)
    (hfit : ∀ i, value (input i) < 2 ^ bits (input i)) (hbits : ∀ i, bits (input i) ≤ W)
    (v : HS T Q A U) (S : Stacks T A) (hw : (S.R width).length = W) (he : (S.R symbols).length = e)
    (hsrc : ∀ i, S.R (input i) = binSyms (bits (input i)) (value (input i)))
    (hblank : ∀ r, S.R (rg r) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (chirpBankLoad rg input width symbols) (mk v S) (chirpBankLoadCost rg input W e bits)
        (mk v' { S with R := chirpBankLoadR rg input W e value S.R }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec (body := body) (hwidth .wr).symm (hwidth (.z 0)).symm
    (hrg.ne (show TblR.wr ≠ .z 0 from by intro h; cases h)) v S (hblank (.z 0))
  rw [hw, hblank .wr, List.append_nil] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R (rg .wr) (List.replicate W tick) }
  obtain ⟨v₂, hu₂, he₂⟩ := ucopy_exec (body := body) (hsymbols .wn).symm (hsymbols (.z 0)).symm
    (hrg.ne (show TblR.wn ≠ .z 0 from by intro h; cases h)) v₁ S₁
    (by simp only [S₁, Function.update_of_ne (hrg.ne (show TblR.z 0 ≠ .wr from by intro h; cases h)), hblank])
  have heSource : (S₁.R symbols).length = e := by
    simpa only [S₁, Function.update_of_ne (hsymbols .wr).symm] using he
  have hwn : S₁.R (rg .wn) = [] := by
    simp only [S₁, Function.update_of_ne (hrg.ne (show TblR.wn ≠ .wr from by intro h; cases h)), hblank]
  rw [heSource, hwn, List.append_nil] at he₂
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rg .wn) (List.replicate e tick) }
  have off (k : Fin T) (hwr : k ≠ rg .wr) (hwn : k ≠ rg .wn) : S₂.R k = S.R k := by
    simp only [S₂, S₁, Function.update_of_ne hwr, Function.update_of_ne hwn]
  have hreg : ∀ p ∈ chirpBankInputAssignments rg input,
      [rg .wr, p.1, p.2, rg (.z 0), rg (.z 1), rg (.z 2)].Nodup := by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    have hin (r : TblR n) : input i ≠ rg r := (hinput i r).symm
    simp [List.nodup_cons, hrg.eq_iff, hinput, hin]
  have hsrcOff : ∀ p ∈ chirpBankInputAssignments rg input,
      ∀ q ∈ chirpBankInputAssignments rg input, p.2 ≠ q.1 := by
    intro p hp q hq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    exact hinput j (.v i)
  obtain ⟨v₃, hu₃, he₃⟩ := chirpBankCopies_exec (body := body) (chirpBankInputAssignments rg input)
    hreg hsrcOff W bits value
    (by intro p hp; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp; exact hfit i)
    (by intro p hp; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp; exact hbits i)
    v₂ S₂ (by simp [S₂, S₁, hrg.eq_iff])
    (by
      intro p hp
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
      exact (off _ (hinput i .wr).symm (hinput i .wn).symm).trans (hsrc i))
    ((off _ (hrg.ne (show TblR.z 0 ≠ .wr from by intro h; cases h)) (hrg.ne (show TblR.z 0 ≠ .wn from by intro h; cases h))).trans (hblank (.z 0)))
    ((off _ (hrg.ne (show TblR.z 1 ≠ .wr from by intro h; cases h)) (hrg.ne (show TblR.z 1 ≠ .wn from by intro h; cases h))).trans (hblank (.z 1)))
    ((off _ (hrg.ne (show TblR.z 2 ≠ .wr from by intro h; cases h)) (hrg.ne (show TblR.z 2 ≠ .wn from by intro h; cases h))).trans (hblank (.z 2)))
  exact ⟨v₃, hu₃.trans (hu₂.trans hu₁), Exec.seq he₁ (Exec.seq he₂ he₃)⟩

/-- Every table-machine precondition follows from the initialized slots, including unused zeros. -/
theorem chirpBankLoad_holds (rg : TblR n → Fin T) (hrg : Function.Injective rg) (input : Fin n → Fin T)
    (W e : ℕ) (value : Fin T → ℕ) (S : Stacks T A) (hblank : ∀ r, S.R (rg r) = []) :
    tblHolds rg { S with R := chirpBankLoadR rg input W e value S.R }
      (tblRho W (List.replicate W tick) (List.replicate e tick) ⟨fun i => value (input i), []⟩) := by
  let R := Function.update (Function.update S.R (rg .wr) (List.replicate W tick)) (rg .wn) (List.replicate e tick)
  have hnd : ((chirpBankInputAssignments rg input).map Prod.snd).Nodup := by
    simp only [chirpBankInputAssignments, List.map_ofFn, Function.comp_def, List.nodup_ofFn]
    exact fun i j h => TblR.v.inj (hrg h)
  have off (r : TblR n) (hr : ∀ i, r ≠ .v i) :
      chirpBankCopiesR W value R (chirpBankInputAssignments rg input) (rg r) = R (rg r) := by
    apply chirpBankCopiesR_off
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact hrg.ne (hr i).symm
  intro r
  cases r with
  | v i =>
    have ha := chirpBankCopiesR_at W value R (chirpBankInputAssignments rg input) hnd
      (input i, rg (.v i)) (List.mem_ofFn.mpr ⟨i, rfl⟩)
    simpa [chirpBankLoadR, R, hrg.eq_iff, hblank] using ha
  | wr =>
    change chirpBankCopiesR W value R (chirpBankInputAssignments rg input) (rg .wr) = _
    rw [off .wr (by intro i h; cases h)]
    simp [R, hrg.eq_iff]
  | wn =>
    change chirpBankCopiesR W value R (chirpBankInputAssignments rg input) (rg .wn) = _
    rw [off .wn (by intro i h; cases h)]
    simp [R]
  | acc =>
    change chirpBankCopiesR W value R (chirpBankInputAssignments rg input) (rg .acc) = _
    rw [off .acc (by intro i h; cases h)]
    simp [R, hrg.eq_iff, hblank]
  | z j =>
    change chirpBankCopiesR W value R (chirpBankInputAssignments rg input) (rg (.z j)) = _
    rw [off (.z j) (by intro i h; cases h)]
    simp [R, hrg.eq_iff, hblank]

/-- Loading a bank preserves every register outside its allocated roles. -/
theorem chirpBankLoad_off (rg : TblR n → Fin T) (input : Fin n → Fin T)
    (W e : ℕ) (value : Fin T → ℕ) (R : Fin T → List (Fin (A + 4)))
    (k : Fin T) (hoff : ∀ r, k ≠ rg r) :
    chirpBankLoadR rg input W e value R k = R k := by
  unfold chirpBankLoadR
  rw [chirpBankCopiesR_off _ _ _ _ _ (by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact (hoff (.v i)).symm)]
  simp only [Function.update_of_ne (hoff .wn), Function.update_of_ne (hoff .wr)]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
