import IntegerMultBounds.Machine.Gather
import IntegerMultBounds.Machine.ColumnTransducer
import IntegerMultBounds.Machine.WordMoves

/-! One line of packed address arithmetic on five tapes: gather a packed
offset from the digit fields of a source word under the control word, rewind,
combine the accumulator with the offset by a column transducer into a fresh
target word, erase the offset and rewind. Source, control and accumulator are
preserved; the target holds the exact transduced word; the offset scratch is
blank again; every head is back at its origin. -/

namespace IntegerMultBounds.Machine.PackedLine

variable {a : ℕ}

open ColumnTransducer (Rule)

/-- The five-tape bank: source, control, offset scratch, accumulator, target. -/
def bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) : Tapes 5 a :=
  ⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3 else p4,
   fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f3 else f4⟩

def tPlace : Fin (3 + 2) ≃ Fin 5 where
  toFun := fun i => if i = 0 then 3 else if i = 1 then 2 else if i = 2 then 4 else if i = 3 then 0 else 1
  invFun := fun i => if i = 0 then 3 else if i = 1 then 4 else if i = 2 then 1 else if i = 3 then 0 else 2
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def r1 : Fin (1 + 4) ≃ Fin 5 where
  toFun := fun i => if i = 0 then 1 else if i = 1 then 0 else if i = 2 then 2 else if i = 3 then 3 else 4
  invFun := fun i => if i = 0 then 1 else if i = 1 then 0 else if i = 2 then 2 else if i = 3 then 3 else 4
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def r2 : Fin (1 + 4) ≃ Fin 5 where
  toFun := fun i => if i = 0 then 2 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 3 else 4
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 0 else if i = 3 then 3 else 4
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def r3 : Fin (1 + 4) ≃ Fin 5 where
  toFun := fun i => if i = 0 then 3 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 2 else 4
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 0 else 4
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def r4 : Fin (1 + 4) ≃ Fin 5 where
  toFun := fun i => if i = 0 then 4 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 2 else 3
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 4 else 0
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem gather_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) :
    (Gather.bank f0 f1 f2 p0 p1 p2).append
      (⟨fun i => if i = 0 then p3 else p4, fun i => if i = 0 then f3 else f4⟩ : Tapes 2 a) =
      bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.append Gather.bank bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem trans_bank {s : ℕ} (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) (st : Fin (s + 1)) :
    ((ColumnTransducer.cfg f3 f2 f4 p3 p2 p4 st).tapes.append
      (⟨fun i => if i = 0 then p0 else p1, fun i => if i = 0 then f0 else f1⟩ : Tapes 2 a)).reindex
        tPlace = bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.reindex Tapes.append ColumnTransducer.cfg Config.tapes bank tPlace
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem r0_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) :
    (⟨fun _ => p0, fun _ => f0⟩ : Tapes 1 a).append
      (⟨fun i => if i = 0 then p1 else if i = 1 then p2 else if i = 2 then p3 else p4,
        fun i => if i = 0 then f1 else if i = 1 then f2 else if i = 2 then f3 else f4⟩ : Tapes 4 a) =
      bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.append bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem r1_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) :
    ((⟨fun _ => p1, fun _ => f1⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p2 else if i = 2 then p3 else p4, fun i => if i = 0 then f0 else if i = 1 then f2 else if i = 2 then f3 else f4⟩ : Tapes 4 a)).reindex r1 = bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.reindex Tapes.append bank r1
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem r2_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) :
    ((⟨fun _ => p2, fun _ => f2⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p3 else p4, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f3 else f4⟩ : Tapes 4 a)).reindex r2 = bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.reindex Tapes.append bank r2
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem r3_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) :
    ((⟨fun _ => p3, fun _ => f3⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else p4, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else f4⟩ : Tapes 4 a)).reindex r3 = bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.reindex Tapes.append bank r3
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem r4_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) :
    ((⟨fun _ => p4, fun _ => f4⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else p3, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else f3⟩ : Tapes 4 a)).reindex r4 = bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.reindex Tapes.append bank r4
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def gatherPart (op : Bool → Bool → Bool) (S : Gather.Shape) (n : ℕ) (a : ℕ) :=
  extend (Gather.program op S n a) 2
def transPart {s : ℕ} (R : Rule s) (a : ℕ) : Program 5 (s + 1) a :=
  reindex (extend (ColumnTransducer.program R a) 2) tPlace
def ret0 (a : ℕ) : Program 5 3 a := extend (ReturnOrigin.program (a := a)) 4
def ret1 (a : ℕ) : Program 5 3 a := reindex (extend (ReturnOrigin.program (a := a)) 4) r1
def ret2 (a : ℕ) : Program 5 3 a := reindex (extend (ReturnOrigin.program (a := a)) 4) r2
def ret3 (a : ℕ) : Program 5 3 a := reindex (extend (ReturnOrigin.program (a := a)) 4) r3
def ret4 (a : ℕ) : Program 5 3 a := reindex (extend (ReturnOrigin.program (a := a)) 4) r4
def erase2 (a : ℕ) : Program 5 3 a := reindex (extend (EraseBack.program (a := a)) 4) r2

/-- The line: gather, three rewinds, transduce, erase, two rewinds. -/
def program (op : Bool → Bool → Bool) (S : Gather.Shape) (n : ℕ) {s : ℕ} (R : Rule s) (a : ℕ) :=
  seq (seq (seq (seq (seq (seq (seq (gatherPart op S n a) (ret0 a)) (ret1 a)) (ret2 a))
    (transPart R a)) (erase2 a)) (ret3 a)) (ret4 a)

/-- The cost of a line for `n` digits, an accumulator of width `m` and a
source of which `n` strides are scanned. -/
def lineCost (S : Gather.Shape) (n m : ℕ) : ℕ :=
  n * (Gather.digitCost S + 1) + 1 + (n * S.sx + 2) + 1 + (n + 2) + 1 + (n * S.st + 2) + 1 + m + 1 +
    (n * S.st + 2) + 1 + (m + 2) + 1 + (m + 2)

variable (op : Bool → Bool → Bool) (S : Gather.Shape) {s : ℕ} (R : Rule s) (xs zs acc : List Bool)
  (f g h : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ)

/-- The line contract. -/
theorem line_hoare (hxs : zs.length * S.sx ≤ xs.length) (hacc : acc.length = zs.length * S.st)
    (hf : f (p0 - 1) = blank) (hg : g (p1 - 1) = blank) (hh : h (p3 - 1) = blank)
    (hh' : h (p3 + acc.length) = blank) :
    HoareTime (program op S zs.length R a)
      (fun v => v = bank (putWord f p0 (xs.map bitSymbol)) (putWord g p1 (zs.map bitSymbol))
        (fun _ => blank) (putWord h p3 (acc.map bitSymbol)) (fun _ => blank) p0 p1 p2 p3 p4)
      (fun v => v = bank (putWord f p0 (xs.map bitSymbol)) (putWord g p1 (zs.map bitSymbol))
        (fun _ => blank) (putWord h p3 (acc.map bitSymbol))
        (putWord (fun _ => blank) p4
          ((ColumnTransducer.digits R 0 (acc.zip (Gather.gather op S xs zs zs.length))).map bitSymbol))
        p0 p1 p2 p3 p4)
      (lineCost S zs.length acc.length) := by
  set n := zs.length with hn
  set G := Gather.gather op S xs zs n with hG
  set D := ColumnTransducer.digits R 0 (acc.zip G) with hD
  have hGl : G.length = n * S.st := Gather.gather_length op S xs zs n
  have hDl : D.length = acc.length := by
    rw [hD, ColumnTransducer.digits_length, List.length_zip, hGl, hacc, min_self]
  have hlen : acc.length = G.length := by rw [hGl, hacc]
  -- gather
  have h1 := hoare_extend_eq (Gather.gather_hoare op S xs zs f g (fun _ => blank) p0 p1 p2 hxs)
    (⟨fun i => if i = 0 then p3 else p4,
      fun i => if i = 0 then putWord h p3 (acc.map bitSymbol) else (fun _ => blank)⟩ : Tapes 2 a)
  rw [gather_bank, gather_bank] at h1
  -- rewind the source over the scanned prefix
  have hsplit : xs.map bitSymbol = (xs.take (n * S.sx)).map (bitSymbol (a := a)) ++
      (xs.drop (n * S.sx)).map bitSymbol := by rw [← List.map_append, List.take_append_drop]
  have htake : ((xs.take (n * S.sx)).map (bitSymbol (a := a))).length = n * S.sx := by
    simp [List.length_take]; omega
  have h2 := hoare_extend_eq (ReturnOrigin.return_hoare_prefix f p0
    ((xs.take (n * S.sx)).map bitSymbol) ((xs.drop (n * S.sx)).map bitSymbol)
    (ReturnOrigin.bits_nonblank _) hf)
    (⟨fun i => if i = 0 then p1 + n else if i = 1 then p2 + n * S.st else if i = 2 then p3 else p4,
      fun i => if i = 0 then putWord g p1 (zs.map bitSymbol)
        else if i = 1 then putWord (fun _ => blank) p2 (G.map bitSymbol)
        else if i = 2 then putWord h p3 (acc.map bitSymbol) else (fun _ => blank)⟩ : Tapes 4 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at h2
  rw [r0_bank, r0_bank, ← hsplit, htake] at h2
  -- rewind the control
  have h3 := hoare_place (ReturnOrigin.return_hoare_at g p1 (zs.map bitSymbol)
    (ReturnOrigin.bits_nonblank _) hg) r1
    (⟨fun i => if i = 0 then p0 else if i = 1 then p2 + n * S.st else if i = 2 then p3 else p4,
      fun i => if i = 0 then putWord f p0 (xs.map bitSymbol)
        else if i = 1 then putWord (fun _ => blank) p2 (G.map bitSymbol)
        else if i = 2 then putWord h p3 (acc.map bitSymbol) else (fun _ => blank)⟩ : Tapes 4 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at h3
  rw [r1_bank, r1_bank, List.length_map, ← hn] at h3
  -- rewind the offset
  have h4 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) p2 (G.map bitSymbol)
    (ReturnOrigin.bits_nonblank _) rfl) r2
    (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p3 else p4,
      fun i => if i = 0 then putWord f p0 (xs.map bitSymbol)
        else if i = 1 then putWord g p1 (zs.map bitSymbol)
        else if i = 2 then putWord h p3 (acc.map bitSymbol) else (fun _ => blank)⟩ : Tapes 4 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at h4
  rw [r2_bank, r2_bank, List.length_map, hGl] at h4
  -- transduce
  have h5 := hoare_place (ColumnTransducer.transduce_hoare R acc G hlen h (fun _ => blank)
    (fun _ => blank) p3 p2 p4 hh' rfl) tPlace
    (⟨fun i => if i = 0 then p0 else p1,
      fun i => if i = 0 then putWord f p0 (xs.map bitSymbol) else putWord g p1 (zs.map bitSymbol)⟩ :
      Tapes 2 a)
  rw [trans_bank, trans_bank, ← hD, ← hlen] at h5
  -- erase the offset
  have h6 := hoare_place (EraseBack.erase_hoare (fun _ => blank) p2 (G.map bitSymbol)
    (ReturnOrigin.bits_nonblank _) rfl (fun _ _ => rfl)) r2
    (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p3 + acc.length
        else p4 + acc.length,
      fun i => if i = 0 then putWord f p0 (xs.map bitSymbol)
        else if i = 1 then putWord g p1 (zs.map bitSymbol)
        else if i = 2 then putWord h p3 (acc.map bitSymbol)
        else putWord (fun _ => blank) p4 (D.map bitSymbol)⟩ : Tapes 4 a)
  simp only [EraseBack.cfg, Config.tapes] at h6
  rw [r2_bank, r2_bank, List.length_map, ← hlen] at h6
  -- rewind the accumulator
  have h7 := hoare_place (ReturnOrigin.return_hoare_at h p3 (acc.map bitSymbol)
    (ReturnOrigin.bits_nonblank _) hh) r3
    (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else p4 + acc.length,
      fun i => if i = 0 then putWord f p0 (xs.map bitSymbol)
        else if i = 1 then putWord g p1 (zs.map bitSymbol)
        else if i = 2 then (fun _ => blank)
        else putWord (fun _ => blank) p4 (D.map bitSymbol)⟩ : Tapes 4 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at h7
  rw [r3_bank, r3_bank, List.length_map] at h7
  -- rewind the target
  have h8 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) p4 (D.map bitSymbol)
    (ReturnOrigin.bits_nonblank _) rfl) r4
    (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else p3,
      fun i => if i = 0 then putWord f p0 (xs.map bitSymbol)
        else if i = 1 then putWord g p1 (zs.map bitSymbol)
        else if i = 2 then (fun _ => blank) else putWord h p3 (acc.map bitSymbol)⟩ : Tapes 4 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at h8
  rw [r4_bank, r4_bank, List.length_map, hDl] at h8
  have hall := ((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8
  simp only [← hn] at hall
  refine hall.consequence (fun v hv => hv) (fun v hv => hv) ?_
  unfold lineCost
  omega

end IntegerMultBounds.Machine.PackedLine
