import IntegerMultBounds.Machine.ExactFrame

/-! A stride gadget assembling a packed word from digit fields of a source
word under a one-bit-per-digit control. For each of `n` digits the source
head skips to the field, each field bit is combined with the digit's control
bit by a fixed Boolean operation and written into the target digit at a
chosen offset, the remaining target cells of the digit are zero, and the
heads move on by one source stride, one target stride and one control bit.
Everything is unrolled into finite control; the cost is linear in the total
stride width. The four packed offsets of the compact-control address
arithmetic and the selected-bit toggle mask are instances. -/

namespace IntegerMultBounds.Machine.Gather

variable {a : ℕ}

/-- Strides and offsets: the field of `d` bits starts `ox` into each source
digit of `sx` bits and is placed `ot` into each target digit of `st` bits. -/
structure Shape where
  sx : ℕ
  ox : ℕ
  d : ℕ
  st : ℕ
  ot : ℕ
  hx : ox + d ≤ sx
  ht : ot + d ≤ st

section Lists

/-- `d` bits of a word from a start position, missing bits read as zero. -/
def field (xs : List Bool) (start d : ℕ) : List Bool :=
  (List.range d).map fun j => xs.getD (start + j) false

@[simp] theorem field_zero (xs : List Bool) (start : ℕ) : field xs start 0 = [] := rfl

theorem field_succ (xs : List Bool) (start d : ℕ) :
    field xs start (d + 1) = field xs start d ++ [xs.getD (start + d) false] := by
  simp [field, List.range_succ]

@[simp] theorem field_length (xs : List Bool) (start d : ℕ) : (field xs start d).length = d := by
  simp [field]

/-- One target digit. -/
def digitWord (op : Bool → Bool → Bool) (S : Shape) (xs zs : List Bool) (i : ℕ) : List Bool :=
  List.replicate S.ot false ++
    (field xs (i * S.sx + S.ox) S.d).map (fun x => op x (zs.getD i false)) ++
    List.replicate (S.st - S.ot - S.d) false

theorem digitWord_length (op : Bool → Bool → Bool) (S : Shape) (xs zs : List Bool) (i : ℕ) :
    (digitWord op S xs zs i).length = S.st := by
  have := S.ht
  simp [digitWord]
  omega

/-- The target word after `n` digits. -/
def gather (op : Bool → Bool → Bool) (S : Shape) (xs zs : List Bool) : ℕ → List Bool
  | 0 => []
  | i + 1 => gather op S xs zs i ++ digitWord op S xs zs i

theorem gather_length (op : Bool → Bool → Bool) (S : Shape) (xs zs : List Bool) (n : ℕ) :
    (gather op S xs zs n).length = n * S.st := by
  induction n with
  | zero => simp [gather]
  | succ n ih => simp [gather, ih, digitWord_length]; ring

theorem putWord_getD (f : ℤ → Fin (a + 4)) (p : ℤ) (xs : List Bool) (k : ℕ) (hk : k < xs.length) :
    putWord f p (xs.map bitSymbol) (p + k) = bitSymbol (xs.getD k false) := by
  induction xs generalizing f p k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero => simp [putWord_head]
    | succ k =>
      rw [List.map_cons, putWord_cons, show p + ((k + 1 : ℕ) : ℤ) = p + 1 + k by omega,
        ih _ (p + 1) k (by simpa using hk)]
      rfl

end Lists

section Machine

/-- The three-tape bank: source, control, target. -/
def bank (f g h : ℤ → Fin (a + 4)) (px pz pt : ℤ) : Tapes 3 a :=
  ⟨fun i => if i = 0 then px else if i = 1 then pz else pt,
   fun i => if i = 0 then f else if i = 1 then g else h⟩

/-- A one-tape routine at the target slot. -/
def tPlace : Fin (1 + 2) ≃ Fin 3 where
  toFun := fun i => if i = 0 then 2 else if i = 1 then 0 else 1
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else 0
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- A one-tape routine at the control slot. -/
def zPlace : Fin (1 + 2) ≃ Fin 3 where
  toFun := fun i => if i = 0 then 1 else if i = 1 then 0 else 2
  invFun := fun i => if i = 0 then 1 else if i = 1 then 0 else 2
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def skipX (a : ℕ) : Program 3 2 a := extend (StepRight.program (a := a)) 2
def zeroT (a : ℕ) : Program 3 2 a := reindex (extend (WriteZero.program (a := a)) 2) tPlace
def stepZ (a : ℕ) : Program 3 2 a := reindex (extend (StepRight.program (a := a)) 2) zPlace

/-- Combine the source and control bits under the operation into the target
cell; the source and target heads advance, the control head stays. -/
def opCell (op : Bool → Bool → Bool) (a : ℕ) : Program 3 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols =>
    if s = 0 then
      some (1, fun i => (if i = 2 then bitSymbol (op (decide (symbols 0 = bitSymbol true))
        (decide (symbols 1 = bitSymbol true))) else symbols i, if i = 1 then .stay else .right))
    else none

theorem opCell_hoare (op : Bool → Bool → Bool) (f g h : ℤ → Fin (a + 4)) (px pz pt : ℤ) (x z : Bool)
    (hx : f px = bitSymbol x) (hz : g pz = bitSymbol z) :
    HoareTime (opCell op a) (fun v => v = bank f g h px pz pt)
      (fun v => v = bank f g (Function.update h pt (bitSymbol (op x z))) (px + 1) pz (pt + 1)) 1 := by
  rintro v rfl
  refine ⟨1, ⟨1, (bank f g (Function.update h pt (bitSymbol (op x z))) (px + 1) pz (pt + 1)).head,
    (bank f g (Function.update h pt (bitSymbol (op x z))) (px + 1) pz (pt + 1)).tape⟩, le_rfl, ?_,
    by simp [step, opCell], rfl⟩
  rw [run_one]
  have hx' : decide (f px = bitSymbol true) = x := by rw [hx]; cases x <;> simp [bitSymbol]
  have hz' : decide (g pz = bitSymbol true) = z := by rw [hz]; cases z <;> simp [bitSymbol]
  simp only [step, opCell, Tapes.start, bank, ↓reduceIte, hx', Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp [Function.update_apply, eq_comm, hz']
    all_goals (try (intro hj; rw [hj]))

theorem x_bank (f g h : ℤ → Fin (a + 4)) (px pz pt : ℤ) (s : Fin 2) :
    (StepRight.cfg f px s).tapes.append
      (⟨fun i => if i = 0 then pz else pt, fun i => if i = 0 then g else h⟩ : Tapes 2 a) =
      bank f g h px pz pt := by
  unfold Tapes.append StepRight.cfg Config.tapes bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem t_bank (f g h : ℤ → Fin (a + 4)) (px pz pt : ℤ) :
    ((⟨fun _ => pt, fun _ => h⟩ : Tapes 1 a).append
      (⟨fun i => if i = 0 then px else pz, fun i => if i = 0 then f else g⟩ : Tapes 2 a)).reindex
        tPlace = bank f g h px pz pt := by
  unfold Tapes.reindex Tapes.append bank tPlace
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem z_bank (f g h : ℤ → Fin (a + 4)) (px pz pt : ℤ) :
    ((⟨fun _ => pz, fun _ => g⟩ : Tapes 1 a).append
      (⟨fun i => if i = 0 then px else pt, fun i => if i = 0 then f else h⟩ : Tapes 2 a)).reindex
        zPlace = bank f g h px pz pt := by
  unfold Tapes.reindex Tapes.append bank zPlace
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem skipX_hoare (f g h : ℤ → Fin (a + 4)) (px pz pt : ℤ) :
    HoareTime (skipX a) (fun v => v = bank f g h px pz pt)
      (fun v => v = bank f g h (px + 1) pz pt) 1 := by
  have := hoare_extend_eq (StepRight.step_hoare (a := a) f px)
    (⟨fun i => if i = 0 then pz else pt, fun i => if i = 0 then g else h⟩ : Tapes 2 a)
  rwa [x_bank, x_bank] at this

theorem zeroT_hoare (f g h : ℤ → Fin (a + 4)) (px pz pt : ℤ) :
    HoareTime (zeroT a) (fun v => v = bank f g h px pz pt)
      (fun v => v = bank f g (Function.update h pt (bitSymbol false)) px pz (pt + 1)) 1 := by
  have := hoare_place (WriteZero.write_hoare (a := a) h pt) tPlace
    (⟨fun i => if i = 0 then px else pz, fun i => if i = 0 then f else g⟩ : Tapes 2 a)
  simp only [WriteZero.cfg, Config.tapes] at this
  rwa [t_bank, t_bank] at this

theorem stepZ_hoare (f g h : ℤ → Fin (a + 4)) (px pz pt : ℤ) :
    HoareTime (stepZ a) (fun v => v = bank f g h px pz pt)
      (fun v => v = bank f g h px (pz + 1) pt) 1 := by
  have := hoare_place (StepRight.step_hoare (a := a) g pz) zPlace
    (⟨fun i => if i = 0 then px else pt, fun i => if i = 0 then f else h⟩ : Tapes 2 a)
  simp only [StepRight.cfg, Config.tapes] at this
  rwa [z_bank, z_bank] at this

/-- Appending one symbol to a placed word. -/
theorem putWord_snoc (h : ℤ → Fin (a + 4)) (pt : ℤ) (w : List (Fin (a + 4))) (x : Fin (a + 4)) :
    Function.update (putWord h pt w) (pt + w.length) x = putWord h pt (w ++ [x]) := by
  have := putWord_append_forward h pt w [x]
  rw [← this]
  simp [putWord]

/-- One digit of the gadget. -/
def digit (op : Bool → Bool → Bool) (S : Shape) (a : ℕ) :
    Program 3 (iterStates 2 S.ox + iterStates 2 S.ot + iterStates 2 S.d +
      iterStates 2 (S.st - S.ot - S.d) + iterStates 2 (S.sx - S.ox - S.d) + 2) a :=
  seq (seq (seq (seq (seq (iterate (skipX a) S.ox) (iterate (zeroT a) S.ot))
    (iterate (opCell op a) S.d)) (iterate (zeroT a) (S.st - S.ot - S.d)))
    (iterate (skipX a) (S.sx - S.ox - S.d))) (stepZ a)

/-- The whole gadget over `n` digits. -/
def program (op : Bool → Bool → Bool) (S : Shape) (n : ℕ) (a : ℕ) :=
  iterate (digit op S a) n

variable (op : Bool → Bool → Bool) (S : Shape) (xs zs : List Bool) (f g h : ℤ → Fin (a + 4))
  (px pz pt : ℤ)

/-- The bank after `i` digits. -/
def state (i : ℕ) : Tapes 3 a :=
  bank (putWord f px (xs.map bitSymbol)) (putWord g pz (zs.map bitSymbol))
    (putWord h pt ((gather op S xs zs i).map bitSymbol))
    (px + i * S.sx) (pz + i) (pt + i * S.st)

/-- Writing `j` zeros extends the target word. -/
theorem zeros_hoare (w : List Bool) (q r : ℤ) (j : ℕ) :
    HoareTime (iterate (zeroT a) j)
      (fun v => v = bank (putWord f px (xs.map bitSymbol)) (putWord g pz (zs.map bitSymbol))
        (putWord h pt (w.map bitSymbol)) q r (pt + w.length))
      (fun v => v = bank (putWord f px (xs.map bitSymbol)) (putWord g pz (zs.map bitSymbol))
        (putWord h pt ((w ++ List.replicate j false).map bitSymbol)) q r (pt + w.length + j))
      (j * (1 + 1)) := by
  have := iterate_hoare (zeroT a) j (fun i => bank (putWord f px (xs.map bitSymbol))
    (putWord g pz (zs.map bitSymbol)) (putWord h pt ((w ++ List.replicate i false).map bitSymbol))
    q r (pt + w.length + i)) 1 (fun i hi => by
      have hz := zeroT_hoare (putWord f px (xs.map bitSymbol)) (putWord g pz (zs.map bitSymbol))
        (putWord h pt ((w ++ List.replicate i false).map bitSymbol)) q r (pt + w.length + i)
      refine hz.consequence (fun v hv => hv) (fun v hv => ?_) le_rfl
      rw [hv]
      have hl : pt + (w.length : ℤ) + i =
          pt + ((w ++ List.replicate i false).map (bitSymbol (a := a))).length := by
        simp only [List.length_map, List.length_append, List.length_replicate]; push_cast; ring
      rw [hl, putWord_snoc, show [bitSymbol (a := a) false] = [false].map bitSymbol from rfl,
        ← List.map_append (f := bitSymbol (a := a)), List.append_assoc,
        show List.replicate i false ++ [false] = List.replicate (i + 1) false by
          simp [List.replicate_succ']]
      congr 1
      all_goals first | rfl | (simp only [List.length_map, List.length_append, List.length_replicate]; push_cast; ring))
  simpa using this

/-- Skipping `j` source cells. -/
theorem skips_hoare (T : ℤ → Fin (a + 4)) (q r u : ℤ) (j : ℕ) :
    HoareTime (iterate (skipX a) j)
      (fun v => v = bank (putWord f px (xs.map bitSymbol)) (putWord g pz (zs.map bitSymbol)) T q r u)
      (fun v => v = bank (putWord f px (xs.map bitSymbol)) (putWord g pz (zs.map bitSymbol)) T (q + j) r u)
      (j * (1 + 1)) := by
  have := iterate_hoare (skipX a) j (fun i => bank (putWord f px (xs.map bitSymbol))
    (putWord g pz (zs.map bitSymbol)) T (q + i) r u) 1 (fun i hi => by
      refine (skipX_hoare _ _ _ _ _ _).consequence (fun v hv => hv) (fun v hv => ?_) le_rfl
      rw [hv]; congr 1; push_cast; ring)
  simpa using this

/-- Combining `j` field bits. -/
theorem ops_hoare (w : List Bool) (i : ℕ) (hi : i < zs.length)
    (start : ℕ) (j : ℕ) (hj : start + j ≤ xs.length) :
    HoareTime (iterate (opCell op a) j)
      (fun v => v = bank (putWord f px (xs.map bitSymbol)) (putWord g pz (zs.map bitSymbol))
        (putWord h pt (w.map bitSymbol)) (px + start) (pz + i) (pt + w.length))
      (fun v => v = bank (putWord f px (xs.map bitSymbol)) (putWord g pz (zs.map bitSymbol))
        (putWord h pt ((w ++ (field xs start j).map (fun x => op x (zs.getD i false))).map bitSymbol))
        (px + start + j) (pz + i) (pt + w.length + j))
      (j * (1 + 1)) := by
  have := iterate_hoare (opCell op a) j (fun k => bank (putWord f px (xs.map bitSymbol))
    (putWord g pz (zs.map bitSymbol))
    (putWord h pt ((w ++ (field xs start k).map (fun x => op x (zs.getD i false))).map bitSymbol))
    (px + start + k) (pz + i) (pt + w.length + k)) 1 (fun k hk => by
      have hc := opCell_hoare op (putWord f px (xs.map bitSymbol)) (putWord g pz (zs.map bitSymbol))
        (putWord h pt ((w ++ (field xs start k).map (fun x => op x (zs.getD i false))).map bitSymbol))
        (px + start + k) (pz + i) (pt + w.length + k) (xs.getD (start + k) false) (zs.getD i false)
        (by rw [show px + (start : ℤ) + k = px + ((start + k : ℕ) : ℤ) by push_cast; ring,
          putWord_getD _ _ _ _ (by omega)])
        (by rw [putWord_getD _ _ _ _ hi])
      refine hc.consequence (fun v hv => hv) (fun v hv => ?_) le_rfl
      rw [hv]
      have hl : pt + (w.length : ℤ) + k =
          pt + ((w ++ (field xs start k).map (fun x => op x (zs.getD i false))).map
            (bitSymbol (a := a))).length := by
        simp only [List.length_map, List.length_append, field_length]; push_cast; ring
      rw [hl, putWord_snoc,
        show [bitSymbol (a := a) (op (xs.getD (start + k) false) (zs.getD i false))] =
          [op (xs.getD (start + k) false) (zs.getD i false)].map bitSymbol from rfl,
        ← List.map_append (f := bitSymbol (a := a))]
      simp only [field_succ, List.map_append, List.map_singleton, List.append_assoc]
      congr 1
      all_goals first | rfl | ((try simp only [List.length_map, List.length_append, field_length]); push_cast; ring))
  simpa using this

/-- The cost of one digit. -/
def digitCost (S : Shape) : ℕ :=
  S.ox * (1 + 1) + 1 + S.ot * (1 + 1) + 1 + S.d * (1 + 1) + 1 + (S.st - S.ot - S.d) * (1 + 1) + 1 +
    (S.sx - S.ox - S.d) * (1 + 1) + 1 + 1

theorem digitCost_le (S : Shape) : digitCost S ≤ 2 * (S.sx + S.st) + 6 := by
  have := S.hx; have := S.ht
  unfold digitCost
  omega

/-- One digit carries the bank from `i` digits to `i + 1`. -/
theorem digit_hoare (hxs : zs.length * S.sx ≤ xs.length) (i : ℕ) (hi : i < zs.length) :
    HoareTime (digit op S a) (fun v => v = state op S xs zs f g h px pz pt i)
      (fun v => v = state op S xs zs f g h px pz pt (i + 1)) (digitCost S) := by
  set w := gather op S xs zs i with hw
  have hwl : w.length = i * S.st := gather_length op S xs zs i
  -- skip to the field
  have h1 := skips_hoare xs zs f g px pz (putWord h pt (w.map bitSymbol)) (px + i * S.sx) (pz + i)
    (pt + i * S.st) S.ox
  -- leading zeros
  have h2 := zeros_hoare xs zs f g h px pz pt w (px + i * S.sx + S.ox) (pz + i) S.ot
  -- the field
  have h3 := ops_hoare op xs zs f g h px pz pt (w ++ List.replicate S.ot false) i hi
    (i * S.sx + S.ox) S.d (by have := S.hx; nlinarith)
  rw [show px + ((i * S.sx + S.ox : ℕ) : ℤ) = px + i * S.sx + S.ox by push_cast; ring] at h3
  -- trailing zeros
  have h4 := zeros_hoare xs zs f g h px pz pt
    (w ++ List.replicate S.ot false ++ (field xs (i * S.sx + S.ox) S.d).map (fun x => op x (zs.getD i false)))
    (px + i * S.sx + S.ox + S.d) (pz + i) (S.st - S.ot - S.d)
  -- skip the rest of the source digit
  have h5 := skips_hoare xs zs f g px pz
    (putWord h pt ((w ++ List.replicate S.ot false ++
      (field xs (i * S.sx + S.ox) S.d).map (fun x => op x (zs.getD i false)) ++
      List.replicate (S.st - S.ot - S.d) false).map bitSymbol))
    (px + i * S.sx + S.ox + S.d) (pz + i) (pt + i * S.st + S.st) (S.sx - S.ox - S.d)
  -- advance the control
  have h6 := stepZ_hoare (putWord f px (xs.map bitSymbol)) (putWord g pz (zs.map bitSymbol))
    (putWord h pt ((w ++ List.replicate S.ot false ++
      (field xs (i * S.sx + S.ox) S.d).map (fun x => op x (zs.getD i false)) ++
      List.replicate (S.st - S.ot - S.d) false).map bitSymbol))
    (px + i * S.sx + S.ox + S.d + ((S.sx - S.ox - S.d : ℕ) : ℤ)) (pz + i) (pt + i * S.st + S.st)
  -- align the intermediate banks
  have e2 : pt + (i : ℤ) * S.st = pt + (w.length : ℤ) := by rw [hwl]; push_cast; ring
  have e3 : pt + (w.length : ℤ) + S.ot = pt + ((w ++ List.replicate S.ot false).length : ℤ) := by
    simp only [List.length_append, List.length_replicate]; push_cast; ring
  have e4 : pt + ((w ++ List.replicate S.ot false).length : ℤ) + S.d =
      pt + ((w ++ List.replicate S.ot false ++
        (field xs (i * S.sx + S.ox) S.d).map (fun x => op x (zs.getD i false))).length : ℤ) := by
    simp only [List.length_append, List.length_replicate, List.length_map, field_length]; push_cast; ring
  have e5 : pt + ((w ++ List.replicate S.ot false ++
      (field xs (i * S.sx + S.ox) S.d).map (fun x => op x (zs.getD i false))).length : ℤ) +
      ((S.st - S.ot - S.d : ℕ) : ℤ) = pt + i * S.st + S.st := by
    have := S.ht
    simp only [List.length_append, List.length_replicate, List.length_map, field_length, hwl]
    push_cast [show S.d ≤ S.st - S.ot by omega, show S.ot ≤ S.st by omega]
    ring
  rw [e2] at h1
  rw [e3] at h2
  rw [e4] at h3
  rw [e5] at h4
  have hpre : state op S xs zs f g h px pz pt i =
      bank (putWord f px (xs.map bitSymbol)) (putWord g pz (zs.map bitSymbol))
        (putWord h pt (w.map bitSymbol)) (px + i * S.sx) (pz + i) (pt + w.length) := by
    rw [state, hw, hwl]; push_cast; rfl
  have hpost : state op S xs zs f g h px pz pt (i + 1) =
      bank (putWord f px (xs.map bitSymbol)) (putWord g pz (zs.map bitSymbol))
        (putWord h pt ((w ++ List.replicate S.ot false ++
          (field xs (i * S.sx + S.ox) S.d).map (fun x => op x (zs.getD i false)) ++
          List.replicate (S.st - S.ot - S.d) false).map bitSymbol))
        (px + i * S.sx + S.ox + S.d + ((S.sx - S.ox - S.d : ℕ) : ℤ)) (pz + i + 1)
        (pt + i * S.st + S.st) := by
    have := S.hx
    rw [state, gather, digitWord, hw]
    congr 1
    all_goals first | (simp only [List.append_assoc]) | (push_cast [show S.d ≤ S.sx - S.ox by omega, show S.ox ≤ S.sx by omega]; ring)
  rw [hpre, hpost]
  have hall := ((((h1.seq h2).seq h3).seq h4).seq h5).seq h6
  refine hall.consequence (fun v hv => hv) (fun v hv => hv) ?_
  unfold digitCost
  omega

/-- The gadget's contract: the target word is the gathered packing; every
head advances past its word. -/
theorem gather_hoare (hxs : zs.length * S.sx ≤ xs.length) :
    HoareTime (program op S zs.length a)
      (fun v => v = bank (putWord f px (xs.map bitSymbol)) (putWord g pz (zs.map bitSymbol)) h px pz pt)
      (fun v => v = bank (putWord f px (xs.map bitSymbol)) (putWord g pz (zs.map bitSymbol))
        (putWord h pt ((gather op S xs zs zs.length).map bitSymbol))
        (px + zs.length * S.sx) (pz + zs.length) (pt + zs.length * S.st))
      (zs.length * (digitCost S + 1)) := by
  have hit := iterate_hoare (digit op S a) zs.length (state op S xs zs f g h px pz pt) (digitCost S)
    (fun i hi => digit_hoare op S xs zs f g h px pz pt hxs i hi)
  have h0 : state op S xs zs f g h px pz pt 0 =
      bank (putWord f px (xs.map bitSymbol)) (putWord g pz (zs.map bitSymbol)) h px pz pt := by
    simp [state, gather, putWord]
  have hn : state op S xs zs f g h px pz pt zs.length =
      bank (putWord f px (xs.map bitSymbol)) (putWord g pz (zs.map bitSymbol))
        (putWord h pt ((gather op S xs zs zs.length).map bitSymbol))
        (px + zs.length * S.sx) (pz + zs.length) (pt + zs.length * S.st) := by
    simp [state]
  rw [h0, hn] at hit
  exact hit

end Machine

end IntegerMultBounds.Machine.Gather
