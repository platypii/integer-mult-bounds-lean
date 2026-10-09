import IntegerMultBounds.Machine.PackedLine
import IntegerMultBounds.Machine.CountedGatherRun

/-! Uniform thirteen-tape packed line. Shape and digit count are supplied on
runtime binary descriptors, all of which are retained across the actual gather,
column transduction, offset erasure and physical head rewinds. -/
namespace IntegerMultBounds.Machine.CountedPackedLine
noncomputable section
variable {a : ℕ}
open PackedLine
open ColumnTransducer (Rule)

def controls (hs : Fin 5 → List Bool) (ns : List Bool) : Tapes 8 a :=
  (CountedGatherDigit.descriptors hs).append (CountedLoopReuseAlphabet.controls
    CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1)
def bank (v : Tapes 5 a) (hs : Fin 5 → List Bool) (ns : List Bool) := v.append (controls hs ns)

def placement : Fin (11+2) ≃ Fin 13 where
  toFun := fun i => if h : i.val < 3 then ⟨i.val,by omega⟩ else
    if h' : i.val < 11 then ⟨i.val+2,by omega⟩ else ⟨i.val-8,by omega⟩
  invFun := fun i => if h : i.val < 3 then ⟨i.val,by omega⟩ else
    if h' : i.val < 5 then ⟨i.val+8,by omega⟩ else ⟨i.val-2,by omega⟩
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem gather_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a+4))
    (p0 p1 p2 p3 p4 : ℤ) (hs : Fin 5 → List Bool) (ns : List Bool) :
    ((CountedGatherRun.bank (CountedGatherDigit.bank (Gather.bank f0 f1 f2 p0 p1 p2) hs) ns).append
      (⟨fun i => if i = 0 then p3 else p4,fun i => if i = 0 then f3 else f4⟩ : Tapes 2 a)).reindex placement =
      bank (PackedLine.bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4) hs ns := by
  unfold bank controls CountedGatherRun.bank CountedGatherDigit.bank CountedGatherDigit.descriptors
    CountedLoopReuseAlphabet.bank CountedLoopReuseAlphabet.controls Tapes.reindex Tapes.append
    Gather.bank PackedLine.bank placement
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def gatherPart (op : Bool → Bool → Bool) (a : ℕ) :=
  reindex (extend (CountedGatherRun.program op a) 2) placement
def finish {s : ℕ} (R : Rule s) (a : ℕ) :=
  seq (seq (seq (seq (seq (seq (PackedLine.ret0 a) (ret1 a)) (ret2 a))
    (transPart R a)) (erase2 a)) (ret3 a)) (ret4 a)
def program (op : Bool → Bool → Bool) {s : ℕ} (R : Rule s) (a : ℕ) :=
  seq (gatherPart op a) (extend (finish R a) 8)
def finishCost (S : Gather.Shape) (n m : ℕ) :=
  (n*S.sx+2)+1+(n+2)+1+(n*S.st+2)+1+m+1+(n*S.st+2)+1+(m+2)+1+(m+2)
def cost (S : Gather.Shape) (hs : Fin 5 → List Bool) (n m : ℕ) (ns : List Bool) :=
  CountedGatherRun.cost S hs n ns+1+finishCost S n m

variable (op : Bool → Bool → Bool) (S : Gather.Shape) {s : ℕ} (R : Rule s) (xs zs acc : List Bool)
  (f g h : ℤ → Fin (a+4)) (p0 p1 p2 p3 p4 : ℤ)

theorem finish_hoare (hxs : zs.length*S.sx ≤ xs.length) (hacc : acc.length = zs.length*S.st)
    (hf : f (p0-1) = blank) (hg : g (p1-1) = blank) (hh : h (p3-1) = blank)
    (hh' : h (p3+acc.length) = blank) :
    HoareTime (finish R a)
      (fun v => v = PackedLine.bank (putWord f p0 (xs.map bitSymbol)) (putWord g p1 (zs.map bitSymbol))
        (putWord (fun _ => blank) p2 ((Gather.gather op S xs zs zs.length).map bitSymbol))
        (putWord h p3 (acc.map bitSymbol)) (fun _ => blank)
        (p0+zs.length*S.sx) (p1+zs.length) (p2+zs.length*S.st) p3 p4)
      (fun v => v = PackedLine.bank (putWord f p0 (xs.map bitSymbol)) (putWord g p1 (zs.map bitSymbol))
        (fun _ => blank) (putWord h p3 (acc.map bitSymbol))
        (putWord (fun _ => blank) p4
          ((ColumnTransducer.digits R 0 (acc.zip (Gather.gather op S xs zs zs.length))).map bitSymbol))
        p0 p1 p2 p3 p4)
      (finishCost S zs.length acc.length) := by
  set n := zs.length with hn
  set G := Gather.gather op S xs zs n with hG
  set D := ColumnTransducer.digits R 0 (acc.zip G) with hD
  have hGl : G.length = n*S.st := Gather.gather_length op S xs zs n
  have hDl : D.length = acc.length := by
    rw [hD,ColumnTransducer.digits_length,List.length_zip,hGl,hacc,min_self]
  have hlen : acc.length = G.length := by rw [hGl,hacc]
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
  have hall := (((((h2.seq h3).seq h4).seq h5).seq h6).seq h7).seq h8
  refine hall.consequence (fun _ h => h) (fun _ h => h) ?_
  unfold finishCost
  omega

/-- A literal line with runtime shape/count descriptors and restored controls. -/
theorem line_hoare (hs : Fin 5 → List Bool) (ns : List Bool)
    (hxs : zs.length*S.sx ≤ xs.length) (hacc : acc.length = zs.length*S.st)
    (hv : ∀ j, Counter.value (hs j) = CountedGatherDigit.counts S j)
    (hn : Counter.value ns = zs.length)
    (hf : f (p0-1) = blank) (hg : g (p1-1) = blank) (hh : h (p3-1) = blank)
    (hh' : h (p3+acc.length) = blank) :
    HoareTime (program op R a)
      (fun v => v = bank (PackedLine.bank (putWord f p0 (xs.map bitSymbol))
        (putWord g p1 (zs.map bitSymbol)) (fun _ => blank)
        (putWord h p3 (acc.map bitSymbol)) (fun _ => blank) p0 p1 p2 p3 p4) hs ns)
      (fun v => v = bank (PackedLine.bank (putWord f p0 (xs.map bitSymbol))
        (putWord g p1 (zs.map bitSymbol)) (fun _ => blank)
        (putWord h p3 (acc.map bitSymbol))
        (putWord (fun _ => blank) p4
          ((ColumnTransducer.digits R 0 (acc.zip (Gather.gather op S xs zs zs.length))).map bitSymbol))
        p0 p1 p2 p3 p4) hs ns)
      (cost S hs zs.length acc.length ns) := by
  have hgather := hoare_place (CountedGatherRun.gather_hoare op S xs zs f g (fun _ => blank)
    p0 p1 p2 hs ns hxs hv hn) placement
    (⟨fun i => if i = 0 then p3 else p4,
      fun i => if i = 0 then putWord h p3 (acc.map bitSymbol) else fun _ => blank⟩ : Tapes 2 a)
  simp only [CountedGatherRun.state,Gather.gather,List.map_nil,putWord,Nat.cast_zero,
    zero_mul,add_zero] at hgather
  rw [gather_bank,gather_bank] at hgather
  have hfinish := hoare_extend_eq (finish_hoare op S R xs zs acc f g h p0 p1 p2 p3 p4
    hxs hacc hf hg hh hh') (controls (a := a) hs ns)
  exact hgather.seq hfinish

theorem cost_linear (S : Gather.Shape) (hs : Fin 5 → List Bool) (n m : ℕ) (ns : List Bool)
    (hv : ∀ j, Counter.value (hs j) = CountedGatherDigit.counts S j)
    (hc : ∀ j, GrowingCounterData.Canonical (hs j))
    (hn : Counter.value ns = n) (cn : GrowingCounterData.Canonical ns) :
    cost S hs n m ns ≤ 140*(n*(S.sx+S.st+1))+3*m+42 := by
  have hg := CountedGatherRun.cost_linear S hs n ns hv hc hn cn
  unfold cost finishCost
  nlinarith

/-- Canonical runtime descriptors give a uniform linear bound, including
empty controls, zero-width fields and the zero-digit case. -/
theorem runs (hs : Fin 5 → List Bool) (ns : List Bool)
    (hxs : zs.length*S.sx ≤ xs.length) (hacc : acc.length = zs.length*S.st)
    (hv : ∀ j, Counter.value (hs j) = CountedGatherDigit.counts S j)
    (hc : ∀ j, GrowingCounterData.Canonical (hs j))
    (hn : Counter.value ns = zs.length) (cn : GrowingCounterData.Canonical ns)
    (hf : f (p0-1) = blank) (hg : g (p1-1) = blank) (hh : h (p3-1) = blank)
    (hh' : h (p3+acc.length) = blank) :
    HoareTime (program op R a)
      (fun v => v = bank (PackedLine.bank (putWord f p0 (xs.map bitSymbol))
        (putWord g p1 (zs.map bitSymbol)) (fun _ => blank)
        (putWord h p3 (acc.map bitSymbol)) (fun _ => blank) p0 p1 p2 p3 p4) hs ns)
      (fun v => v = bank (PackedLine.bank (putWord f p0 (xs.map bitSymbol))
        (putWord g p1 (zs.map bitSymbol)) (fun _ => blank)
        (putWord h p3 (acc.map bitSymbol))
        (putWord (fun _ => blank) p4
          ((ColumnTransducer.digits R 0 (acc.zip (Gather.gather op S xs zs zs.length))).map bitSymbol))
        p0 p1 p2 p3 p4) hs ns)
      (140*(zs.length*(S.sx+S.st+1))+3*acc.length+42) :=
  (line_hoare op S R xs zs acc f g h p0 p1 p2 p3 p4 hs ns hxs hacc hv hn hf hg hh hh').consequence
    (fun _ h => h) (fun _ h => h) (cost_linear S hs zs.length acc.length ns hv hc hn cn)

end
end IntegerMultBounds.Machine.CountedPackedLine
