import IntegerMultBounds.Machine.CountedGatherDigit

/-! A uniform packed gather: both strides, field offsets and digit count are
runtime descriptors. Neither the state count nor the transition table depends
on the shape or the number of digits. All independent clocks are restored. -/
namespace IntegerMultBounds.Machine.CountedGatherRun
noncomputable section
variable {a : ℕ}

def program (op : Bool → Bool → Bool) (a : ℕ) : Program 11 108 a :=
  CountedLoopReuseAlphabet.program (CountedGatherDigit.program op a)

def state (op : Bool → Bool → Bool) (S : Gather.Shape) (xs zs : List Bool)
    (f g h : ℤ → Fin (a+4)) (px pz pt : ℤ) (hs : Fin 5 → List Bool) (i : ℕ) : Tapes 9 a :=
  CountedGatherDigit.bank (Gather.bank (putWord f px (xs.map bitSymbol))
    (putWord g pz (zs.map bitSymbol))
    (putWord h pt ((Gather.gather op S xs zs i).map bitSymbol))
    (px+i*S.sx) (pz+i) (pt+i*S.st)) hs

def bank (v : Tapes 9 a) (ns : List Bool) : Tapes 11 a :=
  CountedLoopReuseAlphabet.bank v CountedLoopReuseAlphabet.empty
    (CountedLoopReuseAlphabet.binary ns) 1 1

def cost (S : Gather.Shape) (hs : Fin 5 → List Bool) (n : ℕ) (ns : List Bool) : ℕ :=
  n*(CountedGatherDigit.cost S hs+6)+7*ns.length+16

theorem gather_hoare (op : Bool → Bool → Bool) (S : Gather.Shape) (xs zs : List Bool)
    (f g h : ℤ → Fin (a+4)) (px pz pt : ℤ) (hs : Fin 5 → List Bool) (ns : List Bool)
    (hxs : zs.length*S.sx ≤ xs.length)
    (hv : ∀ j, Counter.value (hs j) = CountedGatherDigit.counts S j)
    (hn : Counter.value ns = zs.length) :
    HoareTime (program op a)
      (fun z => z = bank (state op S xs zs f g h px pz pt hs 0) ns)
      (fun z => z = bank (state op S xs zs f g h px pz pt hs zs.length) ns)
      (cost S hs zs.length ns) := by
  have hbody (i : ℕ) (hi : i < zs.length) :
      HoareTime (CountedGatherDigit.program op a)
        (fun z => z = state op S xs zs f g h px pz pt hs i)
        (fun z => z = state op S xs zs f g h px pz pt hs (i+1))
        (CountedGatherDigit.cost S hs) := by
    have hh := CountedGatherDigit.digit_hoare op S xs zs f
      (putWord g pz (zs.map bitSymbol))
      (putWord h pt ((Gather.gather op S xs zs i).map bitSymbol))
      px (pz+i) (pt+i*S.st) i hs
      ((Nat.mul_le_mul_right S.sx (by omega : i+1 ≤ zs.length)).trans hxs)
      (Gather.putWord_getD g pz zs i hi) hv
    have ht : pt+(i*S.st : ℕ) =
        pt+((Gather.gather op S xs zs i).map (bitSymbol (a := a))).length := by
      simp only [List.length_map,Gather.gather_length]
    have he : putWord (putWord h pt ((Gather.gather op S xs zs i).map bitSymbol))
        (pt+i*S.st) ((Gather.digitWord op S xs zs i).map bitSymbol) =
        putWord h pt ((Gather.gather op S xs zs (i+1)).map bitSymbol) := by
      rw [show pt+(i : ℤ)*S.st = pt+((i*S.st : ℕ) : ℤ) by push_cast; ring,ht,
        putWord_append_forward]
      simp only [Gather.gather,List.map_append]
    apply hh.consequence (fun _ h => h) _ le_rfl
    rintro z rfl
    rw [he]
    unfold state
    congr 1
    congr 1 <;> first | rfl | (push_cast; ring)
  have hh := CountedLoopReuseAlphabet.loop_hoare (CountedGatherDigit.program op a) ns
    zs.length (state op S xs zs f g h px pz pt hs) (fun _ => CountedGatherDigit.cost S hs)
    hn hbody
  apply hh.consequence (fun _ h => h) (fun _ h => h) _
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,cost,Nat.mul_add]
  omega

theorem cost_linear (S : Gather.Shape) (hs : Fin 5 → List Bool) (n : ℕ) (ns : List Bool)
    (hv : ∀ j, Counter.value (hs j) = CountedGatherDigit.counts S j)
    (hc : ∀ j, GrowingCounterData.Canonical (hs j))
    (hn : Counter.value ns = n) (cn : GrowingCounterData.Canonical ns) :
    cost S hs n ns ≤ 134*(n*(S.sx+S.st+1))+23 := by
  have hd := CountedGatherDigit.cost_linear S hs hv hc
  have hw := GrowingCounterData.canonical_width ns cn
  have hl := Nat.log2_le_self (Counter.value ns)
  rw [hn] at hw hl
  have hm := Nat.mul_le_mul_left n hd
  unfold cost
  nlinarith

/-- The complete fixed gather has literal source/control words and the exact
gathered target, with all eight binary control tapes restored. -/
theorem runs (op : Bool → Bool → Bool) (S : Gather.Shape) (xs zs : List Bool)
    (f g h : ℤ → Fin (a+4)) (px pz pt : ℤ) (hs : Fin 5 → List Bool) (ns : List Bool)
    (hxs : zs.length*S.sx ≤ xs.length)
    (hv : ∀ j, Counter.value (hs j) = CountedGatherDigit.counts S j)
    (hc : ∀ j, GrowingCounterData.Canonical (hs j))
    (hn : Counter.value ns = zs.length) (cn : GrowingCounterData.Canonical ns) :
    HoareTime (program op a)
      (fun z => z = bank (CountedGatherDigit.bank
        (Gather.bank (putWord f px (xs.map bitSymbol)) (putWord g pz (zs.map bitSymbol))
          h px pz pt) hs) ns)
      (fun z => z = bank (CountedGatherDigit.bank
        (Gather.bank (putWord f px (xs.map bitSymbol)) (putWord g pz (zs.map bitSymbol))
          (putWord h pt ((Gather.gather op S xs zs zs.length).map bitSymbol))
          (px+zs.length*S.sx) (pz+zs.length) (pt+zs.length*S.st)) hs) ns)
      (134*(zs.length*(S.sx+S.st+1))+23) := by
  have hh := (gather_hoare op S xs zs f g h px pz pt hs ns hxs hv hn).consequence
    (fun _ h => h) (fun _ h => h) (cost_linear S hs zs.length ns hv hc hn cn)
  simpa only [state,Gather.gather,List.map_nil,putWord,Nat.cast_zero,zero_mul,add_zero] using hh

end
end IntegerMultBounds.Machine.CountedGatherRun
