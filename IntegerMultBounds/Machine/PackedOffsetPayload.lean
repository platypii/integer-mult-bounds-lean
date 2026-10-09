import IntegerMultBounds.Machine.PackedOffsetStreamRaw
import IntegerMultBounds.Machine.StreamedFiberTranslationReusable
import IntegerMultBounds.Machine.MarkedControlStreamReset

/-! Physical packed-offset payload rotation, including synthesis and erasure
of its control stream. Original w/B/Q/n headers and both source heads survive;
all private storage starts and finishes wholly blank. -/
namespace IntegerMultBounds.Machine.PackedOffsetPayload
noncomputable section
open MarkedWordCleanup (one empty marked)
open SharedPlacementAlphabet (setTape)
open CountedCopyReuse (binary)

def tail (ws : List Bool) (offsets : ℤ → Fin 4) (s : ℤ) : Tapes 2 0 :=
  ⟨![1,s],![binary ws,offsets]⟩

def bank (payload control offsets : ℤ → Fin 4) (p r s : ℤ) (bs qs ns ws : List Bool) : Tapes 17 0 :=
  (StreamedFiberTranslationInitialized.bare payload (fun _ => blank) control p 0 r bs qs ns).append
    (tail ws offsets s)

def atSlot {k : ℕ} (M : Program 1 k 0) (slot : Fin 17) :=
  Placement.placed M (FiniteReturnStackAt.placement slot)

theorem at_hoare {k cost : ℕ} (M : Program 1 k 0) (slot : Fin 17) (v : Tapes 17 0)
    (f g : ℤ → Fin 4) (p q : ℤ)
    (h : HoareTime M (fun z => z=one f p) (fun z => z=one g q) cost)
    (ht : v.tape slot=f) (hh : v.head slot=p) :
    HoareTime (atSlot M slot) (fun z => z=v) (fun z => z=setTape v slot g q) cost := by
  have ha : Placement.active (FiniteReturnStackAt.placement slot) v = one f p := by
    rw [FiniteReturnStackAt.active_bank,ht,hh]
    rfl
  have he := Placement.hoare_at h (FiniteReturnStackAt.placement slot) v ha
  apply he.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨v,rfl,rfl⟩
  exact FiniteReturnStackAt.replace_bank _ _ _ _

theorem set_control (payload control offsets control' : ℤ → Fin 4) (p r s r' : ℤ) (bs qs ns ws : List Bool) :
    setTape (bank payload control offsets p r s bs qs ns ws) 12 control' r' =
      bank payload control' offsets p r' s bs qs ns ws := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem set_offsets (payload control offsets offsets' : ℤ → Fin 4) (p r s s' : ℤ) (bs qs ns ws : List Bool) :
    setTape (bank payload control offsets p r s bs qs ns ws) 16 offsets' s' =
      bank payload control offsets' p r s' bs qs ns ws := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def generatorPlacement : Fin (7+10) ≃ Fin 17 where
  toFun := ![16,0,1,15,12,2,14,3,4,5,6,7,8,9,10,11,13]
  invFun := ![1,2,5,7,8,9,10,11,12,13,14,15,4,16,6,3,0]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def generator := Placement.placed PackedOffsetStream.program generatorPlacement

theorem generates (V : List Bool) (w n : ℕ) (hV : V.length=n*w)
    (payload control f : ℤ → Fin 4) (p r s : ℤ) (bs qs ns ws : List Bool)
    (hw : Counter.value ws=w) (hn : Counter.value ns=n)
    (cw : GrowingCounterData.Canonical ws) (cn : GrowingCounterData.Canonical ns) :
    HoareTime generator
      (fun z => z=bank payload control (putWord f s (V.map bitSymbol)) p r s bs qs ns ws)
      (fun z => z=bank payload (putWord control r (PackedOffsetStreamRaw.output V w n))
        (putWord f s (V.map bitSymbol)) p (r+(PackedOffsetStreamRaw.output V w n).length)
        (s+((n*w : ℕ) : ℤ)) bs qs ns ws) (66*(n*(w+1))+28) := by
  have ha : Placement.active generatorPlacement
      (bank payload control (putWord f s (V.map bitSymbol)) p r s bs qs ns ws) =
      PackedOffsetStream.input (putWord f s (V.map bitSymbol)) control s r ws ns := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hh := Placement.hoare_at (PackedOffsetStreamRaw.runs V w n hV f control s r ws ns hw hn cw cn)
    generatorPlacement _ ha
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨v,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def view (V : List Bool) (w n B : ℕ) (a : Fin (n*(2^w*B)) → Bool) :
    Fin ((PackedOffsetStreamRaw.words V w n).length*(2^w*B)) → Bool :=
  fun i => a (Fin.cast (congrArg (fun k => k*(2^w*B)) (PackedOffsetStreamRaw.words_length V w n)) i)

theorem view_word (V : List Bool) (w n B : ℕ) (a : Fin (n*(2^w*B)) → Bool) :
    List.ofFn (fun i => (bitSymbol (view V w n B a i) : Fin 4)) = List.ofFn (fun i => bitSymbol (a i)) := by
  have he {n m : ℕ} (h : n=m) (f : Fin m → Fin 4) : List.ofFn (fun i => f (Fin.cast h i))=List.ofFn f := by
    subst m; rfl
  exact he (congrArg (fun k => k*(2^w*B)) (PackedOffsetStreamRaw.words_length V w n))
    (fun i => bitSymbol (a i))

def result (V : List Bool) (w n B : ℕ) (a : Fin (n*(2^w*B)) → Bool) : List (Fin 4) :=
  FiberLayoutData.translated (fun i => bitSymbol (view V w n B a i))
    (fun i => StreamedFiberTranslation.offset (PackedOffsetStreamRaw.words V w n) i.val)

theorem stream_no_separator (V : List Bool) (w n : ℕ) :
    ∀ x ∈ PackedOffsetStreamRaw.output V w n, x ≠ (separator : Fin 4) := by
  intro x hx
  obtain ⟨word,hw,hx⟩ := List.mem_flatten.mp hx
  obtain ⟨xs,_,rfl⟩ := List.mem_map.mp hw
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
    cases b <;> decide
  · have he := List.mem_singleton.mp hx
    rw [he]
    decide

theorem rotates (V : List Bool) (w n B : ℕ) (hV : V.length=n*w) (hB : 0 < B)
    (f offsets : ℤ → Fin 4) (p s : ℤ) (hf : f (p-1)=blank) (bs qs ns ws : List Bool)
    (hb : Counter.value bs=B) (hq : Counter.value qs=2^w) (hn : Counter.value ns=n)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns) (a : Fin (n*(2^w*B)) → Bool) :
    HoareTime (extend StreamedFiberTranslationReusable.program 2)
      (fun z => z=bank (putWord f p (List.ofFn (fun i => bitSymbol (a i))))
        (marked (PackedOffsetStreamRaw.output V w n)) offsets p 1 s bs qs ns ws)
      (fun z => z=bank (putWord f p (result V w n B a)) (marked (PackedOffsetStreamRaw.output V w n))
        offsets p (1+(PackedOffsetStreamRaw.output V w n).length) s bs qs ns ws)
      (500*(n*(2^w*B))+70) := by
  have hh := StreamedFiberTranslationReusable.runs (PackedOffsetStreamRaw.words V w n) (2^w) B
    (by positivity) hB f empty p 1 hf bs qs ns hb hq
    (by simpa only [PackedOffsetStreamRaw.words_length] using hn) cb cq cn
    (PackedOffsetStreamRaw.words_canonical V w n)
    (fun xs hx => (PackedOffsetStreamRaw.words_bounded V w n hV xs hx).le) (view V w n B a)
  rw [view_word] at hh
  have he := hoare_extend_eq hh (tail ws offsets s)
  simp only [PackedOffsetStreamRaw.words_length] at he
  simpa only [bank,result,marked,PackedOffsetStreamRaw.output,
    PackedOffsetStream.output,PackedOffsetStreamRaw.words] using he

def program : Program 17 331 0 := seq (seq (seq (seq (seq
  (atSlot MarkedWordCleanup.markProgram 12) generator)
  (atSlot MarkedControlStreamReset.rewind 12)) (extend StreamedFiberTranslationReusable.program 2))
  (atSlot MarkedControlStreamReset.program 12)) (atSlot ReturnOrigin.program 16)

/-- Generate controls from the packed word, execute all physical payload
rotations, erase the control stream, and restore the packed-source head.
Every original header and both tape exteriors survive. -/
theorem runs (V : List Bool) (w n B : ℕ) (hV : V.length=n*w) (hB : 0 < B)
    (f g : ℤ → Fin 4) (p s : ℤ) (hf : f (p-1)=blank) (hg : g (s-1)=blank)
    (bs qs ns ws : List Bool) (hb : Counter.value bs=B) (hq : Counter.value qs=2^w)
    (hn : Counter.value ns=n) (hw : Counter.value ws=w)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns) (cw : GrowingCounterData.Canonical ws)
    (a : Fin (n*(2^w*B)) → Bool) :
    HoareTime program
      (fun z => z=bank (putWord f p (List.ofFn (fun i => bitSymbol (a i))))
        (fun _ => blank) (putWord g s (V.map bitSymbol)) p 0 s bs qs ns ws)
      (fun z => z=bank (putWord f p (result V w n B a)) (fun _ => blank)
        (putWord g s (V.map bitSymbol)) p 0 s bs qs ns ws)
      (600*(n*(2^w*B))+150) := by
  let X := putWord f p (List.ofFn (fun i => (bitSymbol (a i) : Fin 4)))
  let Y := putWord f p (result V w n B a)
  let O := putWord g s (V.map bitSymbol)
  let C := PackedOffsetStreamRaw.output V w n
  let s' : ℤ := s+((n*w : ℕ) : ℤ)
  have h₀ := at_hoare MarkedWordCleanup.markProgram 12 (bank X (fun _ => blank) O p 0 s bs qs ns ws)
    _ _ _ _ (MarkedWordCleanup.mark_hoare ([] : List (Fin 4))) rfl rfl
  rw [set_control] at h₀
  have h₁ := generates V w n hV X empty g p 1 s bs qs ns ws hw hn cw cn
  have h₂ := at_hoare MarkedControlStreamReset.rewind 12 (bank X (marked C) O p (1+C.length) s' bs qs ns ws)
    _ _ _ _ (MarkedControlStreamReset.rewinds C (stream_no_separator V w n)) rfl rfl
  rw [set_control] at h₂
  have h₃ := rotates V w n B hV hB f O p s' hf bs qs ns ws hb hq hn cb cq cn a
  have h₄ := at_hoare MarkedControlStreamReset.program 12 (bank Y (marked C) O p (1+C.length) s' bs qs ns ws)
    _ _ _ _ (MarkedControlStreamReset.resets C (stream_no_separator V w n)) rfl rfl
  rw [set_control] at h₄
  have hnb : ∀ x ∈ V.map bitSymbol, x ≠ (blank : Fin 4) := by
    intro x hx
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
    cases b <;> decide
  have h₅ := at_hoare ReturnOrigin.program 16 (bank Y (fun _ => blank) O p 0 s' bs qs ns ws)
    _ _ _ _ (ReturnOrigin.return_hoare_at g s (V.map bitSymbol) hnb hg) rfl
    (by change s'=s+(V.map bitSymbol).length; simp only [List.length_map,hV]; rfl)
  rw [set_offsets,List.length_map,hV] at h₅
  have hl := PackedOffsetStreamRaw.output_length V w n hV
  have hw2 : w+1 ≤ 2^w := Nat.lt_two_pow_self
  have hNB : n*(w+1) ≤ n*(2^w*B) := Nat.mul_le_mul_left n
    (hw2.trans (Nat.le_mul_of_pos_right _ hB))
  have hNw : n*w ≤ n*(w+1) := Nat.mul_le_mul_left n (by omega)
  exact (((((h₀.seq h₁).seq h₂).seq h₃).seq h₄).seq h₅).consequence
    (fun _ h => h) (fun _ h => h) (by dsimp only [C]; omega)

end
end IntegerMultBounds.Machine.PackedOffsetPayload
