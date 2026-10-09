import IntegerMultBounds.Machine.StreamedFiberTranslationInitialized
import IntegerMultBounds.Machine.StreamedFiberTranslationAlphabet

/-! Complete original-header streamed rotation on the interchange alphabet.
The actual machine physically initializes and erases every private tape. Its
larger-alphabet endpoints are literal banks and arrays, not supplied execution
certificates or prepared marker configurations. -/
namespace IntegerMultBounds.Machine.StreamedFiberTranslationInitializedAlphabet
noncomputable section
variable {a : ℕ}
open StreamedFiberTranslationAlphabet (encoding mapTape)

def bare (source dest control : ℤ → Fin (a+4)) (p q r : ℤ)
    (bs qs ns : List Bool) : Tapes 15 a :=
  ⟨![0,0,0,0,0,1,0,1,0,0,p,q,r,0,1],
   ![fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,
     fun _ => blank,CountedLoopReuseAlphabet.binary bs,fun _ => blank,
     CountedLoopReuseAlphabet.binary qs,fun _ => blank,
     fun _ => blank,source,dest,control,fun _ => blank,CountedLoopReuseAlphabet.binary ns]⟩

def program (a : ℕ) : Program 15 252 a := Alphabet.program (encoding (a := a)) StreamedFiberTranslationInitialized.program

theorem mapped_bare (source dest control : ℤ → Fin 4) (p q r : ℤ) (bs qs ns : List Bool) :
    Alphabet.mapTapes (encoding (a := a))
      (StreamedFiberTranslationInitialized.bare source dest control p q r bs qs ns) =
      bare (mapTape source) (mapTape dest) (mapTape control) p q r bs qs ns := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i
    fin_cases i <;> first | rfl | exact CountedLoopReuseAlphabet.encoding_binary _

private theorem map_word (f : ℤ → Fin 4) (p : ℤ) (xs : List (Fin 4)) :
    mapTape (a := a) (putWord f p xs) =
      putWord (mapTape f) p (xs.map (encoding (a := a)).encode) :=
  RowPaddingConstructedAlphabet.map_putWord f p xs

private theorem map_exact {t s cost : ℕ} {M : Program t s 0} {v w : Tapes t 0}
    (h : HoareTime M (fun x => x = v) (fun x => x = w) cost) :
    HoareTime (Alphabet.program (encoding (a := a)) M)
      (fun x => x = Alphabet.mapTapes encoding v) (fun x => x = Alphabet.mapTapes encoding w) cost := by
  apply (Alphabet.map_hoare encoding h).consequence _ _ le_rfl
  · rintro x rfl; exact ⟨_,rfl,rfl⟩
  · rintro x ⟨original,rfl,rfl⟩; rfl

/-- The original Q/B/n words and literal offset stream are the only control
inputs. Every private tape starts and returns wholly blank, with actual paid
initialization and erasure, on any larger finite alphabet. -/
theorem runs_linear (ws : List (List Bool)) (Q B : ℕ) (hQ : 0 < Q) (hB : 0 < B)
    (source dest control : ℤ → Fin 4) (p q r : ℤ) (bs qs ns : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (hn : Counter.value ns = ws.length)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns)
    (hc : ∀ xs ∈ ws, GrowingCounterData.Canonical xs) (hv : ∀ xs ∈ ws, Counter.value xs ≤ Q)
    (x : Fin (ws.length*(Q*B)) → Fin 4) :
    HoareTime (program a)
      (fun v => v=bare
        (putWord (mapTape source) p (List.ofFn fun j => (encoding (a := a)).encode (x j)))
        (mapTape dest)
        (putWord (mapTape control) r ((StreamedFiberTranslation.encoded ws).map (encoding (a := a)).encode))
        p q r bs qs ns)
      (fun v => v=bare
        (putWord (mapTape source) p (List.ofFn fun j => (encoding (a := a)).encode (x j)))
        (putWord (mapTape dest) q
          ((FiberLayoutData.translated x (fun i => StreamedFiberTranslation.offset ws i.val)).map
            (encoding (a := a)).encode))
        (putWord (mapTape control) r ((StreamedFiberTranslation.encoded ws).map (encoding (a := a)).encode))
        (p+((ws.length*(Q*B) : ℕ) : ℤ)) (q+((ws.length*(Q*B) : ℕ) : ℤ))
        (r+(StreamedFiberTranslation.encoded ws).length) bs qs ns)
      (483*(ws.length*(Q*B))+35) := by
  have h := map_exact (a := a) (M := (StreamedFiberTranslationInitialized.program : Program 15 252 0))
    (StreamedFiberTranslationInitialized.runs_linear ws Q B hQ hB
    source dest control p q r bs qs ns hb hq hn cb cq cn hc hv x)
  refine h.consequence ?_ ?_ (le_refl _)
  · intro v hv'
    rw [mapped_bare,map_word,map_word,List.map_ofFn]
    exact hv'
  · intro v hv'
    rw [mapped_bare,map_word,map_word,map_word,List.map_ofFn] at hv'
    exact hv'

/-- Exact whole-blank private state, including the last offset descriptor. -/
theorem bare_private (source dest control : ℤ → Fin (a+4)) (p q r : ℤ)
    (bs qs ns : List Bool) (i : Fin 15)
    (hi : i ∈ ([0,1,2,3,4,6,8,9,13] : List (Fin 15))) :
    (bare source dest control p q r bs qs ns).head i=0 ∧
      (bare source dest control p q r bs qs ns).tape i=fun _ => blank := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl,rfl⟩

end
end IntegerMultBounds.Machine.StreamedFiberTranslationInitializedAlphabet
