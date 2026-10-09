import IntegerMultBounds.Machine.StreamedFiberTranslationInitialized
import IntegerMultBounds.Machine.WordBankCleanup

/-! Reusable varying-offset binary rotations. The real initialized stream
machine writes a private destination, returns both payload heads, copies the
rotated word over the original source and physically erases the destination. -/
namespace IntegerMultBounds.Machine.StreamedFiberTranslationReusable
noncomputable section
open StreamedFiberTranslationInitialized (bare)
open StreamedFiberTranslation (encoded offset)
open SharedPlacementAlphabet (setTape)
open WordBankCleanup (write)

def rewindProgram (slot : Fin 15) := Placement.placed (ReturnOrigin.program (a := 0))
  (FiniteReturnStackAt.placement slot)

/-- Actual origin return on one named tape, with the complete bank framed. -/
theorem rewind_hoare (slot : Fin 15) (v : Tapes 15 0) (f : ℤ → Fin 4) (p : ℤ)
    (xs : List (Fin 4)) (hx : ∀ x ∈ xs, x ≠ blank) (hf : f (p-1)=blank)
    (ht : v.tape slot=putWord f p xs) (hh : v.head slot=p+xs.length) :
    HoareTime (rewindProgram slot) (fun w => w=v)
      (fun w => w=setTape v slot (putWord f p xs) p) (xs.length+2) := by
  have ha : Placement.active (FiniteReturnStackAt.placement slot) v =
      (ReturnOrigin.cfg (putWord f p xs) (p+xs.length) 0).tapes := by
    rw [FiniteReturnStackAt.active_bank,ht,hh]
    rfl
  have h := Placement.hoare_at (ReturnOrigin.return_hoare_at f p xs hx hf)
    (FiniteReturnStackAt.placement slot) v ha
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  exact FiniteReturnStackAt.replace_bank _ _ _ _

/-- Translation only permutes literal bit symbols. -/
theorem translated_nonblank {P Q B : ℕ} (a : Fin (P*(Q*B)) → Bool) (os : Fin P → ℕ) :
    ∀ x ∈ FiberLayoutData.translated (fun i => bitSymbol (a i)) os, x ≠ (blank : Fin 4) := by
  intro x hx
  obtain ⟨word,hw,hx⟩ := List.mem_flatten.mp hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
  have hx' := (BlockRotationData.payload_perm (os i)
    (FiberLayoutData.fiber (fun j => bitSymbol (a j)) i)).mem_iff.mp hx
  obtain ⟨block,hb,hx'⟩ := List.mem_flatten.mp hx'
  obtain ⟨y,rfl⟩ := List.mem_ofFn.mp hb
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx'
  change bitSymbol (a (FiberLayoutData.index i y j)) ≠ (blank : Fin 4)
  cases a (FiberLayoutData.index i y j) <;> decide

def program := seq (seq (seq (seq StreamedFiberTranslationInitialized.program
  (rewindProgram 10)) (rewindProgram 11))
  (WordBankCleanup.replaceProgram (11 : Fin 15) 10 (by decide) (by decide) 0))
  (WordBankCleanup.clearProgram (11 : Fin 15) (by decide) 0)

/-- Source origin and exterior, original descriptors and literal control tape
are retained. Every private tape, including the whole destination, is blank at
head zero. The control head finishes at the exact end of the consumed stream. -/
theorem runs (ws : List (List Bool)) (Q B : ℕ) (hQ : 0 < Q) (hB : 0 < B)
    (f control : ℤ → Fin 4) (p r : ℤ) (hf : f (p-1)=blank) (bs qs ns : List Bool)
    (hb : Counter.value bs=B) (hq : Counter.value qs=Q) (hn : Counter.value ns=ws.length)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns)
    (hc : ∀ xs ∈ ws, GrowingCounterData.Canonical xs) (hv : ∀ xs ∈ ws, Counter.value xs ≤ Q)
    (a : Fin (ws.length*(Q*B)) → Bool) :
    HoareTime program
      (fun v => v=bare (putWord f p (List.ofFn (fun i => bitSymbol (a i))))
        (fun _ => blank) (putWord control r (encoded ws)) p 0 r bs qs ns)
      (fun v => v=bare (putWord f p (FiberLayoutData.translated (fun i => bitSymbol (a i))
        (fun i => offset ws i.val))) (fun _ => blank) (putWord control r (encoded ws))
        p 0 (r+(encoded ws).length) bs qs ns)
      (500*(ws.length*(Q*B))+70) := by
  let X : List (Fin 4) := List.ofFn (fun i => bitSymbol (a i))
  let Y := FiberLayoutData.translated (fun i => (bitSymbol (a i) : Fin 4)) (fun i => offset ws i.val)
  let V := ws.length*(Q*B)
  have hx : ∀ x ∈ X, x ≠ blank := by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    cases a i <;> decide
  have hy : ∀ x ∈ Y, x ≠ blank := translated_nonblank a _
  have hX : X.length=V := List.length_ofFn
  have hY : Y.length=V := FiberLayoutData.translated_length _ _
  let C := putWord control r (encoded ws)
  let r' : ℤ := r+(encoded ws).length
  let A := bare (putWord f p X) (putWord (fun _ => blank) 0 Y) C (p+V) V r' bs qs ns
  let B0 := bare (putWord f p X) (putWord (fun _ => blank) 0 Y) C p V r' bs qs ns
  let B1 := bare (putWord f p X) (putWord (fun _ => blank) 0 Y) C p 0 r' bs qs ns
  let B2 := bare (putWord f p Y) (putWord (fun _ => blank) 0 Y) C p 0 r' bs qs ns
  have hr := StreamedFiberTranslationInitialized.runs_linear ws Q B hQ hB f (fun _ => blank)
    control p 0 r bs qs ns hb hq hn cb cq cn hc hv (fun i => bitSymbol (a i))
  have hA : HoareTime StreamedFiberTranslationInitialized.program
      (fun v => v=bare (putWord f p X) (fun _ => blank) C p 0 r bs qs ns)
      (fun v => v=A) (483*V+35) := by
    simpa only [X,Y,V,C,r',A,zero_add] using hr
  have hs := rewind_hoare 10 A f p X hx hf rfl (by simp [A,bare,hX])
  have hsout : setTape A 10 (putWord f p X) p = B0 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [hsout,hX] at hs
  have hd := rewind_hoare 11 B0 (fun _ => blank) 0 Y hy rfl rfl (by simp [B0,bare,hY])
  have hdout : setTape B0 11 (putWord (fun _ => blank) 0 Y) 0 = B1 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [hdout,hY] at hd
  have hp := WordBankCleanup.replace_hoare B1 (11 : Fin 15) 10 (by decide) (by decide)
    (fun _ => blank) f Y X (hY.trans hX.symm) rfl rfl hy rfl rfl hf
  have hpout : write B1 10 (putWord f p Y) = B2 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  change HoareTime _ (fun w => w=B1) (fun w => w=write B1 10 (putWord f p Y)) _ at hp
  rw [hpout,hY] at hp
  have he := WordBankCleanup.clear_hoare B2 (11 : Fin 15) (by decide) Y hy rfl
  have heout : write B2 11 (fun _ => blank) = bare (putWord f p Y)
      (fun _ => blank) C p 0 r' bs qs ns := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [heout,hY] at he
  exact ((((hA.seq hs).seq hd).seq hp).seq he).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.StreamedFiberTranslationReusable
