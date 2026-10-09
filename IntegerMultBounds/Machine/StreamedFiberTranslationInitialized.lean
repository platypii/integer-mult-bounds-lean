import IntegerMultBounds.Machine.StreamedFiberTranslationArray
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList

/-! Complete varying-offset rotation lifecycle. Only original B/Q/n headers,
source, destination and literal control stream are supplied; every private tape
starts and finishes blank at zero. Payload heads advance by the exact volume. -/
namespace IntegerMultBounds.Machine.StreamedFiberTranslationInitialized
open CountedCopyReuse (binary empty)
open StreamedFiberTranslation (encoded old)
open SharedPlacementAlphabet (setTape)
noncomputable section

/-- The three immutable original headers occupy slots 5,7,14. -/
def bare (source dest control : ℤ → Fin 4) (p q r : ℤ)
    (bs qs ns : List Bool) : Tapes 15 0 :=
  ⟨![0,0,0,0,0,1,0,1,0,0,p,q,r,0,1],
   ![fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,
     fun _ => blank,binary bs,fun _ => blank,binary qs,fun _ => blank,
     fun _ => blank,source,dest,control,fun _ => blank,binary ns]⟩

def ready (source dest control : ℤ → Fin 4) (p q r : ℤ)
    (bs qs ns as : List Bool) : Tapes 15 0 :=
  ⟨![1,1,1,1,1,1,1,1,1,0,p,q,r,1,1],
   fun i => if i=8 then binary as else
     ![fun _ => blank,empty,empty,empty,empty,binary bs,empty,binary qs,
       empty,fun _ => blank,source,dest,control,empty,binary ns] i⟩

def marker (i : Fin 15) : Bool := decide (i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=6 ∨ i=8 ∨ i=13)
def shifted (i : Fin 15) : Bool := decide (i=0) || marker i

def setupProgram : Program 15 2 0 where
  tapes_pos := by decide
  start := 0
  transition := fun s xs => if s=0 then some (1,fun i =>
    (if marker i then separator else xs i,if shifted i then Move.right else Move.stay)) else none

theorem initializes (source dest control : ℤ → Fin 4) (p q r : ℤ)
    (bs qs ns : List Bool) :
    HoareTime setupProgram (fun v => v=bare source dest control p q r bs qs ns)
      (fun v => v=ready source dest control p q r bs qs ns []) 1 := by
  intro v hv
  subst v
  refine ⟨1,⟨1,(ready source dest control p q r bs qs ns []).head,
    (ready source dest control p q r bs qs ns []).tape⟩,le_rfl,?_,?_,rfl⟩
  · rw [run_one]
    simp only [step,setupProgram,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> simp [bare,ready,marker,shifted,Move.offset]
    · funext i z; fin_cases i <;>
        simp [bare,ready,marker,binary,empty,putBits] <;> aesop
  · simp [step,setupProgram]

def resetSlot (i : Fin 15) : Bool := decide (i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=6 ∨ i=13)

/-- Move to every private sentinel, then physically erase it. -/
def eraseMarkers : Program 15 3 0 where
  tapes_pos := by decide
  start := 0
  transition := fun s xs => if s=0 then some (1,fun i =>
    (xs i,if resetSlot i then Move.left else Move.stay)) else if s=1 then
    some (2,fun i => (if resetSlot i then blank else xs i,Move.stay)) else none

def lowered (source dest control : ℤ → Fin 4) (p q r : ℤ)
    (bs qs ns : List Bool) : Tapes 15 0 :=
  ⟨(bare source dest control p q r bs qs ns).head,
   (setTape (ready source dest control p q r bs qs ns []) 8 (fun _ => blank) 0).tape⟩

theorem erases_markers (source dest control : ℤ → Fin 4) (p q r : ℤ)
    (bs qs ns : List Bool) :
    HoareTime eraseMarkers
      (fun v => v=setTape (ready source dest control p q r bs qs ns []) 8 (fun _ => blank) 0)
      (fun v => v=bare source dest control p q r bs qs ns) 2 := by
  intro v hv
  subst v
  refine ⟨2,⟨2,(bare source dest control p q r bs qs ns).head,
    (bare source dest control p q r bs qs ns).tape⟩,le_rfl,?_,?_,rfl⟩
  · change Machine.run eraseMarkers (1+1) _ = _
    rw [run_add]
    have hfirst : Machine.run eraseMarkers 1
        ((setTape (ready source dest control p q r bs qs ns []) 8 (fun _ => blank) 0).start eraseMarkers) =
        some ⟨1,(lowered source dest control p q r bs qs ns).head,
          (lowered source dest control p q r bs qs ns).tape⟩ := by
      rw [run_one]
      simp only [step,eraseMarkers,Tapes.start,ite_true]
      congr 1
      congr 1
      · funext i; fin_cases i <;> simp [setTape,ready,lowered,bare,resetSlot,Move.offset]
      · funext i z
        simp only [lowered,setTape,ready]
        by_cases hz : z = (Function.update ![1,1,1,1,1,1,1,1,1,0,p,q,r,1,1] 8 0) i <;>
          simp [hz]
    change (Machine.run eraseMarkers 1 _).bind (Machine.run eraseMarkers 1) = _
    rw [hfirst]
    rw [Option.bind_some,run_one]
    simp only [step,eraseMarkers,show (1 : Fin 3) ≠ 0 by decide,ite_false,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> simp [lowered,bare,Move.offset]
    · funext i z; fin_cases i <;>
        simp [lowered,bare,ready,setTape,resetSlot,empty] <;> aesop
  · simp [step,eraseMarkers]

def cleanup := seq (BinaryDescriptorCleanupList.oneProgram (a := 0) (8 : Fin 15)) eraseMarkers

theorem cleans (source dest control : ℤ → Fin 4) (p q r : ℤ)
    (bs qs ns as : List Bool) :
    HoareTime cleanup (fun v => v=ready source dest control p q r bs qs ns as)
      (fun v => v=bare source dest control p q r bs qs ns) (2*as.length+7) := by
  have h := BinaryDescriptorCleanupList.one_hoare (8 : Fin 15)
    (ready source dest control p q r bs qs ns as) as
    (by exact BinaryDescriptorStackRoundtrip.descriptor_encoded as |>.symm) rfl
  have he : setTape (ready source dest control p q r bs qs ns as) 8 (fun _ => blank) 0 =
      setTape (ready source dest control p q r bs qs ns []) 8 (fun _ => blank) 0 := by
    apply congrArg₂ Tapes.mk
    · rfl
    · funext i z
      simp only [ready,Function.update_apply]
      split_ifs <;> rfl
  rw [he] at h
  exact (h.seq (erases_markers source dest control p q r bs qs ns)).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

def program := seq (seq setupProgram StreamedFiberTranslation.program) cleanup

private theorem input_ready (ws : List (List Bool)) (Q B : ℕ)
    (source dest control : ℤ → Fin 4) (p q r : ℤ) (bs qs ns : List Bool)
    (a : Fin (ws.length*(Q*B)) → Fin 4) :
    StreamedFiberTranslationArray.bank ws Q B source dest control p q r bs qs ns a 0 =
      ready (putWord source p (List.ofFn a)) dest (putWord control r (encoded ws)) p q r bs qs ns [] := by
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> first | rfl | (change p+((0*(Q*B):ℕ):ℤ)=p; simp) | (change q+((0*(Q*B):ℕ):ℤ)=q; simp) | (change r+(encoded (ws.take 0)).length=r; simp [encoded])
  · funext i; fin_cases i <;> first | rfl | exact StreamedFiberTranslationArray.source_tape ws Q B source dest control p q r bs qs ns a 0

private theorem output_ready (ws : List (List Bool)) (Q B : ℕ)
    (source dest control : ℤ → Fin 4) (p q r : ℤ) (bs qs ns : List Bool)
    (a : Fin (ws.length*(Q*B)) → Fin 4) :
    StreamedFiberTranslationArray.bank ws Q B source dest control p q r bs qs ns a ws.length =
      ready (putWord source p (List.ofFn a))
        (putWord dest q (FiberLayoutData.translated a (fun i => StreamedFiberTranslation.offset ws i.val)))
        (putWord control r (encoded ws)) (p+((ws.length*(Q*B) : ℕ) : ℤ))
        (q+((ws.length*(Q*B) : ℕ) : ℤ)) (r+(encoded ws).length) bs qs ns (old ws ws.length) := by
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> first | rfl | exact (StreamedFiberTranslationArray.output_heads ws Q B source dest control p q r bs qs ns a).2.2
  · funext i; fin_cases i <;> first | rfl | exact StreamedFiberTranslationArray.source_tape ws Q B source dest control p q r bs qs ns a ws.length | exact StreamedFiberTranslationArray.destination_tape ws Q B source dest control p q r bs qs ns a

/-- Actual initialized stream rotation and physical final erasure, retaining
all original headers and literal control symbols. Zero fibers are included. -/
theorem runs (ws : List (List Bool)) (Q B : ℕ) (hQ : 0 < Q) (hB : 0 < B)
    (source dest control : ℤ → Fin 4) (p q r : ℤ) (bs qs ns : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (hn : Counter.value ns = ws.length)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns)
    (hc : ∀ xs ∈ ws, GrowingCounterData.Canonical xs) (hv : ∀ xs ∈ ws, Counter.value xs ≤ Q)
    (a : Fin (ws.length*(Q*B)) → Fin 4) :
    HoareTime program
      (fun v => v=bare (putWord source p (List.ofFn a)) dest (putWord control r (encoded ws)) p q r bs qs ns)
      (fun v => v=bare (putWord source p (List.ofFn a))
        (putWord dest q (FiberLayoutData.translated a (fun i => StreamedFiberTranslation.offset ws i.val)))
        (putWord control r (encoded ws)) (p+((ws.length*(Q*B) : ℕ) : ℤ))
        (q+((ws.length*(Q*B) : ℕ) : ℤ)) (r+(encoded ws).length) bs qs ns)
      (481*(ws.length*(Q*B))+2*(old ws ws.length).length+33) := by
  have hi := initializes (putWord source p (List.ofFn a)) dest (putWord control r (encoded ws)) p q r bs qs ns
  have hr := StreamedFiberTranslationArray.runs ws Q B hQ hB source dest control p q r bs qs ns
    hb hq hn cb cq cn hc hv a
  rw [input_ready,output_ready] at hr
  have he := cleans (putWord source p (List.ofFn a))
    (putWord dest q (FiberLayoutData.translated a (fun i => StreamedFiberTranslation.offset ws i.val)))
    (putWord control r (encoded ws)) (p+((ws.length*(Q*B) : ℕ) : ℤ))
    (q+((ws.length*(Q*B) : ℕ) : ℤ)) (r+(encoded ws).length) bs qs ns (old ws ws.length)
  exact ((hi.seq hr).seq he).consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- Final offset cleanup remains linear in the original payload volume. -/
theorem cost_linear (ws : List (List Bool)) (Q B : ℕ) (_hQ : 0 < Q) (hB : 0 < B)
    (hc : ∀ xs ∈ ws, GrowingCounterData.Canonical xs)
    (hv : ∀ xs ∈ ws, Counter.value xs ≤ Q) :
    481*(ws.length*(Q*B))+2*(old ws ws.length).length+33 ≤
      483*(ws.length*(Q*B))+35 := by
  by_cases hw : ws.length=0
  · have he : ws=[] := List.length_eq_zero_iff.mp hw
    simp [he,old]
  · have ho := StreamedFiberTranslation.old_length ws Q ws.length le_rfl hc hv
    have hQB : Q ≤ Q*B := Nat.le_mul_of_pos_right _ hB
    have hn : 1 ≤ ws.length := by omega
    have hV : Q*B ≤ ws.length*(Q*B) := by nlinarith
    omega

/-- Exact clean endpoint with a uniform linear charge, including an empty stream. -/
theorem runs_linear (ws : List (List Bool)) (Q B : ℕ) (hQ : 0 < Q) (hB : 0 < B)
    (source dest control : ℤ → Fin 4) (p q r : ℤ) (bs qs ns : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (hn : Counter.value ns = ws.length)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns)
    (hc : ∀ xs ∈ ws, GrowingCounterData.Canonical xs) (hv : ∀ xs ∈ ws, Counter.value xs ≤ Q)
    (a : Fin (ws.length*(Q*B)) → Fin 4) :
    HoareTime program
      (fun v => v=bare (putWord source p (List.ofFn a)) dest (putWord control r (encoded ws)) p q r bs qs ns)
      (fun v => v=bare (putWord source p (List.ofFn a))
        (putWord dest q (FiberLayoutData.translated a (fun i => StreamedFiberTranslation.offset ws i.val)))
        (putWord control r (encoded ws)) (p+((ws.length*(Q*B) : ℕ) : ℤ))
        (q+((ws.length*(Q*B) : ℕ) : ℤ)) (r+(encoded ws).length) bs qs ns)
      (483*(ws.length*(Q*B))+35) :=
  (runs ws Q B hQ hB source dest control p q r bs qs ns hb hq hn cb cq cn hc hv a).consequence
    (fun _ h => h) (fun _ h => h) (cost_linear ws Q B hQ hB hc hv)

/-- Every private tape is wholly blank, with its head at zero. -/
theorem bare_private (source dest control : ℤ → Fin 4) (p q r : ℤ)
    (bs qs ns : List Bool) (i : Fin 15)
    (hi : i ∈ ([0,1,2,3,4,6,8,9,13] : List (Fin 15))) :
    (bare source dest control p q r bs qs ns).head i=0 ∧
      (bare source dest control p q r bs qs ns).tape i=fun _ => blank := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl,rfl⟩

/-- The supplied immutable B,Q,n words remain in their original slots. -/
theorem bare_headers (source dest control : ℤ → Fin 4) (p q r : ℤ)
    (bs qs ns : List Bool) :
    (bare source dest control p q r bs qs ns).head 5=1 ∧
    (bare source dest control p q r bs qs ns).tape 5=binary bs ∧
    (bare source dest control p q r bs qs ns).head 7=1 ∧
    (bare source dest control p q r bs qs ns).tape 7=binary qs ∧
    (bare source dest control p q r bs qs ns).head 14=1 ∧
    (bare source dest control p q r bs qs ns).tape 14=binary ns := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end
end IntegerMultBounds.Machine.StreamedFiberTranslationInitialized
