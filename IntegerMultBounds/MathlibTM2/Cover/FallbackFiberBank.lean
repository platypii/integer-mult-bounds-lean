module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackFiberLoop

/-! Initialize the translation workspace from two binary header words and blank stacks. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host TranslationExecutionReuse
variable {T Q A : ℕ} {P U : Type}

def markers (call : Fin 12 ↪ Fin T) := ([1,2,3,4,5,6,7,8] : List (Fin 12)).map call

def pushMarkers : List (Fin T) → Act T Q A U
  | [] => .done
  | i :: is => .push (.lt i) (fun _ => separator) (pushMarkers is)

theorem pushMarkers_run (is : List (Fin T)) (nd : is.Nodup) (v : HS T Q A U) (S : Stacks T A) :
    (pushMarkers is).run (mk v S) =
      mk v {S with L := fun i => if i ∈ is then separator :: S.L i else S.L i} := by
  induction is generalizing S with
  | nil => simp [pushMarkers]
  | cons k ks ih =>
    rw [List.nodup_cons] at nd
    simp only [pushMarkers,Action.run,mk_stk,mk_var,Stacks.get,update_lt,store_mk]
    rw [ih nd.2]
    congr 2
    funext i
    by_cases h : i = k
    · subst i; simp [nd.1]
    · simp [h]

def initializeBank (call : Fin 12 ↪ Fin T) : Pr P T Q A U := .act (pushMarkers (markers call))

/-- Slots 5 and 7 hold the block width and modulus. Slots 10 and 11 already
represent the payload tapes at their caller-selected heads. -/
theorem initializeBank_exec (body : P → Pr P T Q A U) (call : Fin 12 ↪ Fin T)
    (bs ms : List Bool) (src dst : ℤ → Fin 4) (p q : ℤ)
    (v : HS T Q A U) (S : Stacks T A)
    (left : ∀ i : Fin 12, i < 10 → S.L (call i) = [])
    (right : ∀ i : Fin 12, i < 10 → S.R (call i) =
      if i = 5 then bs.map bitSymbol else if i = 7 then ms.map bitSymbol else [])
    (source : ∀ k, RadixToBinary.binaryEncoding.encode (src k) =
      readAt blank (S.L (call 10)) (S.R (call 10)) (k-p))
    (dest : ∀ k, RadixToBinary.binaryEncoding.encode (dst k) =
      readAt blank (S.L (call 11)) (S.R (call 11)) (k-q)) :
    ∃ F, Exec body (initializeBank call) (mk v S) 1 (mk v F) ∧
      F.R = S.R ∧ F.L (call 8) = [separator] ∧
      (∀ i, (∀ j, call j ≠ i) → F.L i = S.L i) ∧
      RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding (bank src dst p q bs ms []))
        (F.L ∘ call) (F.R ∘ call) := by
  have nd : (markers call).Nodup :=
    (show ([1,2,3,4,5,6,7,8] : List (Fin 12)).Nodup by decide).map call.injective
  have run := Exec.act (body := body) (pushMarkers (markers call)) (mk v S)
  rw [pushMarkers_run _ nd] at run
  refine ⟨_,run,
    rfl,?_,?_,?_⟩
  · simp [markers,left 8 (by decide)]
  · intro i hi; simp [markers,fun j => (hi j).symm]
  · intro i k
    have header (xs : List Bool) : RadixZeroFill.encodedBinary (q := A) xs k =
        readAt blank [separator] (xs.map bitSymbol) (k-1) := by rw [encodedBinary_eq,readAt_single]
    have empty (h : ℤ) : (blank : Fin (A+4)) = readAt blank [] [] (k-h) := by
      rw [readAt_nil_left,wordTape_nil]
    fin_cases i <;> simp only [Function.comp_apply] <;>
      simp [markers,call.injective.eq_iff,left,right] <;>
      first | exact header [] | exact header _ | exact empty _ | exact source k | exact dest k

/-- Start the complete shear with raw width and modulus words and unmarked workspace. -/
theorem initializedShear_exec (body : P → Pr P T 217 A U) (r : Fin 13 ↪ Fin T)
    (call : Fin 12 ↪ Fin T) (slot : call 8 = r 3)
    (outside : ∀ i : Fin 13, i ≠ 3 → ∀ j, call j ≠ r i)
    (count : Fin T) (hr : ∀ i, r i ≠ count) (ht : ∀ i, call i ≠ count)
    (L c M B : ℕ) (hc : c < M) (hM : M < 2^L) (hB : 0 < B)
    (v : HS T 217 A U) (S : Stacks T A) (coef : S.R (r 0) = binSyms L c)
    (modulus : S.R (r 2) = binSyms L M) (digit : S.R (r 1) = [])
    (scratch : ∀ i : Fin 13, 3 ≤ i → i < 12 → S.R (r i) = [])
    (source dest : ℤ → Fin 4) (p q : ℤ) (payload : ℕ → ℕ → List (Fin 4))
    (hw : ∀ i y, (payload i y).length = B) (bs ms : List Bool)
    (hb : Counter.value bs = B) (hm : Counter.value ms = M)
    (cb : GrowingCounterData.Canonical bs) (cm : GrowingCounterData.Canonical ms)
    (empty : S.R count = [])
    (left : ∀ i : Fin 12, i < 10 → S.L (call i) = [])
    (right : ∀ i : Fin 12, i < 10 → S.R (call i) =
      if i = 5 then bs.map bitSymbol else if i = 7 then ms.map bitSymbol else [])
    (src : ∀ k, RadixToBinary.binaryEncoding.encode
      (putWord source p (TranslationStream.fibers M M payload).flatten k) =
        readAt blank (S.L (call 10)) (S.R (call 10)) (k-p))
    (dst : ∀ k, RadixToBinary.binaryEncoding.encode (dest k) =
        readAt blank (S.L (call 11)) (S.R (call 11)) (k-q)) :
    ∃ z F n, z.user = v.user ∧ n ≤ 6*M+15*L+11 + M*(48*L*L+162*L+93+(207*(M*B)+241)*25)+2 ∧
      Exec body (Prog.seq (initializeBank call) (shearProgram r call count)) (mk v S) n (mk z F) ∧
      F.R count = [] ∧ FiberReady r L c M M F ∧
      RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
        (shearBank M B c source dest p q payload bs ms M)) (F.L ∘ call) (F.R ∘ call) := by
  obtain ⟨D,init,hR,mark,_,rep⟩ := initializeBank_exec body call bs ms _ dest p q v S left right src dst
  have hrep : RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
      (shearBank M B c source dest p q payload bs ms 0)) (D.L ∘ call) (D.R ∘ call) := by
    simpa [shearBank,TranslationPreparedFamily.outputPrefix,putWord] using rep
  obtain ⟨z,F,n,hu,hn,run,rest,ready,final⟩ := shear_exec body r call slot outside count hr ht
    L c M B hc hM hB v D (hR ▸ coef) (hR ▸ modulus) (hR ▸ digit) (hR ▸ scratch)
    (slot ▸ mark) source dest p q payload hw bs ms hb hm cb cm (hR ▸ empty) hrep
  exact ⟨z,F,_,hu,by omega,Exec.seq init run,rest,ready,final⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
