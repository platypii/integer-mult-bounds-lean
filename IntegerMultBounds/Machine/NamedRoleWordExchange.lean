import IntegerMultBounds.Machine.NativeRoleWordSwap

/-! Physical exchange of the two named banks of a finite role family. All
non-role words and all heads remain literal; no complete enumeration is reduced. -/
namespace IntegerMultBounds.Machine.NamedRoleWordExchange
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open WordBankCleanup (write)
variable {A S : Type*} [DecidableEq A] [DecidableEq S]
abbrev Role (A S : Type*) := A ⊕ A ⊕ S
variable {t : ℕ} (port : Role A S → Fin t) (hinj : Function.Injective port)

def bank (v : Tapes t 2) {sh : Shape} {rows ell : ℕ} (data : Role A S → Array sh rows ell) : Tapes t 2 :=
  by
  classical
  exact ⟨v.head,fun i => if h : ∃ a,port a=i then
    NativeZeroPadding.word (NativeZeroPaddingArray.word (data (Classical.choose h))) else v.tape i⟩

omit [DecidableEq A] [DecidableEq S] in
include hinj in
theorem bank_role (v : Tapes t 2) {sh : Shape} {rows ell : ℕ}
    (data : Role A S → Array sh rows ell) (a : Role A S) :
    (bank port v data).tape (port a)=NativeZeroPadding.word (NativeZeroPaddingArray.word (data a)) := by
  dsimp only [bank]
  rw [dite_eq_left ⟨a,rfl⟩]
  exact congrArg (fun z => NativeZeroPadding.word (NativeZeroPaddingArray.word (data z)))
    (hinj (Classical.choose_spec (show ∃ b,port b=port a from ⟨a,rfl⟩)))

def exchange {X : Type*} (a : A) (data : Role A S → X) :=
  Function.update (Function.update data (Sum.inl a) (data (Sum.inr (Sum.inl a))))
    (Sum.inr (Sum.inl a)) (data (Sum.inl a))

include hinj in
theorem bank_exchange (v : Tapes t 2) {sh : Shape} {rows ell : ℕ}
    (data : Role A S → Array sh rows ell) (a : A) :
    write (write (bank port v data) (port (Sum.inl a))
      (NativeZeroPadding.word (NativeZeroPaddingArray.word (data (Sum.inr (Sum.inl a))))))
      (port (Sum.inr (Sum.inl a)))
      (NativeZeroPadding.word (NativeZeroPaddingArray.word (data (Sum.inl a))))=
    bank port v (exchange a data) := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i
    change (write (write (bank port v data) (port (Sum.inl a))
      (NativeZeroPadding.word (NativeZeroPaddingArray.word (data (Sum.inr (Sum.inl a))))))
      (port (Sum.inr (Sum.inl a)))
      (NativeZeroPadding.word (NativeZeroPaddingArray.word (data (Sum.inl a))))).tape i=
      (bank port v (exchange a data)).tape i
    by_cases hx : port (Sum.inl a)=i
    · subst i
      have hn : port (Sum.inl a)≠port (Sum.inr (Sum.inl a)) := fun h => Sum.inl_ne_inr (hinj h)
      rw [bank_role port hinj]
      simp [write,exchange,hn]
    · by_cases hy : port (Sum.inr (Sum.inl a))=i
      · subst i
        rw [bank_role port hinj]
        simp only [write,Function.update_self,exchange]
      · have hx' : i≠port (Sum.inl a) := Ne.symm hx
        have hy' : i≠port (Sum.inr (Sum.inl a)) := Ne.symm hy
        simp only [write,Function.update_of_ne hx',Function.update_of_ne hy',bank]
        split_ifs with h
        · have hcx : Classical.choose h≠Sum.inl a := by
            intro he; exact hx (he ▸ Classical.choose_spec h)
          have hcy : Classical.choose h≠Sum.inr (Sum.inl a) := by
            intro he; exact hy (he ▸ Classical.choose_spec h)
          simp only [exchange,Function.update_of_ne hcx,Function.update_of_ne hcy]
        · rfl

def compile (ht : 2≤t) : List A → Σ q,Program t q 2
  | [] => ⟨1,skip _ _ (by omega)⟩
  | a::as => ⟨_,seq (NativeRoleWordSwap.program (port (Sum.inl a)) (port (Sum.inr (Sum.inl a)))
      (fun h => Sum.inl_ne_inr (hinj h)) ht) (compile ht as).2⟩

def execute {X : Type*} : List A → (Role A S → X) → (Role A S → X)
  | [],data => data
  | a::as,data => execute as (exchange a data)

theorem execute_width (as : List A) {sh : Shape} {rows ell w : ℕ}
    (data : Role A S → Array sh rows ell)
    (hw : ∀ a i,(data a i).1.length=w ∧ (data a i).2.length=w) :
    ∀ a i,(execute as data a i).1.length=w ∧ (execute as data a i).2.length=w := by
  induction as generalizing data with
  | nil => exact hw
  | cons a as ih =>
    apply ih
    intro b i
    unfold exchange
    by_cases hy : b=Sum.inr (Sum.inl a)
    · subst b; simpa only [Function.update_self] using hw (Sum.inl a) i
    · rw [Function.update_of_ne hy]
      by_cases hx : b=Sum.inl a
      · subst b; simpa only [Function.update_self] using hw (Sum.inr (Sum.inl a)) i
      · simpa only [Function.update_of_ne hx] using hw b i

theorem compile_runs (ht : 2≤t) (as : List A) (v : Tapes t 2)
    (sh : Shape) (rows ell p : ℕ) (hr : 0<rows)
    (data : Role A S → Array sh rows ell)
    (hw : ∀ a i,(data a i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (data a i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hh : ∀ a,v.head (port a)=0) :
    HoareTime (compile port hinj ht as).2 (fun z => z=bank port v data)
      (fun z => z=bank port v (execute as data))
      (as.length*(9*CompactNativeRoleTransferBudget.volume rows sh ell p+1)) := by
  induction as generalizing data with
  | nil => simpa only [compile,execute,List.length_nil,Nat.zero_mul] using
      skip_hoare (a:=2) (by omega : 0<t) (bank port v data)
  | cons a as ih =>
    have hone := NativeRoleWordSwap.runs_linear (bank port v data)
      (port (Sum.inl a)) (port (Sum.inr (Sum.inl a))) (fun h => Sum.inl_ne_inr (hinj h)) ht
      sh rows ell p hr _ _ (hw _) (hw _) (bank_role port hinj v data _) (bank_role port hinj v data _)
      (hh _) (hh _)
    rw [bank_exchange port hinj] at hone
    have hnext := ih (exchange a data) (execute_width [a] data hw)
    exact (hone.seq hnext).consequence (fun _ h => h) (fun _ h => h)
      (by simp only [List.length_cons,Nat.add_mul]; omega)

/-- A noduplicate list exchanges exactly its named X/Y pairs. -/
theorem execute_formula {X : Type*} (as : List A) (hn : as.Nodup) (data : Role A S → X) :
    (∀ b,execute as data (Sum.inl b)=if b∈as then data (Sum.inr (Sum.inl b)) else data (Sum.inl b)) ∧
    (∀ b,execute as data (Sum.inr (Sum.inl b))=if b∈as then data (Sum.inl b) else data (Sum.inr (Sum.inl b))) ∧
    (∀ c,execute as data (Sum.inr (Sum.inr c))=data (Sum.inr (Sum.inr c))) := by
  induction as generalizing data with
  | nil => simp [execute]
  | cons a as ih =>
    obtain ⟨ha,hn⟩ := List.nodup_cons.mp hn
    obtain ⟨hx,hy,hs⟩ := ih hn (exchange a data)
    refine ⟨?_,?_,?_⟩
    · intro b
      rw [execute,hx]
      by_cases he : b=a
      · subst b; simp [ha,exchange]
      · simp [he,exchange]
    · intro b
      rw [execute,hy]
      by_cases he : b=a
      · subst b; simp [ha,exchange]
      · simp [he,exchange]
    · intro c
      rw [execute,hs]
      simp [exchange]

omit [DecidableEq A] [DecidableEq S] in
theorem bank_eq (v : Tapes t 2) {sh : Shape} {rows ell : ℕ}
    (data : Role A S → Array sh rows ell)
    (hs : ∀ a,v.tape (port a)=NativeZeroPadding.word (NativeZeroPaddingArray.word (data a))) :
    bank port v data=v := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i
    split_ifs with h
    · rw [←hs (Classical.choose h),Classical.choose_spec h]
    · rfl

omit [DecidableEq A] [DecidableEq S] in
theorem bank_frame (v : Tapes t 2) {sh : Shape} {rows ell : ℕ}
    (data : Role A S → Array sh rows ell) (i : Fin t) (hi : ∀ a,port a≠i) :
    (bank port v data).tape i=v.tape i := by
  dsimp only [bank]
  exact dite_eq_right (by rintro ⟨a,ha⟩; exact hi a ha)

end
end IntegerMultBounds.Machine.NamedRoleWordExchange
