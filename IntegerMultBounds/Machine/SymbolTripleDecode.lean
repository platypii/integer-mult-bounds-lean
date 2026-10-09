import IntegerMultBounds.Machine.SymbolTripleEncode
import IntegerMultBounds.Machine.Branch

/-! A finite runtime decoder reads all three Boolean cells and physically
writes the recovered native coefficient symbol. Branches inspect actual cells;
no decoded value or branch result is supplied to the transition table. -/
namespace IntegerMultBounds.Machine.SymbolTripleDecode
noncomputable section

def value (a b c : Bool) : Fin 6 :=
  ⟨min (4*(if a then 1 else 0)+2*(if b then 1 else 0)+(if c then 1 else 0)) 5,
    Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

def test (sy : Fin 2 → Fin 6) : Bool := sy 0==bitSymbol true

def advance : Program 2 2 2 := DescriptorStackControl.once (by decide : 0<2)
  (fun sy i => (sy i,if i=0 then .right else .stay))

def writer (a b : Bool) := DescriptorStackControl.once (by decide : 0<2)
  (fun sy i => if i=0 then (sy 0,.right) else (value a b (sy 0==bitSymbol true),.right))

def second (a : Bool) := branch test (seq advance (writer a true)) (seq advance (writer a false))
def body := branch test (seq advance (second true)) (seq advance (second false))

private theorem advance_runs (f g : ℤ → Fin 6) (p r : ℤ) :
    HoareTime advance (fun v => v=Copy.tapes f g p r)
      (fun v => v=Copy.tapes f g (p+1) r) 1 := by
  have h := DescriptorStackControl.once_hoare (by decide : 0<2)
    (fun sy i => (sy i,if i=0 then .right else .stay)) (Copy.tapes f g p r)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i
    · rfl
    · exact add_zero r
  · funext i z; fin_cases i
    all_goals dsimp only [DescriptorStackControl.after,Copy.tapes,Copy.cfg,Config.tapes]
    all_goals split_ifs with hz <;> simp_all

private theorem writer_runs (a b c : Bool) (f g : ℤ → Fin 6) (p r : ℤ)
    (hc : f p=bitSymbol c) :
    HoareTime (writer a b) (fun v => v=Copy.tapes f g p r)
      (fun v => v=Copy.tapes f (Function.update g r (value a b c)) (p+1) (r+1)) 1 := by
  have h := DescriptorStackControl.once_hoare (by decide : 0<2)
    (fun sy i => if i=0 then (sy 0,.right) else (value a b (sy 0==bitSymbol true),.right))
    (Copy.tapes f g p r)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> rfl
  · funext i z; fin_cases i
    · change (if z=p then f p else f z)=f z
      split_ifs with hz <;> simp_all
    · dsimp only [DescriptorStackControl.after,Copy.tapes,Copy.cfg,Config.tapes]
      have hbit : (bitSymbol c == bitSymbol (a := 2) true)=c := by
        cases c <;> simp [bitSymbol]
      simp [hc,hbit,Function.update_apply]

private theorem test_reads (f g : ℤ → Fin 6) (p r : ℤ) (a : Bool) (ha : f p=bitSymbol a) :
    test (Copy.tapes f g p r).reads=a := by
  change (f p==bitSymbol true)=a
  rw [ha]
  cases a <;> simp [bitSymbol]

private theorem branch_exact {q r B : ℕ} (M : Program 2 q 2) (N : Program 2 r 2)
    (v w : Tapes 2 2) (b : Bool) (ht : test v.reads=b)
    (hy : b=true → HoareTime M (fun z => z=v) (fun z => z=w) B)
    (hn : b=false → HoareTime N (fun z => z=v) (fun z => z=w) B) :
    HoareTime (branch test M N) (fun z => z=v) (fun z => z=w) (B+1) := by
  have h := branch_hoare test
    (show HoareTime M (fun z => z=v ∧ test z.reads=true) (fun z => z=w) B from by
      intro z hz
      have hb : b=true := ht.symm.trans (hz.1 ▸ hz.2)
      exact hy hb z hz.1)
    (show HoareTime N (fun z => z=v ∧ test z.reads=false) (fun z => z=w) B from by
      intro z hz
      have hb : b=false := ht.symm.trans (hz.1 ▸ hz.2)
      exact hn hb z hz.1)
  simpa only [max_self] using h

private theorem second_runs (a b c : Bool) (f g : ℤ → Fin 6) (p r : ℤ)
    (hb : f p=bitSymbol b) (hc : f (p+1)=bitSymbol c) :
    HoareTime (second a) (fun v => v=Copy.tapes f g p r)
      (fun v => v=Copy.tapes f (Function.update g r (value a b c)) (p+2) (r+1)) 4 := by
  have hmove := advance_runs f g p r
  have hwrite := writer_runs a b c f g (p+1) r hc
  rw [show p+1+1=p+2 by ring] at hwrite
  apply branch_exact _ _ _ _ b (test_reads f g p r b hb)
  · intro he; subst b; exact hmove.seq hwrite
  · intro he; subst b; exact hmove.seq hwrite

theorem body_reads (a b c : Bool) (f g : ℤ → Fin 6) (p r : ℤ)
    (ha : f p=bitSymbol a) (hb : f (p+1)=bitSymbol b) (hc : f (p+2)=bitSymbol c) :
    HoareTime body (fun v => v=Copy.tapes f g p r)
      (fun v => v=Copy.tapes f (Function.update g r (value a b c)) (p+3) (r+1)) 7 := by
  have hmove := advance_runs f g p r
  have hnext := second_runs a b c f g (p+1) r hb (by simpa only [show p+1+1=p+2 by ring] using hc)
  rw [show p+1+2=p+3 by ring] at hnext
  apply branch_exact _ _ _ _ a (test_reads f g p r a ha)
  · intro he; subst a; exact hmove.seq hnext
  · intro he; subst a; exact hmove.seq hnext

theorem value_code (s : Fin 6) : value (SymbolTripleEncode.bit s 0)
    (SymbolTripleEncode.bit s 1) (SymbolTripleEncode.bit s 2)=s := by
  fin_cases s <;> norm_num [value,SymbolTripleEncode.bit]

theorem body_runs (s : Fin 6) (f g : ℤ → Fin 6) (p r : ℤ)
    (hf : ∀ i : Fin 3,f (p+i.val)=bitSymbol (SymbolTripleEncode.bit s i)) :
    HoareTime body (fun v => v=Copy.tapes f g p r)
      (fun v => v=Copy.tapes f (Function.update g r s) (p+3) (r+1)) 7 := by
  have h := body_reads (SymbolTripleEncode.bit s 0) (SymbolTripleEncode.bit s 1)
    (SymbolTripleEncode.bit s 2) f g p r (by simpa using hf 0) (hf 1) (hf 2)
  rwa [value_code] at h

end
end IntegerMultBounds.Machine.SymbolTripleDecode
