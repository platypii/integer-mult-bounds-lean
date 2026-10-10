import IntegerMultBounds.Machine.RawLinearCombinationFieldFamily

/-! A whole Gaussian row executes every fixed wire expression on both stored
components. Output records retain the original wire ordering; original marked
source controls are restored and one shared private bank is blank afterward. -/
namespace IntegerMultBounds.Machine.RawLinearCombinationComplexFamily
noncomputable section
open RadixLinearCombinationRefresh (Expr Size controls)
variable {c q S : ℕ} [Fact q.Prime]

def placement (c S : ℕ) : Fin ((c+(c+S))+c) ≃ Fin (c+(c+(c+S))) where
  toFun := Fin.addCases
    (Fin.addCases (Fin.castAdd (c+(c+S))) (fun i => Fin.natAdd c (Fin.natAdd c i)))
    (fun i => Fin.natAdd c (Fin.castAdd (c+S) i))
  invFun := Fin.addCases (fun i => Fin.castAdd c (Fin.castAdd (c+S) i))
    (Fin.addCases (fun i => Fin.natAdd (c+(c+S)) i) (fun i => Fin.castAdd c (Fin.natAdd c i)))
  left_inv := by
    intro i
    induction i using Fin.addCases with
    | left i => induction i using Fin.addCases <;> simp
    | right i => simp
  right_inv := by
    intro i
    induction i using Fin.addCases with
    | left i => simp
    | right i => induction i using Fin.addCases <;> simp

omit [Fact q.Prime] in
private theorem active (x y : Tapes c q) (z : Tapes (c+S) q) :
    Placement.active (placement c S) (x.append (y.append z))=x.append z := by
  apply Placement.Tapes.ext'
  all_goals intro i; induction i using Fin.addCases <;> simp [Placement.active,placement,Tapes.append]

omit [Fact q.Prime] in
private theorem extra (x y : Tapes c q) (z : Tapes (c+S) q) :
    Placement.extra (placement c S) (x.append (y.append z))=y := by
  apply Placement.Tapes.ext'
  all_goals intro i; simp [Placement.extra,placement,Tapes.append]

omit [Fact q.Prime] in
private theorem combined (x y : Tapes c q) (z : Tapes (c+S) q) :
    Placement.combine (placement c S) (x.append z) y=x.append (y.append z) := by
  simpa only [active,extra] using Placement.view (placement c S) (x.append (y.append z))

def bank (xs ys : ℕ → List (Fin q)) (fs : Fin c → ℤ → Fin (q+4)) (ps : Fin c → ℤ) :
    Tapes (c+(c+(c+S))) q :=
  (controls xs).append (RawLinearCombinationFieldFamily.bank (S:=S) ys fs ps)

def program (hc : 0<c) (es : Fin c → Expr c) (hs : ∀ i,Size (es i)≤S) :=
  seq (Placement.placed (RawLinearCombinationFieldFamily.compile (q:=q) hc es hs (List.finRange c)).2 (placement c S))
    (RawLinearCombinationCleanup.prepend
      (RawLinearCombinationFieldFamily.compile (q:=q) hc es hs (List.finRange c)).2 c)

def output (es : Fin c → Expr c) (xs ys : ℕ → List (Fin q))
    (fs : Fin c → ℤ → Fin (q+4)) (ps : Fin c → ℤ) :=
  bank (S:=S) xs ys
    (fun i => putWord (fs i) (ps i)
      (DelimitedRadixRecord.complex (RadixLinearCombination.result (es i).erase xs)
        (RadixLinearCombination.result (es i).erase ys)))
    (fun i => ps i+(RadixLinearCombination.result (es i).erase xs).length+
      (RadixLinearCombination.result (es i).erase ys).length+2)

/-- Actual fixed expression programs emit every real-plus-imaginary output
record. Arithmetic storage is shared across all wires and both components. -/
theorem runs (hc : 0<c) (es : Fin c → Expr c) (hs : ∀ i,Size (es i)≤S)
    (xs ys : ℕ → List (Fin q)) (w : ℕ)
    (hx : ∀ j,(xs j).length=w) (hy : ∀ j,(ys j).length=w)
    (fs : Fin c → ℤ → Fin (q+4)) (ps : Fin c → ℤ) :
    HoareTime (program hc es hs) (fun v => v=bank (S:=S) xs ys fs ps)
      (fun v => v=output (S:=S) es xs ys fs ps)
      (2*RawLinearCombinationFieldFamily.cost es (List.finRange c) w+1) := by
  let fr := fun i => putWord (fs i) (ps i)
    (DelimitedRadixRecord.field (RadixLinearCombination.result (es i).erase xs))
  let pr := fun i => ps i+(RadixLinearCombination.result (es i).erase xs).length+1
  have hr := RawLinearCombinationFieldFamily.runs hc es hs (List.finRange c) xs w hx fs ps
  rw [RawLinearCombinationFieldFamily.execute_all] at hr
  have ha : Placement.active (placement c S) (bank (S:=S) xs ys fs ps)=
      RawLinearCombinationFieldFamily.bank xs fs ps := active _ _ _
  have hreal := Placement.hoare_at hr (placement c S) (bank (S:=S) xs ys fs ps) ha
  have h0 : HoareTime
      (Placement.placed (RawLinearCombinationFieldFamily.compile (q:=q) hc es hs (List.finRange c)).2 (placement c S))
      (fun v => v=bank (S:=S) xs ys fs ps) (fun v => v=bank (S:=S) xs ys fr pr)
      (RawLinearCombinationFieldFamily.cost es (List.finRange c) w) := by
    apply hreal.consequence (fun _ h => h) _ le_rfl
    rintro v ⟨small,rfl,rfl⟩
    simp only [Placement.replace,bank,RawLinearCombinationFieldFamily.bank,extra,combined]
    rfl
  have hi := RawLinearCombinationFieldFamily.runs hc es hs (List.finRange c) ys w hy fr pr
  rw [RawLinearCombinationFieldFamily.execute_all] at hi
  have h1 := RawLinearCombinationCleanup.prepend_runs _ _ _ (controls (c:=c) xs) hi
  have hend :
      (controls xs).append (RawLinearCombinationFieldFamily.bank (S:=S) ys
        (fun i => putWord (fr i) (pr i)
          (DelimitedRadixRecord.field (RadixLinearCombination.result (es i).erase ys)))
        (fun i => pr i+(RadixLinearCombination.result (es i).erase ys).length+1))=
      output (S:=S) es xs ys fs ps := by
    have hf : (fun i => putWord (fr i) (pr i)
        (DelimitedRadixRecord.field (RadixLinearCombination.result (es i).erase ys)))=
        (fun i => putWord (fs i) (ps i)
          (DelimitedRadixRecord.complex (RadixLinearCombination.result (es i).erase xs)
            (RadixLinearCombination.result (es i).erase ys))) := by
      funext i
      dsimp only [fr,pr]
      rw [show ps i+((RadixLinearCombination.result (es i).erase xs).length:ℤ)+1=
          ps i+(DelimitedRadixRecord.field (RadixLinearCombination.result (es i).erase xs)).length by
        simp [DelimitedRadixRecord.field_length]; omega,putWord_append_forward]
      rfl
    have hp : (fun i => pr i+(RadixLinearCombination.result (es i).erase ys).length+1)=
        (fun i => ps i+(RadixLinearCombination.result (es i).erase xs).length+
          (RadixLinearCombination.result (es i).erase ys).length+2) := by
      funext i
      dsimp only [pr]
      omega
    rw [hf,hp]
    rfl
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h.trans hend) (by omega)

end
end IntegerMultBounds.Machine.RawLinearCombinationComplexFamily
