import IntegerMultBounds.Machine.RawLinearCombinationFieldEmit

/-! A finite family of compiled expressions shares the same retained controls
and blank private arithmetic bank. Each fixed output wire receives its actual
field; no arithmetic program or field result is supplied as a callback. -/
namespace IntegerMultBounds.Machine.RawLinearCombinationFieldFamily
noncomputable section
open RadixLinearCombinationRefresh (Expr Size controls)
open SharedPlacementAlphabet (setTape)
variable {c q S : ℕ} [Fact q.Prime]

abbrev count (c S : ℕ) := c+(c+S)
def destination (S : ℕ) (i : Fin c) : Fin (count c S) := Fin.natAdd c (Fin.castAdd S i)

def slot (e : Expr c) (hs : Size e≤S) (target : Fin c) : Fin (RawLinearCombinationFieldEmit.count e) → Fin (count c S) :=
  fun i => if hi : i.val<c then ⟨i.val,by unfold count; omega⟩
    else if hj : i.val<c+Size e then ⟨2*c+(i.val-c),by have := i.isLt; unfold count; omega⟩
    else destination S target

theorem slot_injective (e : Expr c) (hs : Size e≤S) (target : Fin c) :
    Function.Injective (slot e hs target) := by
  intro i j he
  have hv := congrArg Fin.val he
  have hi := i.isLt
  have hj := j.isLt
  have ht := target.isLt
  apply Fin.ext
  simp only [slot] at hv
  dsimp only [RawLinearCombinationFieldEmit.count] at hi hj
  split_ifs at hv <;> simp only [destination,Fin.val_natAdd,Fin.val_castAdd] at hv <;> omega

def placement (e : Expr c) (hs : Size e≤S) (target : Fin c) :=
  InjectivePlacement.placement (slot e hs target) (slot_injective e hs target)
    (show RawLinearCombinationFieldEmit.count e+(count c S-RawLinearCombinationFieldEmit.count e)=count c S by
      have ht := target.isLt
      unfold count RawLinearCombinationFieldEmit.count
      omega)

theorem slot_control (e : Expr c) (hs : Size e≤S) (target i : Fin c) :
    slot e hs target (Fin.castAdd 1 (Fin.castAdd (Size e) i))=Fin.castAdd (c+S) i := by
  simp only [slot,Fin.val_castAdd,dite_eq_left i.isLt]
  rfl

theorem slot_work (e : Expr c) (hs : Size e≤S) (target : Fin c) (i : Fin (Size e)) :
    slot e hs target (Fin.castAdd 1 (Fin.natAdd c i))=
      Fin.natAdd c (Fin.natAdd c (Fin.castLE hs i)) := by
  have h0 : ¬c+i.val<c := by omega
  have h1 : c+i.val<c+Size e := by have := i.isLt; omega
  simp only [slot,Fin.val_castAdd,Fin.val_natAdd,dite_eq_right h0,dite_eq_left h1]
  apply Fin.ext
  dsimp
  omega

theorem slot_dest (e : Expr c) (hs : Size e≤S) (target : Fin c) :
    slot e hs target (Fin.natAdd (c+Size e) (0 : Fin 1))=destination S target := by
  have h0 : ¬c+Size e<c := by omega
  simp [slot,h0]

def bank (xs : ℕ → List (Fin q)) (fs : Fin c → ℤ → Fin (q+4)) (ps : Fin c → ℤ) : Tapes (count c S) q :=
  (controls xs).append ((⟨ps,fs⟩ : Tapes c q).append (RadixLinearCombinationBootstrap.empty S))

def emit (e : Expr c) (hs : Size e≤S) (target : Fin c) :=
  Placement.placed (RawLinearCombinationFieldEmit.program (q:=q) e) (placement e hs target)

omit [Fact q.Prime] in
private theorem active (e : Expr c) (hs : Size e≤S) (target : Fin c)
    (xs : ℕ → List (Fin q)) (fs : Fin c → ℤ → Fin (q+4)) (ps : Fin c → ℤ) :
    Placement.active (placement e hs target) (bank xs fs ps)=
      RawLinearCombinationFieldEmit.input e xs (fs target) (ps target) := by
  rw [placement,InjectivePlacement.active_bank]
  apply Placement.Tapes.ext'
  all_goals
    intro i
    dsimp only
    induction i using Fin.addCases (m:=c+Size e) (n:=1) with
    | right i => fin_cases i; dsimp only; simp only [Fin.mk_zero]; rw [slot_dest e hs target]; simp [bank,RawLinearCombinationFieldEmit.input,Tapes.append,MarkedWordCleanup.one,destination]
    | left i =>
      induction i using Fin.addCases (m:=c) (n:=Size e) with
      | left i => rw [slot_control]; simp [bank,RawLinearCombinationFieldEmit.input,RawLinearCombination.input,Tapes.append]
      | right i => rw [slot_work]; simp [bank,RawLinearCombinationFieldEmit.input,RawLinearCombination.input,
          RadixLinearCombinationBootstrap.empty,Tapes.append]

private theorem replacement (e : Expr c) (hs : Size e≤S) (target : Fin c)
    (xs : ℕ → List (Fin q)) (fs : Fin c → ℤ → Fin (q+4)) (ps : Fin c → ℤ) :
    Placement.replace (placement e hs target) (bank xs fs ps)
      (RawLinearCombinationFieldEmit.output e xs (fs target) (ps target))=
    setTape (bank xs fs ps) (destination S target)
      (putWord (fs target) (ps target) (DelimitedRadixRecord.field (RadixLinearCombination.result e.erase xs)))
      (ps target+(RadixLinearCombination.result e.erase xs).length+1) := by
  apply Placement.Tapes.ext'
  all_goals
    intro i
    by_cases hi : ∃ j,slot e hs target j=i
    · obtain ⟨j,rfl⟩ := hi
      first
        | rw [placement,InjectivePlacement.replace_head_slot]
        | rw [placement,InjectivePlacement.replace_tape_slot]
      induction j using Fin.addCases (m:=c+Size e) (n:=1) with
      | right j => fin_cases j; dsimp only; simp only [Fin.mk_zero]; rw [slot_dest e hs target]; simp [setTape,RawLinearCombinationFieldEmit.output,RawLinearCombinationFieldEmit.input,Tapes.append,MarkedWordCleanup.one]
      | left j =>
        induction j using Fin.addCases (m:=c) (n:=Size e) with
        | left j =>
          rw [slot_control]
          have hn : (Fin.castAdd (c+S) j : Fin (count c S))≠destination S target := by
            intro h; have hh := congrArg Fin.val h; have := j.isLt; dsimp [destination] at hh; omega
          simp [setTape,Function.update_of_ne hn,bank,RawLinearCombinationFieldEmit.output,
            RawLinearCombinationFieldEmit.input,RawLinearCombination.input,Tapes.append]
        | right j =>
          rw [slot_work]
          have hn : (Fin.natAdd c (Fin.natAdd c (Fin.castLE hs j)) : Fin (count c S))≠destination S target := by
            intro h; have hh := congrArg Fin.val h; have := target.isLt; dsimp [destination] at hh; omega
          simp [setTape,Function.update_of_ne hn,bank,RawLinearCombinationFieldEmit.output,
            RawLinearCombinationFieldEmit.input,RawLinearCombination.input,RadixLinearCombinationBootstrap.empty,Tapes.append]
    · have hn : i≠destination S target := by
        intro h
        apply hi
        exact ⟨RawLinearCombinationFieldEmit.destSlot e,(slot_dest e hs target).trans h.symm⟩
      first
        | rw [placement,InjectivePlacement.replace_head_other _ _ _ _ _ _ (fun j hj => hi ⟨j,hj⟩)]
        | rw [placement,InjectivePlacement.replace_tape_other _ _ _ _ _ _ (fun j hj => hi ⟨j,hj⟩)]
      simp [setTape,Function.update_of_ne hn]

theorem emit_runs (e : Expr c) (hs : Size e≤S) (target : Fin c)
    (xs : ℕ → List (Fin q)) (w : ℕ) (hw : ∀ j,(xs j).length=w)
    (fs : Fin c → ℤ → Fin (q+4)) (ps : Fin c → ℤ) :
    HoareTime (emit e hs target) (fun v => v=bank xs fs ps)
      (fun v => v=setTape (bank xs fs ps) (destination S target)
        (putWord (fs target) (ps target) (DelimitedRadixRecord.field (RadixLinearCombination.result e.erase xs)))
        (ps target+(RadixLinearCombination.result e.erase xs).length+1))
      (RawLinearCombination.cost e w+2*w+7) := by
  apply (Placement.hoare_at (RawLinearCombinationFieldEmit.runs e xs w hw (fs target) (ps target))
    (placement e hs target) (bank xs fs ps) (active e hs target xs fs ps)).consequence
    (fun _ h => h) _ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  exact replacement e hs target xs fs ps

omit [Fact q.Prime] in
theorem bank_write (xs : ℕ → List (Fin q)) (fs : Fin c → ℤ → Fin (q+4)) (ps : Fin c → ℤ)
    (target : Fin c) (f : ℤ → Fin (q+4)) (p : ℤ) :
    setTape (bank (S:=S) xs fs ps) (destination S target) f p=
      bank xs (Function.update fs target f) (Function.update ps target p) := by
  apply Placement.Tapes.ext'
  all_goals
    intro i
    induction i using Fin.addCases (m:=c) (n:=c+S) with
    | left i =>
      have hn : (Fin.castAdd (c+S) i : Fin (count c S))≠destination S target := by
        intro h; have hh := congrArg Fin.val h; have := i.isLt; dsimp [destination] at hh; omega
      simp [setTape,bank,Function.update_of_ne hn,Tapes.append]
    | right i =>
      induction i using Fin.addCases (m:=c) (n:=S) with
      | left i => simp [setTape,bank,destination,Tapes.append,Function.update_apply]
      | right i =>
        have hn : (Fin.natAdd c (Fin.natAdd c i) : Fin (count c S))≠destination S target := by
          intro h; have hh := congrArg Fin.val h; have := target.isLt; dsimp [destination] at hh; omega
        simp [setTape,bank,Function.update_of_ne hn,Tapes.append]

def next (e : Expr c) (xs : ℕ → List (Fin q)) (target : Fin c)
    (fs : Fin c → ℤ → Fin (q+4)) (ps : Fin c → ℤ) :=
  (Function.update fs target
      (putWord (fs target) (ps target) (DelimitedRadixRecord.field (RadixLinearCombination.result e.erase xs))),
    Function.update ps target (ps target+(RadixLinearCombination.result e.erase xs).length+1))

def execute (es : Fin c → Expr c) (xs : ℕ → List (Fin q)) :
    List (Fin c) → (Fin c → ℤ → Fin (q+4)) → (Fin c → ℤ) →
      (Fin c → ℤ → Fin (q+4)) × (Fin c → ℤ)
  | [],fs,ps => (fs,ps)
  | i::ops,fs,ps => let state := next (es i) xs i fs ps
      execute es xs ops state.1 state.2

theorem execute_frame (es : Fin c → Expr c) (xs : ℕ → List (Fin q))
    (ops : List (Fin c)) (fs : Fin c → ℤ → Fin (q+4)) (ps : Fin c → ℤ)
    (i : Fin c) (hi : i∉ops) :
    (execute es xs ops fs ps).1 i=fs i ∧ (execute es xs ops fs ps).2 i=ps i := by
  induction ops generalizing fs ps with
  | nil => exact ⟨rfl,rfl⟩
  | cons j ops ih =>
    have hn : i≠j := fun h => hi (List.mem_cons.mpr (Or.inl h))
    have ht : i∉ops := fun h => hi (List.mem_cons_of_mem _ h)
    simpa only [execute,next,Function.update_of_ne hn] using
      ih (next (es j) xs j fs ps).1 (next (es j) xs j fs ps).2 ht

theorem execute_slot (es : Fin c → Expr c) (xs : ℕ → List (Fin q))
    (ops : List (Fin c)) (hu : ops.Nodup) (fs : Fin c → ℤ → Fin (q+4)) (ps : Fin c → ℤ)
    (i : Fin c) (hi : i∈ops) :
    (execute es xs ops fs ps).1 i=
      putWord (fs i) (ps i) (DelimitedRadixRecord.field (RadixLinearCombination.result (es i).erase xs)) ∧
    (execute es xs ops fs ps).2 i=ps i+(RadixLinearCombination.result (es i).erase xs).length+1 := by
  induction ops generalizing fs ps with
  | nil => exact (List.not_mem_nil hi).elim
  | cons j ops ih =>
    have hh := List.nodup_cons.mp hu
    rcases List.mem_cons.mp hi with rfl | hi
    · simpa only [execute,next,Function.update_self] using
        execute_frame es xs ops (next (es i) xs i fs ps).1 (next (es i) xs i fs ps).2 i hh.1
    · have hn : i≠j := fun he => hh.1 (he ▸ hi)
      simpa only [execute,next,Function.update_of_ne hn] using
        ih hh.2 (next (es j) xs j fs ps).1 (next (es j) xs j fs ps).2 hi

theorem execute_all (es : Fin c → Expr c) (xs : ℕ → List (Fin q))
    (fs : Fin c → ℤ → Fin (q+4)) (ps : Fin c → ℤ) :
    execute es xs (List.finRange c) fs ps=
      (fun i => putWord (fs i) (ps i) (DelimitedRadixRecord.field (RadixLinearCombination.result (es i).erase xs)),
        fun i => ps i+(RadixLinearCombination.result (es i).erase xs).length+1) := by
  apply Prod.ext
  · funext i
    exact (execute_slot es xs (List.finRange c) (List.nodup_finRange c) fs ps i (List.mem_finRange i)).1
  · funext i
    exact (execute_slot es xs (List.finRange c) (List.nodup_finRange c) fs ps i (List.mem_finRange i)).2

def compile (hc : 0<c) (es : Fin c → Expr c) (hs : ∀ i,Size (es i)≤S) :
    List (Fin c) → Σ n,Program (count c S) n q
  | [] => ⟨1,skip (count c S) q (by unfold count; omega)⟩
  | i::ops => ⟨_,seq (emit (es i) (hs i) i) (compile hc es hs ops).2⟩

def cost (es : Fin c → Expr c) (ops : List (Fin c)) (w : ℕ) :=
  (ops.map (fun i => RawLinearCombination.cost (es i) w+2*w+8)).sum

theorem cost_le (es : Fin c → Expr c) (ops : List (Fin c)) (w B : ℕ)
    (hB : ∀ i∈ops,RawLinearCombination.cost (es i) w≤B) :
    cost es ops w≤ops.length*(B+2*w+8) := by
  induction ops with
  | nil => simp [cost]
  | cons i ops ih =>
    have h0 := hB i List.mem_cons_self
    have ht := ih (fun j hj => hB j (List.mem_cons_of_mem _ hj))
    simp only [cost,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

/-- Every finite output list executes its actual expression programs in the
listed order, reusing blank workspace and retaining all original sources. -/
theorem runs (hc : 0<c) (es : Fin c → Expr c) (hs : ∀ i,Size (es i)≤S)
    (ops : List (Fin c)) (xs : ℕ → List (Fin q)) (w : ℕ) (hw : ∀ j,(xs j).length=w)
    (fs : Fin c → ℤ → Fin (q+4)) (ps : Fin c → ℤ) :
    HoareTime (compile hc es hs ops).2 (fun v => v=bank xs fs ps)
      (fun v => v=bank xs (execute es xs ops fs ps).1 (execute es xs ops fs ps).2)
      (cost es ops w) := by
  induction ops generalizing fs ps with
  | nil => exact skip_hoare (by unfold count; omega) (bank xs fs ps)
  | cons i ops ih =>
    have h0 := (emit_runs (es i) (hs i) i xs w hw fs ps).consequence (fun _ h => h)
      (fun _ h => h.trans (bank_write xs fs ps i _ _)) le_rfl
    have ht := ih (next (es i) xs i fs ps).1 (next (es i) xs i fs ps).2
    exact (h0.seq ht).consequence (fun _ h => h) (fun _ h => h)
      (by simp only [cost,List.map_cons,List.sum_cons]; omega)

end
end IntegerMultBounds.Machine.RawLinearCombinationFieldFamily
