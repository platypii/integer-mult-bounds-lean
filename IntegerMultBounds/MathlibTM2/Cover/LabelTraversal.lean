module

public import IntegerMultBounds.MathlibTM2.Cover.LabelCycle

/-! Compile nested residue cycles to host programs that prepend their selector bits in order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelTraversal
noncomputable section

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Host Node LabelCycle
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Only registers satisfying the supplied predicate are read by the writer. -/
def Writes (body : P → Pr P T Q A U) (ok : Regs T A → Prop) (out : Fin T)
    (p : Pr P T Q A U) (word : List (Fin (A+4))) (c : ℕ) :=
  ∀ (u : HS T Q A U) (S : Stacks T A), ok S.R →
    ∃ u' n, u'.user = u.user ∧ n ≤ c ∧ Exec body p (mk u S) n
      (mk u' {S with R := Function.update S.R out (word ++ S.R out)})

def sequence {α : Type} (f : α → Pr P T Q A U) : List α → Pr P T Q A U
  | [] => .act .done
  | x :: xs => .seq (sequence f xs) (f x)

theorem sequence_writes {α : Type} {ok : Regs T A → Prop} {out : Fin T}
    (stable : ∀ R xs, ok R → ok (Function.update R out xs))
    {f : α → Pr P T Q A U} {word : α → List (Fin (A+4))} {c : ℕ}
    (run : ∀ x, Writes body ok out (f x) (word x) c) (xs : List α) :
    Writes body ok out (sequence f xs) (xs.flatMap word) (xs.length*c+1) := by
  induction xs with
  | nil =>
    intro u S _
    exact ⟨u, 1, rfl, by simp, by simpa [sequence, Action.run] using
      (Exec.act (body := body) (.done : Act T Q A U) (mk u S))⟩
  | cons x xs ih =>
    intro u S h
    obtain ⟨v, n, hu, hn, he⟩ := ih u S h
    obtain ⟨v', n', hu', hn', he'⟩ := run x v {S with R := Function.update S.R out (xs.flatMap word ++ S.R out)} (stable _ _ h)
    refine ⟨v', n+n', hu'.trans hu, ?_, ?_⟩
    · simp only [List.length_cons, Nat.succ_mul]; omega
    · simpa [sequence, List.append_assoc] using Exec.seq he he'

/-- Run the callback for every residue, then repeat the entire cycle for each high part. -/
def atom (count saved : Fin T) (f : ZMod prime → Pr P T Q A U) :=
  repeatBlock count saved (sequence (fun i : ℕ => f i) (List.range prime))

theorem atom_writes {ok : Regs T A → Prop} {count saved out : Fin T} (hr : [count,saved,out].Nodup)
    {H : ℕ} {f : ZMod prime → Pr P T Q A U} {word : ZMod prime → List (Fin (A+4))} {c : ℕ}
    (stable : ∀ R M : Regs T A, ok R →
      (∀ k, k ≠ count → k ≠ saved → k ≠ out → M k = R k) → ok M)
    (run : ∀ x, Writes body ok out (f x) (word x) c) :
    Writes body (fun R => ok R ∧ (R count).length = H ∧ R saved = []) out
      (atom count saved f) ((LabelSelectors.cycle H).flatMap word) (H*(prime*c+6)+4) := by
  intro u S ⟨hok, hc, hs⟩
  let xs := List.range prime
  have seqrun := sequence_writes (body := body)
    (fun R ys h => stable R (Function.update R out ys) h (fun k _ _ ho => Function.update_of_ne ho ..))
    (fun i : ℕ => run i) xs
  obtain ⟨v, n, hu, hn, he⟩ := repeat_exec body hr _ _ _ u S hs
    (fun v M hM => seqrun v M (stable _ _ hok hM))
  refine ⟨v, n, hu, ?_, ?_⟩
  · simpa [hc, xs, Nat.add_assoc] using hn
  · have rep (h : ℕ) : (LabelSelectors.cycle h).flatMap word =
        (List.replicate h ((List.range prime).flatMap fun (i : ℕ) => word (i : ZMod prime))).flatten := by
      induction h with
      | zero => simp [LabelSelectors.cycle]
      | succ h ih => simpa [LabelSelectors.cycle, List.replicate_succ, List.flatMap_map, Function.comp_def] using congrArg (((List.range prime).flatMap fun (i : ℕ) => word (i : ZMod prime)) ++ ·) ih
    simpa only [atom, hc, rep,
      List.flatMap_map, Function.comp_def, xs] using he

abbrev Pair (T : ℕ) := Fin T × Fin T

def slots (rs : List (Pair T)) := rs.flatMap fun r => [r.1, r.2]

def ready (H : ℕ) (R : Regs T A) (rs : List (Pair T)) :=
  ∀ r ∈ rs, (R r.1).length = H ∧ R r.2 = []

/-- The innermost register pair serves the least significant atom. -/
def traverse : (rs : List (Pair T)) → ((Fin rs.length → ZMod prime) → Pr P T Q A U) → Pr P T Q A U
  | [], f => f Fin.elim0
  | r :: rs, f => traverse rs (fun a => atom r.1 r.2 fun b => f (Fin.cons b a))

def time (H : ℕ) : ℕ → ℕ → ℕ
  | 0, c => c
  | k+1, c => time H k (H*(prime*c+6)+4)

theorem time_le {H : ℕ} (hH : 0 < H) (k c : ℕ) :
    time H k c ≤ (c+10*k)*(H*prime)^k := by
  induction k generalizing c with
  | zero => simp [time]
  | succ k ih =>
    apply (ih (H*(prime*c+6)+4)).trans
    rw [pow_succ, ← Nat.mul_assoc, Nat.mul_right_comm (c+10*(k+1))]
    apply Nat.mul_le_mul_right
    have hp := IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos
    have hQ := Nat.le_mul_of_pos_right H hp
    have hk := Nat.le_mul_of_pos_right k (Nat.mul_pos hH hp)
    nlinarith

theorem traverse_writes (H : ℕ) (rs : List (Pair T)) (out : Fin T)
    (hr : (slots rs ++ [out]).Nodup) (ok : Regs T A → Prop)
    (frame : ∀ R M : Regs T A, ok R → (∀ k, k ∉ slots rs → k ≠ out → M k = R k) → ok M)
    (f : (Fin rs.length → ZMod prime) → Pr P T Q A U)
    (word : (Fin rs.length → ZMod prime) → List (Fin (A+4))) (c : ℕ)
    (run : ∀ a, Writes body ok out (f a) (word a) c) :
    Writes body (fun R => ok R ∧ ready H R rs) out (traverse rs f)
      ((LabelSelectors.classes H rs.length).flatMap word) (time H rs.length c) := by
  induction rs generalizing ok c with
  | nil =>
    intro u S h
    simpa [traverse, time, LabelSelectors.classes] using run Fin.elim0 u S h.1
  | cons r rs ih =>
    change (r.1 :: r.2 :: (slots rs ++ [out])).Nodup at hr
    simp only [List.nodup_cons, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
      not_or] at hr
    obtain ⟨⟨hab, ha, hao⟩, ⟨hb, hbo⟩, ht⟩ := hr
    let ok' := fun R : Regs T A => ok R ∧ (R r.1).length = H ∧ R r.2 = []
    have f' : ∀ R M, ok' R → (∀ k, k ∉ slots rs → k ≠ out → M k = R k) → ok' M := by
      intro R M h hM
      exact ⟨frame R M h.1 (fun k hk ho => hM k (fun h => hk (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))) ho),
        (hM r.1 ha hao ▸ h.2.1), (hM r.2 hb hbo ▸ h.2.2)⟩
    have inner a := atom_writes (H := H) (out := out) (count := r.1) (saved := r.2)
      (by simp [hab, hao, hbo]) (fun R M h hM => frame R M h (fun k hk ho =>
        hM k (by rintro rfl; exact hk (by simp [slots])) (by rintro rfl; exact hk (by simp [slots])) ho))
      (fun b => run (Fin.cons b a))
    intro u S h
    have step := ih ht ok' f' _ _ _ inner u S
      ⟨⟨h.1, h.2 r (by simp)⟩, fun p hp => h.2 p (by simp [hp])⟩
    simpa only [traverse, List.length_cons, LabelSelectors.classes, List.flatMap_assoc,
      List.flatMap_map, Function.comp_def, time] using step

def emitBit (out : Fin T) (b : Bool) : Pr P T Q A U :=
  .act (.push (.rt out) (fun _ => bitSymbol b) .done)

theorem box_writes (H : ℕ) (rs : List (Pair T)) (out : Fin T) (hr : (slots rs ++ [out]).Nodup)
    (test : (Fin rs.length → ZMod prime) → Bool) :
    Writes body (fun R => ready H R rs) out (traverse rs fun a => emitBit out (test a))
      (((LabelSelectors.classes H rs.length).map test).map bitSymbol) (time H rs.length 1) := by
  have run (a) : Writes body (fun _ => True) out (emitBit out (test a)) [bitSymbol (test a)] 1 := by
    intro u S _
    exact ⟨u, 1, rfl, le_rfl, by
      simpa [emitBit, Action.run, update_rt] using
        (Exec.act (body := body) (.push (.rt out) (fun _ => bitSymbol (test a)) .done) (mk u S))⟩
  intro u S h
  simpa only [List.map_map, Function.comp_def, ← List.map_eq_flatMap] using
    traverse_writes H rs out hr _ (fun _ _ _ _ => trivial) _ _ 1 run u S ⟨trivial, h⟩

theorem recordWords_writes (m : ℕ) (f : (Fin (m*m) → ZMod prime) → List (Fin (A+4))) (rs : List (Pair T)) (hk : rs.length = m*m) (out count saved : Fin T)
    (hr : (count :: saved :: (slots rs ++ [out])).Nodup) :
    ∃ p : Pr P T Q A U, ∀ (v : RecursiveInterchangeLayout.Descriptor) (w B : ℕ),
      0 < w → v.beforeH = B*prime^(m*(w*m)) →
      Writes body (fun R => ready (prime^(w-1)) R rs ∧ R saved = [] ∧
        (R count).length = v.beforeRows*v.rows*B) out p
        (LabelSelectors.recordMap v m w f).flatten
        ((v.beforeRows*v.rows*B)*(time (prime^(w-1)) (m*m) 1+5)+4) := by
  let test := fun a : Fin rs.length → ZMod prime =>
    f (fun i => a (Fin.cast hk.symm i))
  refine ⟨repeatBlock count saved (traverse rs fun a => .act (pushWord out (test a) .done)), ?_⟩
  intro v w B hw hv u S h
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨⟨hcs, hc, hco⟩, ⟨hs, hso⟩, ht⟩ := hr
  have leaf (a) : Writes body (fun _ => True) out (.act (pushWord out (test a) .done)) (test a) 1 := by
    intro z F _
    exact ⟨z,1,rfl,le_rfl,by simpa [pushWord_run,Action.run] using Exec.act (body := body) (pushWord out (test a) .done) (mk z F)⟩
  have box := traverse_writes (body := body) (prime^(w-1)) rs out ht _ (fun _ _ _ _ => trivial) _ _ 1 leaf
  have he := repeat_exec body (count := count) (saved := saved) (out := out) (by simp [hcs,hco,hso])
    _ _ _ u S h.2.1 (fun u M hM => box u M ⟨trivial,by
      intro r hmem
      have same (k : Fin T) (hslot : k ∈ slots rs) : M.R k = S.R k :=
        hM k (by rintro rfl; contradiction) (by rintro rfl; contradiction)
          ((List.nodup_append.mp ht).2.2 k hslot out (by simp))
      rw [same r.1 (List.mem_flatMap.mpr ⟨r,hmem,by simp⟩), same r.2 (List.mem_flatMap.mpr ⟨r,hmem,by simp⟩)]
      exact h.1 r hmem⟩)
  have matchBox : (LabelSelectors.classes (prime^(w-1)) rs.length).map test =
      (LabelSelectors.classes (prime^(w-1)) (m*m)).map f := by
    have cast_map {k n : ℕ} (e : k = n) (t : (Fin n → ZMod prime) → List (Fin (A+4))) (H : ℕ) :
        (LabelSelectors.classes H k).map (fun a => t (fun i => a (Fin.cast e.symm i))) =
          (LabelSelectors.classes H n).map t := by cases e; rfl
    exact cast_map hk _ _
  simpa only [h.2.2,List.flatMap_def,matchBox,hk,LabelSelectors.recordMap_eq v m w B hw hv f,
    List.flatten_flatten,List.map_replicate] using he

theorem recordMap_writes (m : ℕ) (f : (Fin (m*m) → ZMod prime) → Bool) (rs : List (Pair T)) (hk : rs.length = m*m) (out count saved : Fin T)
    (hr : (count :: saved :: (slots rs ++ [out])).Nodup) :
    ∃ p : Pr P T Q A U, ∀ (v : RecursiveInterchangeLayout.Descriptor) (w B : ℕ),
      0 < w → v.beforeH = B*prime^(m*(w*m)) →
      Writes body (fun R => ready (prime^(w-1)) R rs ∧ R saved = [] ∧
        (R count).length = v.beforeRows*v.rows*B) out p
        ((LabelSelectors.recordMap v m w f).map bitSymbol)
        ((v.beforeRows*v.rows*B)*(time (prime^(w-1)) (m*m) 1+5)+4) := by
  simpa [LabelSelectors.recordMap,List.map_map,Function.comp_def,← List.flatMap_def,← List.map_eq_flatMap] using
    recordWords_writes (body := body) m (fun a => [bitSymbol (f a)]) rs hk out count saved hr

/-- Emit a branch bit for each physical record by testing its residue matrix. -/
theorem class_writes (m : ℕ) (branch : Matrix (Fin m) (Fin m) (ZMod prime) → Bool) (rs : List (Pair T)) (hk : rs.length = m*m) (out count saved : Fin T)
    (hr : (count :: saved :: (slots rs ++ [out])).Nodup) :
    ∃ p : Pr P T Q A U, ∀ (v : RecursiveInterchangeLayout.Descriptor) (w B : ℕ),
      0 < w → v.beforeH = B*prime^(m*(w*m)) →
      Writes body (fun R => ready (prime^(w-1)) R rs ∧ R saved = [] ∧
        (R count).length = v.beforeRows*v.rows*B) out p
        (((List.range (LabelMask.records v)).map (fun j => branch (LabelStock.residue m w 1 j))).map bitSymbol)
        ((v.beforeRows*v.rows*B)*(time (prime^(w-1)) (m*m) 1+5)+4) := by
  simpa only [LabelSelectors.recordMap, Function.comp_apply, LabelSelectors.residue_eq] using
    recordMap_writes (body := body) m (branch ∘ LabelSelectors.matrix m) rs hk out count saved hr

theorem record_writes (m : ℕ) (rs : List (Pair T)) (hk : rs.length = m*m) (out count saved : Fin T)
    (hr : (count :: saved :: (slots rs ++ [out])).Nodup) :
    ∃ p : Pr P T Q A U, ∀ (v : RecursiveInterchangeLayout.Descriptor) (w B : ℕ),
      0 < w → v.beforeH = B*prime^(m*(w*m)) →
      Writes body (fun R => ready (prime^(w-1)) R rs ∧ R saved = [] ∧
        (R count).length = v.beforeRows*v.rows*B) out p
        ((LabelMask.selectors m w (LabelMask.records v)).map bitSymbol)
        ((v.beforeRows*v.rows*B)*(time (prime^(w-1)) (m*m) 1+5)+4) := by
  simpa only [LabelSelectors.selectors_eq] using
    recordMap_writes (body := body) m (LabelSelectors.accept m) rs hk out count saved hr

end
end IntegerMultBounds.MathlibTM2.Cover.LabelTraversal
