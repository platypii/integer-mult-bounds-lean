module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackMatrixRead
public import IntegerMultBounds.MathlibTM2.Cover.LabelRing
public import IntegerMultBounds.Networks.Shared50ModularControl

/-! Dispatch from fixed-width binary parent weights stored on the archive tape. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Cover Cover.Fallback
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)

/-- Read a weight most significant bit first while moving it back to its original tape. -/
noncomputable def residueSymbol (n : ℕ) : Fin (prime+4) :=
  ⟨n % prime, (Nat.mod_lt _ prime_prime.pos).trans (by omega)⟩

noncomputable def residueStep (s x : Fin (prime+4)) : Fin (prime+4) :=
  residueSymbol (2*s.val+(symBit x).toNat)

noncomputable def residueAuto : Auto prime 1 1 :=
  ⟨residueSymbol 0, fun s col => (residueStep s (col 0),col)⟩

private theorem residueFold (H n : ℕ) (fits : n < 2^H) :
    (binSyms H n).reverse.foldl residueStep (residueSymbol 0) = residueSymbol n := by
  induction H generalizing n with
  | zero =>
    have : n = 0 := by simpa using fits
    subst n
    rfl
  | succ H ih =>
    rw [binSyms_succ,List.reverse_cons,List.foldl_append,ih (n/2) (by rw [pow_succ] at fits; omega)]
    apply Fin.ext
    simp only [List.foldl_cons,List.foldl_nil,residueStep,residueSymbol,symBit_bitSymbol,Nat.testBit_zero]
    rw [Nat.add_mod,Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> congr 1 <;> omega

private theorem residueAfter (xs : List (Fin (prime+4))) (s : Fin (prime+4)) :
    residueAuto.stateAfter xs.length s (fun _ => xs) = xs.foldl residueStep s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (residueStep s x)

noncomputable def parentWeightResidue {T Q : ℕ} {P U : Type} (word tmp state : Fin T) : Pr P T Q prime U :=
  (moveR word tmp id).seq ((Prog.act (.load (fun v => {v with scan := Function.update v.scan state (residueSymbol 0)})
    (peekR tmp))).seq (colLoop (fun _ : Fin 1 => tmp) (fun _ => word) state residueAuto))

theorem parentWeightResidue_exec {T Q w : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (word tmp state : Fin T) (apart : word ≠ tmp) (scratch : tmp ≠ state)
    (H : ℕ) (x : ZMod (prime^(w+1))) (fits : x.val < 2^H) (v : HS T Q prime U) (S : Stacks T prime)
    (encoded : S.R word = binSyms H x.val) (free : S.R tmp = []) :
    ∃ z, z.user = v.user ∧ (z.scan state).val = (LabelRing.res prime (w+1) (by omega) x).val ∧
      Exec body (parentWeightResidue word tmp state) (mk v S) (5*H+4) (mk z S) := by
  obtain ⟨y,user,move⟩ := moveR_exec body word tmp apart id v S
  let B : Stacks T prime := {S with R := movedR S.R word tmp id (S.R word)}
  let xs := (binSyms (A := prime) H x.val).reverse
  have source : B.R tmp = xs := by simp [B,movedR,encoded,free,xs]
  have empty : B.R word = [] := by simp [B,movedR,apart]
  let u := {y with scan := Function.update y.scan state (residueSymbol 0), flag := (B.R tmp).head?.isSome}
  obtain ⟨z,R,keep,read,run,drained,restored,off⟩ := colLoop_exec body
    (ins := fun _ : Fin 1 => tmp) (outs := fun _ : Fin 1 => word)
    (fun _ _ _ => Subsingleton.elim ..) (fun _ _ _ => Subsingleton.elim ..) (fun _ _ => apart.symm)
    (fun _ => scratch) residueAuto (fun _ _ => rfl) xs.length (fun _ => xs) u B
    (fun _ => rfl) (fun _ => source) (by simp [u,source])
  have final : {B with R := R} = S := by
    apply Stacks.ext <;> try rfl
    funext j
    by_cases a : j = word
    · subst j
      simpa [empty,xs,encoded] using restored 0
    by_cases b : j = tmp
    · subst j
      simpa [free] using drained 0
    change R j = S.R j
    rw [off j (by simpa using b) (by simpa using a)]
    simp [B,movedR,a,b]
  refine ⟨z,keep.trans user,?_,?_⟩
  · rw [read,residueAfter]
    simp only [u,Function.update_self]
    rw [residueFold H x.val fits]
    letI : NeZero (prime^(w+1)) := ⟨(pow_pos prime_prime.pos _).ne'⟩
    simp only [residueSymbol,LabelRing.res,ZMod.castHom_apply,ZMod.cast_eq_val,ZMod.val_natCast]
  · unfold parentWeightResidue
    exact (Exec.seq move (Exec.seq (Exec.act (body := body) (.load
      (fun v => {v with scan := Function.update v.scan state (residueSymbol 0)}) (peekR tmp)) (mk y B)) run)).cast
      (by change 2*(S.R word).length+2+(1+(3*xs.length+1)) = 5*H+4; rw [encoded,length_binSyms]; simp [xs]; omega)
      (by rw [final])

/-- Select one of the packed parent weights with the runtime width register,
then reduce its bits into a single control symbol. -/
noncomputable def archivedWeightResidue {T Q : ℕ} {P U : Type} (i : ℕ) (r : Fin 7 ↪ Fin T) : Pr P T Q prime U :=
  (readMatrixWord i r).seq (parentWeightResidue (r 3) (r 4) (r 5))

theorem archivedWeightResidue_exec {T Q w m : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 7 ↪ Fin T) (parent : Fin m → ZMod (prime^(w+1))) (i : Fin m)
    (v : HS T Q prime U) (S : Stacks T prime) (tail : List (Fin (prime+4)))
    (archive : S.R (r 2) = (List.ofFn fun j => binSyms (prime^(w+1)).size (parent j).val).flatten ++ tail)
    (width : (S.R (r 1)).length = (prime^(w+1)).size)
    (fresh : ∀ j : Fin 7, j ≠ 1 → j ≠ 2 → S.R (r j) = []) :
    let H := (prime^(w+1)).size
    ∃ z, z.user = v.user ∧ (z.scan (r 5)).val = (LabelRing.res prime (w+1) (by omega) (parent i)).val ∧
      Exec body (archivedWeightResidue i r) (mk v S) (8*(i.val*H)+19*H+26)
        (mk z {S with R := Function.update S.R (r 3) (binSyms H (parent i).val)}) := by
  intro H
  letI : NeZero (prime^(w+1)) := ⟨(pow_pos prime_prime.pos _).ne'⟩
  let weights : Matrix (Fin 1) (Fin m) (ZMod (prime^(w+1))) := fun _ => parent
  have packed : S.R (r 2) = matrixWords prime H weights ++ tail := by
    simpa [matrixWords,List.ofFn_succ,weights,H] using archive
  obtain ⟨y,user,copy⟩ := readMatrixWord_exec body r weights 0 i H v S tail packed width
    (fun j hj => fresh j (by rcases hj with h|h <;> omega) (by rcases hj with h|h <;> omega))
  simp only [Fin.val_zero,Nat.zero_mul,Nat.zero_add,weights,fresh 3 (by decide) (by decide),List.append_nil] at copy
  let B := {S with R := Function.update S.R (r 3) (binSyms H (parent i).val)}
  obtain ⟨z,keep,res,run⟩ := parentWeightResidue_exec body (r 3) (r 4) (r 5)
    (r.injective.ne (by decide)) (r.injective.ne (by decide)) H (parent i)
    ((parent i).val_lt.trans (Nat.lt_size_self _)) y B
    (Function.update_self ..) (by simp [B,r.injective.eq_iff,fresh 4 (by decide) (by decide)])
  exact ⟨z,keep.trans user,res,(Exec.seq copy run).cast (by omega) rfl⟩

/-- Branch on a control symbol by bisecting its possible values. -/
def residueCases {T Q : ℕ} {P U : Type} (state : Fin T) (branch : ℕ → Pr P T Q prime U) :
    ℕ → ℕ → Pr P T Q prime U
  | 0, lo => branch lo
  | n+1, lo => .cond (fun v => decide ((v.scan state).val < lo+2^n))
      (residueCases state branch n lo) (residueCases state branch n (lo+2^n))

private theorem residueCases_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (state : Fin T) (branch : ℕ → Pr P T Q prime U) (v : HS T Q prime U) (S : Stacks T prime)
    (n lo t : ℕ) (F : Store (HΓ (T := T) prime) (HS T Q prime U))
    (lower : lo ≤ (v.scan state).val) (upper : (v.scan state).val < lo+2^n)
    (run : Exec body (branch (v.scan state).val) (mk v S) t F) :
    Exec body (residueCases state branch n lo) (mk v S) (t+n) F := by
  induction n generalizing lo with
  | zero =>
    have eq : lo = (v.scan state).val := by simp only [pow_zero] at upper; omega
    simpa [residueCases,eq] using run
  | succ n ih =>
    rw [pow_succ] at upper
    by_cases left : (v.scan state).val < lo+2^n
    · exact Exec.cond_true (decide_eq_true left) (ih lo lower left)
    · exact Exec.cond_false (decide_eq_false left) (ih (lo+2^n) (by omega) (by omega))

noncomputable def withArchivedWeight {T Q : ℕ} {P U : Type} (i : ℕ) (r : Fin 7 ↪ Fin T)
    (branch : ZMod prime → Pr P T Q prime U) : Pr P T Q prime U :=
  (archivedWeightResidue i r).seq (residueCases (r 5) (fun a => (Node.uclear (r 3)).seq (branch a)) prime.size 0)

/-- Dispatch from a packed weight and restore every stack before the selected program starts. -/
theorem withArchivedWeight_exec {T Q w m : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 7 ↪ Fin T) (parent : Fin m → ZMod (prime^(w+1))) (i : Fin m)
    (branch : ZMod prime → Pr P T Q prime U) (v : HS T Q prime U) (S : Stacks T prime)
    (tail : List (Fin (prime+4)))
    (archive : S.R (r 2) = (List.ofFn fun j => binSyms (prime^(w+1)).size (parent j).val).flatten ++ tail)
    (width : (S.R (r 1)).length = (prime^(w+1)).size)
    (fresh : ∀ j : Fin 7, j ≠ 1 → j ≠ 2 → S.R (r j) = []) :
    let H := (prime^(w+1)).size
    ∃ u : HS T Q prime U, u.user = v.user ∧ ∀ F t,
      Exec body (branch (LabelRing.res prime (w+1) (by omega) (parent i))) (mk u S) t F →
      Exec body (withArchivedWeight i r branch) (mk v S) (8*(i.val*H)+21*H+28+prime.size+t) F := by
  intro H
  obtain ⟨y,user,selected,read⟩ := archivedWeightResidue_exec body r parent i v S tail archive width fresh
  let B := {S with R := Function.update S.R (r 3) (binSyms H (parent i).val)}
  obtain ⟨u,keep,clear⟩ := Node.uclear_exec body (r 3) y B
  have restore : {B with R := Function.update B.R (r 3) []} = S := by
    apply Stacks.ext <;> try rfl
    simp [B,← fresh 3 (by decide) (by decide)]
  rw [restore,show (B.R (r 3)).length = H by simp [B]] at clear
  refine ⟨u,keep.trans user,?_⟩
  intro F t run
  letI : NeZero prime := ⟨prime_prime.ne_zero⟩
  let residue := LabelRing.res prime (w+1) (by omega) (parent i)
  have symbol : (((y.scan (r 5)).val : ℕ) : ZMod prime) = residue := by rw [selected,ZMod.natCast_zmod_val]
  have small : (y.scan (r 5)).val < 0+2^prime.size := by
    rw [selected,zero_add]
    exact residue.val_lt.trans (Nat.lt_size_self prime)
  have chosen := residueCases_exec body (r 5) (fun a => (Node.uclear (r 3)).seq (branch a)) y B prime.size 0 _ F
    (Nat.zero_le _) small (Exec.seq clear (by rw [symbol]; exact run))
  exact (Exec.seq read chosen).cast (by dsimp only [H]; omega) rfl

/-- Read the requested components, keeping previously read residues in the
choice of continuation. Each component uses the same seven registers. -/
noncomputable def withParentResidues {T Q m : ℕ} {P U : Type} (r : Fin 7 ↪ Fin T)
    (branch : (Fin m → ZMod prime) → Pr P T Q prime U) :
    List (Fin m) → (Fin m → ZMod prime) → Pr P T Q prime U
  | [], weights => branch weights
  | i :: rest, weights => withArchivedWeight i r fun a =>
      withParentResidues r branch rest (Function.update weights i a)

theorem withParentResidues_exec {T Q w m : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 7 ↪ Fin T) (parent : Fin m → ZMod (prime^(w+1)))
    (branch : (Fin m → ZMod prime) → Pr P T Q prime U) (S : Stacks T prime) (tail : List (Fin (prime+4)))
    (archive : S.R (r 2) = (List.ofFn fun j => binSyms (prime^(w+1)).size (parent j).val).flatten ++ tail)
    (width : (S.R (r 1)).length = (prime^(w+1)).size)
    (fresh : ∀ j : Fin 7, j ≠ 1 → j ≠ 2 → S.R (r j) = []) :
    let H := (prime^(w+1)).size
    let weights := LabelRing.res prime (w+1) (by omega) ∘ parent
    ∀ (indices : List (Fin m)) (known : Fin m → ZMod prime), (∀ i, i ∉ indices → known i = weights i) →
      ∀ v : HS T Q prime U, ∃ u : HS T Q prime U, u.user = v.user ∧ ∀ F t,
        Exec body (branch weights) (mk u S) t F →
        Exec body (withParentResidues r branch indices known) (mk v S)
          ((indices.map fun i => 8*(i.val*H)+21*H+28+prime.size).sum+t) F := by
  intro H weights indices
  induction indices with
  | nil =>
    intro known agree v
    have eq : known = weights := funext fun i => agree i (by simp)
    exact ⟨v,rfl,fun F t run => by simpa [withParentResidues,eq] using run⟩
  | cons i rest ih =>
    intro known agree v
    let next := fun a => withParentResidues r branch rest (Function.update known i a)
    obtain ⟨y,user,read⟩ := withArchivedWeight_exec body r parent i next v S tail archive width fresh
    obtain ⟨u,keep,more⟩ := ih (Function.update known i (weights i)) (by
      intro j absent
      by_cases h : j = i
      · subst j; simp
      · rw [Function.update_of_ne h]
        exact agree j (by simp [h,absent])) y
    refine ⟨u,keep.trans user,fun F t run => ?_⟩
    simpa only [withParentResidues,List.map_cons,List.sum_cons,Nat.add_assoc] using read F _ (more F t run)

end IntegerMultBounds.MathlibTM2.M6.BitNode
