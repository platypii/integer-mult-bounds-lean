import IntegerMultBounds.Machine.CompactComplexSourceReadyWorkspace
import IntegerMultBounds.Machine.CompactComplexScalarCountLifecycle

/-! The actual scalar lifecycle uses a dedicated fixed suffix after the shared
leaf/spectator bank. All nine public frames and both other private banks remain
available to recursive descendants; no runtime depth enters this placement. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyScalarWorkspace
noncomputable section
open CompactComplexScalarCountLifecycle (publicTapes)
open SharedBankStageInput (raw)
variable {s c q B : ℕ}
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount
  CompactComplexScalarCountLifecycle.program Networks.ComplexRank25.program

abbrev roles := CompactComplexRolePhaseSite.roleCount
abbrev permanentTapes (s c : ℕ) := CompactComplexNativeCodecFrame.permanentTapes (10+s) c
abbrev nodeTapes (s c : ℕ) := CompactComplexSourceReadyWorkspace.tapes s c
private def fixedSuffix (a b : ℕ) : ℕ :=
  Classical.choose (show ∃ n : ℕ,n=a+b from ⟨a+b,rfl⟩)
private theorem fixedSuffix_eq (a b : ℕ) : fixedSuffix a b=a+b :=
  Classical.choose_spec (show ∃ n : ℕ,n=a+b from ⟨a+b,rfl⟩)
@[irreducible] def scratch : ℕ := fixedSuffix 43
  (RawLinearCombinationComplexDenominatorPlaced.localCount
    CompactComplexScalarRowBlock.wireCount CompactComplexScalarPolynomialSequence.scratch)

theorem scratch_eq : scratch=43+RawLinearCombinationComplexDenominatorPlaced.localCount
    CompactComplexScalarRowBlock.wireCount CompactComplexScalarPolynomialSequence.scratch := by
  unfold scratch
  exact fixedSuffix_eq 43 (RawLinearCombinationComplexDenominatorPlaced.localCount
    CompactComplexScalarRowBlock.wireCount CompactComplexScalarPolynomialSequence.scratch)
abbrev activeTapes (s c : ℕ) := permanentTapes s c+scratch
abbrev tapes (s c : ℕ) := nodeTapes s c+scratch

theorem public_le : permanentTapes s c ≤ nodeTapes s c := by
  change permanentTapes s c ≤ ((permanentTapes s c+2)+7+
    CompactComplexSourceReadyWorkspace.leafTapes)+10
  exact (((Nat.le_add_right _ 2).trans (Nat.le_add_right _ 7)).trans
    (Nat.le_add_right _ _)).trans (Nat.le_add_right _ 10)

private theorem suffix_bound {P N W : ℕ} (i : Fin (P+W)) (hi : P ≤ i.val) :
    N+(i.val-P)<N+W := by have := i.isLt; omega

private def select {P N W : ℕ} (hPN : P≤N) (i : Fin (P+W)) : Fin (N+W) :=
  if h : i.val<P then ⟨i.val,lt_of_lt_of_le h (hPN.trans (Nat.le_add_right _ _))⟩
  else ⟨N+(i.val-P),suffix_bound i (Nat.le_of_not_gt h)⟩

private theorem select_injective {P N W : ℕ} (hPN : P≤N) :
    Function.Injective (select (W:=W) hPN) := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  unfold select at hv
  split_ifs at hv <;> simp only at hv <;> omega

private theorem placement_size {P N W : ℕ} (hPN : P≤N) :
    (P+W)+(N-P)=N+W := by omega

def slot (i : Fin (activeTapes s c)) : Fin (tapes s c) := select public_le i

theorem slot_injective : Function.Injective (slot (s:=s) (c:=c)) :=
  select_injective public_le

def placement (s c : ℕ) := InjectivePlacement.placement (slot (s:=s) (c:=c)) slot_injective
  (placement_size (W:=scratch) public_le)

def permanent (v : Tapes (nodeTapes s c) 2) : Tapes (permanentTapes s c) 2 :=
  ⟨fun i => v.head ⟨i.val,lt_of_lt_of_le i.isLt public_le⟩,
   fun i => v.tape ⟨i.val,lt_of_lt_of_le i.isLt public_le⟩⟩

def ready (v : Tapes (nodeTapes s c) 2) := v.append (SharedBank.empty scratch 2)

private theorem select_public {P N W : ℕ} (hPN : P≤N) (i : Fin P) :
    select (W:=W) hPN (Fin.castAdd W i)=
      Fin.castAdd W (⟨i.val,lt_of_lt_of_le i.isLt hPN⟩ : Fin N) := by
  apply Fin.ext
  simp [select,i.isLt]

private theorem select_private {P N W : ℕ} (hPN : P≤N) (i : Fin W) :
    select hPN (Fin.natAdd P i)=Fin.natAdd N i := by
  apply Fin.ext
  simp [select]

private theorem slot_public (i : Fin (permanentTapes s c)) :
    slot (s:=s) (Fin.castAdd scratch i)=
      Fin.castAdd scratch (⟨i.val,lt_of_lt_of_le i.isLt public_le⟩ : Fin (nodeTapes s c)) :=
  select_public public_le i

private theorem slot_private (i : Fin scratch) :
    slot (s:=s) (Fin.natAdd (permanentTapes s c) i)=Fin.natAdd (nodeTapes s c) i :=
  select_private public_le i

private theorem select_frame {P N W : ℕ} (hPN : P≤N) (i : Fin N) (hi : P ≤ i.val) :
    ¬∃ j,select (W:=W) hPN j=Fin.castAdd W i := by
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  unfold select at hv
  split_ifs at hv <;> simp only [Fin.val_castAdd] at hv <;> have := i.isLt <;> omega

/-- Every actual shared node bank supplies the scalar's original permanent
input directly, while the only newly borrowed tapes are the fixed suffix. -/
private theorem active_raw {P N W : ℕ} (hPN : P≤N) (v : Tapes N 2) :
    Placement.active (InjectivePlacement.placement (select (W:=W) hPN)
      (select_injective hPN) (placement_size hPN)) (v.append (SharedBank.empty W 2))=
    raw (⟨fun i => v.head ⟨i.val,lt_of_lt_of_le i.isLt hPN⟩,
      fun i => v.tape ⟨i.val,lt_of_lt_of_le i.isLt hPN⟩⟩ : Tapes P 2) (P+W) := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    induction i using Fin.addCases (m:=P) (n:=W) with
    | left i => simp only [InjectivePlacement.active_slot,
        select_public,Tapes.append,Fin.addCases_left,Fin.val_castAdd,
        dite_eq_left i.isLt]
    | right i => simp only [InjectivePlacement.active_slot,
        select_private,Tapes.append,Fin.addCases_right,SharedBank.empty,
        Fin.val_natAdd,Nat.not_lt.mpr (Nat.le_add_right _ _),dite_false]

theorem active_ready (v : Tapes (nodeTapes s c) 2) :
    Placement.active (placement s c) (ready v)=raw (permanent v) (activeTapes s c) :=
  active_raw public_le v

/-- Replace only the original permanent caller prefix. All source-ready
controller, leaf and spectator work remains literal and unchanged. -/
private def prefixOutput {P N : ℕ} (v : Tapes N 2) (w : Tapes P 2) : Tapes N 2 :=
  ⟨fun i => if h : i.val<P then w.head ⟨i.val,h⟩ else v.head i,
   fun i => if h : i.val<P then w.tape ⟨i.val,h⟩ else v.tape i⟩

def output (v : Tapes (nodeTapes s c) 2) (w : Tapes (permanentTapes s c) 2) :
    Tapes (nodeTapes s c) 2 := prefixOutput v w

theorem output_public (v : Tapes (nodeTapes s c) 2)
    (w : Tapes (permanentTapes s c) 2) (i : Fin (permanentTapes s c)) :
    (output v w).head ⟨i.val,lt_of_lt_of_le i.isLt public_le⟩=w.head i ∧
    (output v w).tape ⟨i.val,lt_of_lt_of_le i.isLt public_le⟩=w.tape i := by
  simp [output,prefixOutput,i.isLt]

theorem permanent_output (v : Tapes (nodeTapes s c) 2)
    (w : Tapes (permanentTapes s c) 2) : permanent (output v w)=w := by
  apply congrArg₂ Tapes.mk
  · funext i
    exact (output_public v w i).1
  · funext i
    exact (output_public v w i).2

theorem output_frame (v : Tapes (nodeTapes s c) 2)
    (w : Tapes (permanentTapes s c) 2) (i : Fin (nodeTapes s c))
    (hi : permanentTapes s c ≤ i.val) :
    (output v w).head i=v.head i ∧ (output v w).tape i=v.tape i := by
  simp [output,prefixOutput,Nat.not_lt.mpr hi]

private theorem replace_slot {P N W U : ℕ} (hPN : P≤N)
    (e : Fin ((P+W)+U) ≃ Fin (N+W))
    (he : ∀ i,e (Fin.castAdd U i)=select hPN i) (v : Tapes (N+W) 2)
    (w : Tapes (P+W) 2) (i : Fin (P+W)) :
    (Placement.replace e v w).head (select hPN i)=w.head i ∧
    (Placement.replace e v w).tape (select hPN i)=w.tape i := by
  rw [←he i]
  exact ⟨Placement.combine_head_active _ _ _ _,Placement.combine_tape_active _ _ _ _⟩

private theorem replace_frame {P N W U : ℕ} (hPN : P≤N)
    (e : Fin ((P+W)+U) ≃ Fin (N+W))
    (he : ∀ i,e (Fin.castAdd U i)=select hPN i) (v : Tapes (N+W) 2)
    (w : Tapes (P+W) 2) (i : Fin (N+W))
    (hi : ¬∃ j,select hPN j=i) :
    (Placement.replace e v w).head i=v.head i ∧
    (Placement.replace e v w).tape i=v.tape i := by
  obtain ⟨j,rfl⟩ := e.surjective i
  induction j using Fin.addCases (m:=P+W)
    (n:=U) with
  | left j =>
    exact False.elim (hi ⟨j,(he j).symm⟩)
  | right j =>
    exact ⟨Placement.combine_head_extra _ _ _ _,Placement.combine_tape_extra _ _ _ _⟩

/-- The placed lifecycle returns the exact next public caller and blank scalar
suffix, including every cell and head of the complete middle frame. -/
private theorem replace_ready_aux {P N W U : ℕ} (hPN : P≤N)
    (e : Fin ((P+W)+U) ≃ Fin (N+W))
    (he : ∀ i,e (Fin.castAdd U i)=select hPN i)
    (v : Tapes N 2) (w : Tapes P 2) :
    Placement.replace e
      (v.append (SharedBank.empty W 2)) (raw w (P+W))=
      (prefixOutput v w).append (SharedBank.empty W 2) := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    induction i using Fin.addCases (m:=N) (n:=W) with
    | left i =>
      by_cases hi : i.val<P
      · let j : Fin P := ⟨i.val,hi⟩
        have hj : select hPN (Fin.castAdd W j)=Fin.castAdd W i := select_public hPN j
        have h := replace_slot hPN e he (v.append (SharedBank.empty W 2)) (raw w (P+W))
          (Fin.castAdd W j)
        rw [hj] at h
        first
        | apply h.1.trans; simp only [raw,Fin.val_castAdd,j,dite_eq_left hi,
            Fin.addCases_left,prefixOutput]
        | apply h.2.trans; simp only [raw,Fin.val_castAdd,j,dite_eq_left hi,
            Fin.addCases_left,prefixOutput]
      · have hn : ¬∃ j,select hPN j=Fin.castAdd W i :=
          select_frame hPN i (Nat.le_of_not_gt hi)
        have h := replace_frame hPN e he (v.append (SharedBank.empty W 2)) (raw w (P+W))
          (Fin.castAdd W i) hn
        first
        | apply h.1.trans; simp only [Tapes.append,Fin.addCases_left,prefixOutput,dite_eq_right hi]
        | apply h.2.trans; simp only [Tapes.append,Fin.addCases_left,prefixOutput,dite_eq_right hi]
    | right i =>
      have h := replace_slot hPN e he (v.append (SharedBank.empty W 2)) (raw w (P+W))
        (Fin.natAdd P i)
      rw [select_private] at h
      first
      | apply h.1.trans; simp only [raw,Fin.val_natAdd,
          Nat.not_lt.mpr (Nat.le_add_right _ _),dite_false,
          Fin.addCases_right,SharedBank.empty]
      | apply h.2.trans; simp only [raw,Fin.val_natAdd,
          Nat.not_lt.mpr (Nat.le_add_right _ _),dite_false,
          Fin.addCases_right,SharedBank.empty]

theorem replace_ready (v : Tapes (nodeTapes s c) 2)
    (w : Tapes (permanentTapes s c) 2) :
    Placement.replace (placement s c) (ready v) (raw w (activeTapes s c))=
      ready (output v w) := replace_ready_aux public_le (placement s c)
        (fun i => InjectivePlacement.active_slot _ _ _ i) v w

/-- Generic placement preserves the actual lifecycle's transition count. -/
def liftProgram (P : Σ q,Program (activeTapes s c) q 2) :
    Σ q,Program (tapes s c) q 2 := ⟨P.1,Placement.placed P.2 (placement s c)⟩

theorem lift_runs (P : Σ q,Program (activeTapes s c) q 2)
    (v : Tapes (nodeTapes s c) 2) (w : Tapes (permanentTapes s c) 2)
    (h : HoareTime P.2 (fun z => z=raw (permanent v) (activeTapes s c))
      (fun z => z=raw w (activeTapes s c)) B) :
    HoareTime (liftProgram P).2 (fun z => z=ready v)
      (fun z => z=ready (output v w)) B := by
  have hh := Placement.hoare_at h (placement s c) (ready v) (active_ready v)
  exact hh.consequence (fun _ h => h) (by
    rintro z ⟨w',hw',hz⟩
    rw [hw',replace_ready] at hz
    exact hz) le_rfl

private theorem raw_reindex {k t u : ℕ} (h : t=u) (v : Tapes k 2) :
    (raw v t).reindex (finCongr h)=raw v u := by
  subst u
  rfl

private theorem suffix_assoc {P A B S : ℕ} (h : S=A+B) : (P+A)+B=P+S := by
  rw [h,Nat.add_assoc]

private theorem lifecycle_public : publicTapes (10+s)=permanentTapes s roles := rfl

private theorem lifecycle_size :
    (publicTapes (10+s)+43)+RawLinearCombinationComplexDenominatorPlaced.localCount
      CompactComplexScalarRowBlock.wireCount CompactComplexScalarPolynomialSequence.scratch
      =activeTapes s roles := by
  have hS : scratch=43+RawLinearCombinationComplexDenominatorPlaced.localCount
      CompactComplexScalarRowBlock.wireCount CompactComplexScalarPolynomialSequence.scratch := scratch_eq
  exact (suffix_assoc (P:=publicTapes (10+s)) hS).trans
    (congrArg (fun P => P+scratch) (lifecycle_public (s:=s)))

private def relocate {k : ℕ} (P : Σ q,Program k q 2)
    (h : k=activeTapes s c) : Σ q,Program (tapes s c) q 2 :=
  liftProgram (s:=s) (c:=c) ⟨P.1,reindex P.2 (finCongr h)⟩

private theorem relocate_runs {k : ℕ} (P : Σ q,Program k q 2)
    (hsize : k=activeTapes s c) (v : Tapes (nodeTapes s c) 2)
    (w : Tapes (permanentTapes s c) 2)
    (h : HoareTime P.2 (fun z => z=raw (permanent v) k) (fun z => z=raw w k) B) :
    HoareTime (relocate P hsize).2 (fun z => z=ready v)
      (fun z => z=ready (output v w)) B := by
  have hr := hoare_reindex_eq h (finCongr hsize)
  simp only [raw_reindex] at hr
  exact lift_runs (s:=s) (c:=c) ⟨P.1,reindex P.2 (finCongr hsize)⟩ v w hr

private def lifecycle (header : Fin (10+s)) (hh : header.val≠7)
    (ops : List CompactComplexScalarIntegerRows.RowIndex) :
    Σ q,Program ((publicTapes (10+s)+43)+RawLinearCombinationComplexDenominatorPlaced.localCount
      CompactComplexScalarRowBlock.wireCount CompactComplexScalarPolynomialSequence.scratch) q 2 :=
  CompactComplexScalarCountLifecycle.program (s:=10+s) (by omega) header hh ops

/-- The actual original-header setup, named scalar block, and count erasure
on the fixed source-ready bank, with one private suffix independent of depth. -/
def program (header : Fin (10+s)) (hh : header.val≠7)
    (ops : List CompactComplexScalarIntegerRows.RowIndex) :
    Σ q,Program (tapes s roles) q 2 :=
  relocate (s:=s) (c:=roles) (k:=((publicTapes (10+s)+43)+RawLinearCombinationComplexDenominatorPlaced.localCount
      CompactComplexScalarRowBlock.wireCount CompactComplexScalarPolynomialSequence.scratch))
    (lifecycle (s:=s) header hh ops) (lifecycle_size (s:=s))

/-- The public next caller is literal scalar output; the complete middle bank
is retained and every newly borrowed scalar tape returns blank. -/
theorem runs {sh : CompactGadgetReservationShape.Shape}
    (inp : ActivePrefixStageFullData.Inputs sh) (header : Fin (10+s)) (hh : header.val≠7)
    (ops : List CompactComplexScalarIntegerRows.RowIndex) (ell p w d : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+s) 2) (payload : Tapes (1+roles) 2)
    (v : Tapes (nodeTapes s roles) 2)
    (hv : permanent (s:=s) (c:=roles) v=CompactComplexNativeCodecFrame.bank (s:=10+s) (c:=roles) control queue scalar
      (CompactComplexNativeCodec.raw inp.stage inp.rows ell p) tail storage payload)
    (xs : Fin CompactComplexScalarRowBlock.wireCount →
      Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → ButterflyStreamData.Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=w ∧ (xs a i j).2.length=w)
    (hblank : storage.head header=0 ∧ storage.tape header=(fun _ => blank))
    (hsource : ∀ a,(permanent (s:=s) (c:=roles) v).head
      (CompactComplexNativeRoleBridge.roleSlot (s:=10+s+43) (c:=roles) (CompactComplexScalarRolePorts.roleIndex a))=0 ∧
      (permanent (s:=s) (c:=roles) v).tape
      (CompactComplexNativeRoleBridge.roleSlot (s:=10+s+43) (c:=roles) (CompactComplexScalarRolePorts.roleIndex a))=
        SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
          (ActivePrefixStageNativePolynomial.rows inp (xs a) (hw a)))))
    (hlive : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits d)) :
    HoareTime (program (s:=s) header hh ops).2 (fun z => z=ready (s:=s) (c:=roles) v)
      (fun z => z=ready (s:=s) (c:=roles) (output (s:=s) (c:=roles) v (CompactComplexScalarCountLifecycle.output (s:=10+s)
        (by omega : 7<10+s) header (permanent (s:=s) (c:=roles) v)
        (CompactComplexScalarPolynomialSequence.execute ops
          (fun a => ActivePrefixStageNativePolynomial.flattenArray (xs a))) (d+ops.length))))
      (CompactComplexScalarCountLifecycle.cost ops
        (ActivePrefixStageTripleWords.count inp*2^ell) w d) := by
  have hs : 7<10+s := by omega
  have hsource' := hsource
  rw [hv] at hsource'
  have h := CompactComplexScalarCountLifecycle.runs (s:=10+s) (sh:=sh) inp hs header hh ops ell p w d
    control queue scalar tail storage payload xs hw hblank hsource' hlive
  dsimp only at h
  rw [←hv] at h
  exact relocate_runs (s:=s) (c:=roles) (k:=((publicTapes (10+s)+43)+RawLinearCombinationComplexDenominatorPlaced.localCount
      CompactComplexScalarRowBlock.wireCount CompactComplexScalarPolynomialSequence.scratch))
    (lifecycle (s:=s) header hh ops) (lifecycle_size (s:=s)) v _ h

theorem ready_scratch (v : Tapes (nodeTapes s c) 2) (i : Fin scratch) :
    (ready v).head (Fin.natAdd (nodeTapes s c) i)=0 ∧
    (ready v).tape (Fin.natAdd (nodeTapes s c) i)=(fun _ => blank) := by
  simp only [ready,Tapes.append,Fin.addCases_right,SharedBank.empty,and_self]

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyScalarWorkspace
