module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackArchivePorts
public import IntegerMultBounds.MathlibTM2.Cover.FallbackArchiveStep

/-! Run physical reverse columns from the two alternating matrix archives. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open Matrix GoodForm IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

noncomputable def reverseStages (d : ℕ) : ℕ → Pr P (N+2) columnCapacity prime U
  | 0 => .act .done
  | n+1 => if h : n < d then
      .seq (placedColumn (archivePorts n) (⟨n,h⟩ : Fin d))
        (.seq (dropWords (archivePorts n (columnBank 2)) (archivePorts (n+1) (columnBank 34))
          (archivePorts n (columnBank 0)) (d*d)) (reverseStages d n))
    else reverseStages d n

/-- At every positive stage the exposed matrix supplies the column coefficients. -/
theorem reverseStage_exec (k : Fin d) (rows : Fin d → Fin d) (H J : ℕ)
    (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P (N+2) columnCapacity prime U) (v : HS (N+2) columnCapacity prime U) (S : Stacks (N+2) prime)
    (m : Matrix (Fin d) (Fin d) (ZMod M)) (valid : Itinerary.Valid rows m (k.val+1))
    (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank)
    (original : Fin (M^d*W) → ZMod 2)
    (code : S.R (Fin.last N).castSucc = orderedScheduleCode (((List.finRange d).take (k.val+1)).reverse) rows ++ rest) :
    let ports := archivePorts k.val
    let stage := Itinerary.run rows m
    let ready := ColumnReady (columnBank.trans ports) H J (stage k.val) tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original
    let clean := fun (D : Stacks (N+2) prime) => ∀ i : Fin N, 35 ≤ i.val → D.L (columnPorts i).castSucc = [] ∧ D.R (columnPorts i).castSucc = []
    ready (fun x => stage (k.val+1) *ᵥ x) S → clean S →
    ∃ z F n, z.user = v.user ∧ n ≤ 1+columnProgramTime U k (rows k) w W H J ∧
      Exec body (placedColumn ports k) (mk v S) n (mk z F) ∧ ready (fun x => stage k.val *ᵥ x) F ∧ clean F ∧
      F.R (Fin.last N).castSucc = orderedScheduleCode (((List.finRange d).take k.val).reverse) rows ++ rest ∧
      F.R (archivePorts (k.val+1) (columnBank 34)) = S.R (archivePorts (k.val+1) (columnBank 34)) := by
  intro ports stage ready clean before free
  have unit := ((Itinerary.valid_succ rows m k.val).mp valid).2 k.isLt
  obtain ⟨z,F,n,hz,hn,run,next,freeF,stream,frame⟩ := placedColumn_exec ports k rows H J hm hw hW body v S
    (stage k.val) unit.2 tail rest dest q empty original (fun x => stage k.val *ᵥ x)
    (by simpa [ports,archivePorts_stream] using code)
    (by simpa only [ready,stage,Itinerary.run_succ rows m k.val k.isLt,← mulVec_mulVec] using before)
    (fun i hi => by simpa only [ports,archivePorts_workspace _ _ hi] using free i hi)
  exact ⟨z,F,n,hz,hn,run,next,fun i hi => by simpa only [ports,archivePorts_workspace _ _ hi] using freeF i hi,
    by simpa only [ports,archivePorts_stream] using stream,(frame _ (archivePorts_other k.val)).2⟩

omit [M8.Machine.Net] in
private theorem changeArchive {T A : ℕ} (bank next : Fin 35 ↪ Fin T)
    (fixed : ∀ i, i ≠ 34 → next i = bank i) (H J : ℕ)
    (m a : Matrix (Fin d) (Fin d) (ZMod M)) (tail suffix : List (Fin (A+4)))
    (sym : ZMod 2 → Fin 4) (dest : ℤ → Fin 4) (q : ℤ) (original : Fin (M^d*W) → ZMod 2)
    (addr : (Fin d → ZMod M) → Fin d → ZMod M) (S : Stacks T A)
    (ready : ColumnReady bank H J m tail sym (fun _ => blank) dest 0 q original addr S)
    (packed : S.R (next 34) = matrixWords A H a ++ suffix) :
    ColumnReady next H J a suffix sym (fun _ => blank) dest 0 q original addr S := by
  obtain ⟨word,h,placed⟩ := ready
  refine ⟨word,⟨?_,?_,?_,?_,?_,packed,?_,?_,?_⟩,placed⟩
  · simpa only [fixed 2 (by decide)] using h.modulus
  · simpa only [fixed 27 (by decide)] using h.width
  · simpa only [fixed 28 (by decide)] using h.one
  · simpa only [fixed 32 (by decide)] using h.padded
  · rw [fixed 33 (by decide),h.clock]
  · intro i hi
    rw [fixed i (fun e => (by decide : (34 : Fin 35) ∉ shearWork) (e ▸ hi))]
    exact h.scratch i hi
  · simpa only [fixed 24 (by decide)] using h.src
  · simpa only [fixed 25 (by decide)] using h.dst

theorem reverseStages_exec (rows : Fin d → Fin d) (H J : ℕ)
    (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P (N+2) columnCapacity prime U)
    (m : Matrix (Fin d) (Fin d) (ZMod M)) (tail destTail rest : List (Fin (prime+4)))
    (dest : ℤ → Fin 4) (q : ℤ) (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank)
    (original : Fin (M^d*W) → ZMod 2) :
    let stage := Itinerary.run rows m
    let words := fun n => matrixWords prime H (stage n)
    let archive := matrixArchive words (words 0 ++ tail) destTail
    let bank := fun n => columnBank.trans (archivePorts n)
    let ready := fun n suffix => ColumnReady (bank n) H J (stage n) suffix SparseRoleCircuit.encode (fun _ => blank)
      dest 0 q original (fun x => stage n *ᵥ x)
    let clean := fun (D : Stacks (N+2) prime) => ∀ i : Fin N, 35 ≤ i.val → D.L (columnPorts i).castSucc = [] ∧ D.R (columnPorts i).castSucc = []
    let cost := 1+Finset.univ.sup (fun k => columnProgramTime U k (rows k) w W H J)+(d*d*(4*H+4)+1)
    ∀ n, n ≤ d → Itinerary.Valid rows m n → ∀ v S suffix, ready n suffix S → clean S →
      (S.R (bank n 34), S.R (bank (n+1) 34)) = archive n →
      S.R (Fin.last N).castSucc = orderedScheduleCode (((List.finRange d).take n).reverse) rows ++ rest →
      ∃ z F l, z.user = v.user ∧ l ≤ n*cost+1 ∧ Exec body (reverseStages d n) (mk v S) l (mk z F) ∧
        ready 0 tail F ∧ clean F ∧ F.R (Fin.last N).castSucc = rest ∧ F.R (bank 1 34) = destTail := by
  intro stage words archive bank ready clean cost n
  induction n with
  | zero =>
    intro _ _ v S suffix ok free pair code
    have packed := ok.choose_spec.1.archive
    have same : suffix = tail := List.append_cancel_left (packed.symm.trans (congrArg Prod.fst pair))
    subst suffix
    exact ⟨v,S,1,rfl,by simp,Exec.act (body := body) .done _,ok,free,by simpa [orderedScheduleCode] using code,congrArg Prod.snd pair⟩
  | succ n ih =>
    intro hn valid v S suffix ok free pair code
    let k : Fin d := ⟨n,hn⟩
    have top (j : ℕ) : ∃ t, (archive j).1 = words j ++ t := by cases j <;> exact ⟨_,rfl⟩
    obtain ⟨t,ht⟩ := top n
    have older : S.R (bank n 34) = (archive n).1 := by
      simpa only [bank,Function.Embedding.trans_apply,archivePorts_period] using (show S.R (bank (n+2) 34) = (archive n).1 from congrArg Prod.snd pair)
    have colReady := changeArchive (bank (n+1)) (bank n) (fun i hi => (archivePorts_bank_fixed n i hi).symm)
      H J _ (stage n) suffix t _ dest q original _ S ok (older.trans ht)
    obtain ⟨u,D,l,hu,hl,col,next,freeD,stream,frame⟩ := reverseStage_exec k rows H J hm hw hW body v S m valid
      t rest dest q empty original code colReady free
    have packed : D.R (bank (n+1) 34) = words (n+1) ++ (archive n).2 := frame.trans (congrArg Prod.fst pair)
    obtain ⟨y,hy,drop⟩ := dropWords_exec body ((archivePorts_other n (columnBank 2)))
      ((bank n).injective.ne (by decide : (2 : Fin 35) ≠ 0)) (archivePorts_other n (columnBank 0)).symm
      (d*d) H u D (by exact (congrArg List.length next.choose_spec.1.modulus).trans (length_binSyms ..)) (next.choose_spec.1.scratch 0 (by decide)).2
    let E := {D with R := Function.update D.R (bank (n+1) 34) ((archive n).2)}
    have cut : (D.R (bank (n+1) 34)).drop (d*d*H) = (archive n).2 := by
      rw [packed,← length_matrixWords prime H (stage (n+1)),List.drop_left]
    change Exec body _ _ _ (mk y {D with R := Function.update D.R (bank (n+1) 34) ((D.R (bank (n+1) 34)).drop (d*d*H))}) at drop
    rw [cut] at drop
    have keep (i) : E.R (archivePorts n i) = D.R (archivePorts n i) := Function.update_of_ne (archivePorts_other n i) _ _
    have okE : ready n t E := by
      obtain ⟨word,h,p⟩ := next
      refine ⟨word,?_,p⟩
      rcases h with ⟨modulus,width,one,padded,clock,coeff,scratch,src,dst⟩
      constructor <;> simp only [bank,Function.Embedding.trans_apply,keep] <;> assumption
    obtain ⟨z,F,a,hz,ha,run,done⟩ := ih (by omega) ((Itinerary.valid_succ ..).mp valid).1 y E t okE
      (fun i hi => ⟨(freeD i hi).1,by rw [← archivePorts_workspace n i hi,keep,archivePorts_workspace n i hi]; exact (freeD i hi).2⟩)
      (Prod.ext ((keep _).trans (next.choose_spec.1.archive.trans ht.symm)) (Function.update_self ..))
      (by rw [← archivePorts_stream n,keep,archivePorts_stream]; exact stream)
    have bound := Finset.le_sup (f := fun k => columnProgramTime U k (rows k) w W H J) (Finset.mem_univ k)
    refine ⟨z,F,l+((d*d*(4*H+4)+1)+a),hz.trans (hy.trans hu),?_,?_,done⟩
    · rw [Nat.succ_mul n cost]
      dsimp only [cost] at ha ⊢
      omega
    · rw [reverseStages,dite_eq_left (show n < d from hn)]
      exact Exec.seq col (Exec.seq drop run)

/-- Remove both weight prefixes and run the complete reverse itinerary on its saved matrices. -/
theorem weightedRewind_exec {r b : ℕ} (pivot : Fin r → ZMod M) (parent : Fin b → ZMod M)
    (rows : Fin d → Fin d) (m : Matrix (Fin d) (Fin d) (ZMod M)) (valid : Itinerary.Valid rows m d)
    (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P (N+2) columnCapacity prime U) (v : HS (N+2) columnCapacity prime U) (S : Stacks (N+2) prime)
    (tail destTail suffix rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank) (original : Fin (M^d*W) → ZMod 2) :
    let stage := Itinerary.run rows m
    let words := fun n => matrixWords prime H (stage n)
    let bank := fun n => columnBank.trans (archivePorts n)
    let stream := (Fin.last N).castSucc
    let code := orderedScheduleCode (List.finRange d).reverse rows ++ rest
    let pack := fun {k : ℕ} (a : Fin k → ZMod M) => (List.ofFn fun j => binSyms (A := prime) H (a j).val).flatten
    let clean := fun (D : Stacks (N+2) prime) => ∀ j : Fin N, 35 ≤ j.val →
      D.L (columnPorts j).castSucc = [] ∧ D.R (columnPorts j).castSucc = []
    let pop := .seq (dropWords (bank d 2) (bank d 34) (bank d 0) r) (dropWords (bank d 2) stream (bank d 0) b)
    let cost := 1+Finset.univ.sup (fun k => columnProgramTime U k (rows k) w W H J)+(d*d*(4*H+4)+1)
    ColumnRecordReady (bank d) H J (pack pivot ++ (words d ++ suffix)) SparseRoleCircuit.encode
      (fun _ => blank) dest 0 q original (stage d).mulVec S → clean S → S.R stream = pack parent ++ code →
    (words d ++ suffix,S.R (bank (d+1) 34)) = matrixArchive words (words 0 ++ tail) destTail d →
    ∃ z F l, z.user = v.user ∧ l ≤ ((r*(4*H+4)+1)+(b*(4*H+4)+1))+(d*cost+1) ∧
      Exec body (.seq pop (reverseStages d d)) (mk v S) l (mk z F) ∧
      ColumnReady (bank 0) H J m tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original m.mulVec F ∧
      clean F ∧ F.R stream = rest ∧ F.R (bank 1 34) = destTail := by
  intro stage words bank stream code pack clean pop cost before free schedule archive
  have off (n : ℕ) (i : Fin 35) : bank n i ≠ stream := by
    rw [show stream = archivePorts n (Fin.last N) from (archivePorts_stream n).symm]
    apply (archivePorts n).injective.ne
    intro e
    have val := congrArg Fin.val e
    change i.val = N at val
    omega
  obtain ⟨u,hu,prep,ready⟩ := exposeReverseArchives_exec (bank d) stream (off d) body v S H J pivot parent
    (stage d) suffix code SparseRoleCircuit.encode (fun _ => blank) dest 0 q original (stage d).mulVec before schedule
  let D := {S with R := Function.update (Function.update S.R (bank d 34) (words d ++ suffix)) stream code}
  have work : clean D := by
    intro j hj
    have away : (columnPorts j).castSucc ≠ bank d 34 := by
      rw [← archivePorts_workspace d j hj]
      apply (archivePorts d).injective.ne
      intro e
      have val := congrArg Fin.val e
      change j.val = 34 at val
      omega
    have ns : (columnPorts j).castSucc ≠ stream := by
      intro e
      have val := congrArg Fin.val e
      change j.val = N at val
      omega
    simpa [D,away,ns] using free j hj
  have packed : (D.R (bank d 34),D.R (bank (d+1) 34)) = matrixArchive words (words 0 ++ tail) destTail d := by
    have apart : bank (d+1) 34 ≠ bank d 34 := (archivePorts_other d (columnBank 34)).symm
    simpa [D,off,apart] using archive
  obtain ⟨z,F,l,hz,hl,run,result⟩ := reverseStages_exec rows H J hm hw hW body m tail destTail rest dest q empty
    original d le_rfl valid u D suffix ready work packed (by rw [List.take_of_length_le (by simp)]; exact Function.update_self ..)
  exact ⟨z,F,_,hz.trans hu,Nat.add_le_add_left hl _,Exec.seq prep run,result⟩

/-- Run the archive rewind within a larger tape and state space. -/
theorem placedWeightedRewind_exec {r b T Q : ℕ} (host : Fin (N+2) ↪ Fin T) (capacity : columnCapacity ≤ Q) (pivot : Fin r → ZMod M) (parent : Fin b → ZMod M)
    (rows : Fin d → Fin d) (m : Matrix (Fin d) (Fin d) (ZMod M)) (valid : Itinerary.Valid rows m d)
    (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P T Q prime U) (v : HS T Q prime U) (S : Stacks T prime)
    (tail destTail suffix rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank) (original : Fin (M^d*W) → ZMod 2) :
    let stage := Itinerary.run rows m
    let words := fun n => matrixWords prime H (stage n)
    let bank := fun n => columnBank.trans (archivePorts n)
    let stream := (Fin.last N).castSucc
    let code := orderedScheduleCode (List.finRange d).reverse rows ++ rest
    let pack := fun {k : ℕ} (a : Fin k → ZMod M) => (List.ofFn fun j => binSyms (A := prime) H (a j).val).flatten
    let clean := fun (D : Stacks (N+2) prime) => ∀ j : Fin N, 35 ≤ j.val →
      D.L (columnPorts j).castSucc = [] ∧ D.R (columnPorts j).castSucc = []
    let pop := .seq (dropWords (bank d 2) (bank d 34) (bank d 0) r) (dropWords (bank d 2) stream (bank d 0) b)
    let cost := 1+Finset.univ.sup (fun k => columnProgramTime U k (rows k) w W H J)+(d*d*(4*H+4)+1)
    ColumnRecordReady ((bank d).trans host) H J (pack pivot ++ (words d ++ suffix)) SparseRoleCircuit.encode
      (fun _ => blank) dest 0 q original (stage d).mulVec S → clean (embStk host S) → S.R (host stream) = pack parent ++ code →
    (words d ++ suffix,S.R (host (bank (d+1) 34))) = matrixArchive words (words 0 ++ tail) destTail d →
    ∃ z F l, z.user = v.user ∧ l ≤ 1+(((r*(4*H+4)+1)+(b*(4*H+4)+1))+(d*cost+1)) ∧
      Exec body (statePlacedNormalized host capacity (lt_of_lt_of_le (by decide : 0 < 217) (le_max_left ..)) Empty.elim (.seq pop (reverseStages d d))) (mk v S) l (mk z F) ∧
      ColumnReady ((bank 0).trans host) H J m tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original m.mulVec F ∧
      clean (embStk host F) ∧ F.R (host stream) = rest ∧ F.R (host (bank 1 34)) = destTail ∧
      ∀ h, (∀ i, host i ≠ h) → F.L h = S.L h ∧ F.R h = S.R h := by
  intro stage words bank stream code pack clean pop cost before free schedule archive
  have positive : 0 < columnCapacity := lt_of_lt_of_le (by decide : 0 < 217) (le_max_left ..)
  have projected := (columnRecordReady_project ..).mp before
  obtain ⟨u,D,n,hu,hn,run,next,cleanD,remaining,other⟩ := weightedRewind_exec pivot parent rows m valid
    H J hm hw hW (P := Empty) Empty.elim (stateLiftDown positive (embDn host v)) (embStk host S)
    tail destTail suffix rest dest q empty original ((columnRecordReady_project (bank d) ..).mpr projected)
    free schedule archive
  obtain ⟨z,_,hz,placed⟩ := statePlaced_exec_normalized host host.injective capacity positive Empty.elim
    (body' := body) (fun e => nomatch e) v S run
  let F := embOvr host D.get S
  have eq : embStk host F = D := embStk_ovr host.injective _ _
  have layout := (columnReady_project (bank 0) ..).mp next
  rw [← eq] at layout cleanD remaining other
  exact ⟨z,F,_,hz.trans hu,Nat.add_le_add_left hn 1,placed,(columnReady_project ..).mpr layout,
    cleanD,remaining,other,fun h off => embOvr_off _ _ off⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
