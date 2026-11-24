module

public import IntegerMultBounds.MathlibTM2.M6.BitNodeHeaderSetup
public import IntegerMultBounds.MathlibTM2.M6.BitScheduledChildHeaders
public import IntegerMultBounds.MathlibTM2.M6.BitClearBank

/-! Generate the packed seed headers for the scheduled child using the parent's
role fields and the child's row-length control. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open RecursiveInterchangeLayout
open Shared50ModularControl (prime)

def headerRegs : Fin 12 ↪ Fin 38 := Fin.castLEEmb (by decide)
def clockRegs : Fin 7 ↪ Fin 38 :=
  ⟨![3,12,13,14,15,16,17],by decide⟩
def powerRegs : Fin 10 ↪ Fin 38 :=
  ⟨![12,18,19,20,21,22,23,24,25,26],by decide⟩
def divRegs : Fin 11 ↪ Fin 38 := ⟨fun i => ⟨27+i.val,by omega⟩,fun i j h =>
  Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))⟩

def moveSeedHeaders {T : ℕ} (r : Fin 38 ↪ Fin T) (fields : Fin 6 → Fin T) (cut : Fin T) :=
  nodeHeaderSources (scheduledHeaderPorts fields (headerRegs.trans r)) (clockRegs.trans r)
    (powerRegs.trans r) cut (r (divRegs 2))

def moveSeedOutputs {T : ℕ} (r : Fin 38 ↪ Fin T) : List (Fin T) :=
  ([3,4,12,13,18,20,29] : List (Fin 38)).map r

/-- The runtime program is fixed by the scheduled occurrence. The first three
registers hold the parent clock, radix and middle field. -/
theorem scheduledMoveSeedHeaders {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (r : Fin 38 ↪ Fin T) (fields : Fin 6 → Fin T) (cut row : Fin T)
    (fieldOff : ∀ i j, fields i ≠ r j) (cutOff : ∀ j, cut ≠ r j) (rowOff : ∀ j, row ≠ r j)
    (i : Fin nodeChildren5.length) :
    ∃ code, ∀ (p c : CutoffNodeInput), c.node = scheduledChild prime p.node i →
      ∀ u (S : Stacks T prime), (S.R (r 0)).length = p.w →
      S.R (r 1) = binSyms (prime^(p.w+1)).size (prime^(p.w+1)) →
      S.R (r 2) = (Routines.hdr p.node 4).map bitSymbol →
      (∀ j : Fin 38, 3 ≤ j.val → S.R (r j) = []) →
      (∀ j, j ≠ 3 → j ≠ 4 → S.R (fields j) = (Routines.hdr (role p.node 142080) j).map bitSymbol) →
      S.R cut = binSyms c.root.width.size c.cutoff → LengthControl (S.R row) c.cells →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (512008*p.cells+nodeHeaderSetupRate*c.cells) ∧
        (∀ j, F.R (moveSeedHeaders r fields cut j) = nodeSeedWords c j) ∧
        ∀ j, j ∉ moveSeedOutputs r → F.L j = S.L j ∧ F.R j = S.R j := by
  let h := headerRegs.trans r
  let clock := clockRegs.trans r
  let power := powerRegs.trans r
  let div := divRegs.trans r
  let src := scheduledHeaderPorts fields h
  have distinct (a b : Fin 38) (ne : a ≠ b) := r.injective.ne ne
  have outer (j) (off : ∀ k, j ≠ r k) : outsideArchiveOutputs clock power j :=
    ⟨off _,off _,off _,off _⟩
  have inner (j : Fin 38) (a : j ≠ 12) (b : j ≠ 13) (c : j ≠ 18) (d : j ≠ 20) :
      outsideArchiveOutputs clock power (r j) :=
    ⟨distinct _ _ a,distinct _ _ b,distinct _ _ c,distinct _ _ d⟩
  obtain ⟨build,prepare⟩ := prepareScheduledHeaders body h fields i (fun j _ _ => ⟨fieldOff j _,fieldOff j _⟩)
  have srcOff (j) : outsideArchiveOutputs clock power (src j) ∧ src j ≠ div 2 := by
    have base k := And.intro (outer (fields k) (fieldOff k)) (fieldOff k (divRegs 2))
    have at3 := And.intro (inner 3 (by decide) (by decide) (by decide) (by decide)) (distinct 3 29 (by decide))
    have at4 := And.intro (inner 4 (by decide) (by decide) (by decide) (by decide)) (distinct 4 29 (by decide))
    fin_cases j <;> first | exact base _ | exact at3 | exact at4
  obtain ⟨setup,generate⟩ := nodeHeaderSetup body src clock power cut row div rfl rfl
    (fun j => distinct _ _ ((by decide : ∀ i, clockRegs 2 ≠ powerRegs i) j))
    (fun j => (srcOff j).1) (outer cut cutOff) (outer row rowOff)
    (fun j => inner _ (by exact (by decide : ∀ i, divRegs i ≠ 12) j) (by exact (by decide : ∀ i, divRegs i ≠ 13) j)
      (by exact (by decide : ∀ i, divRegs i ≠ 18) j) (by exact (by decide : ∀ i, divRegs i ≠ 20) j))
    (fun j => rowOff _) (cutOff _) (fun j => (srcOff j).2)
  refine ⟨build.seq setup,?_⟩
  intro p c child u S clockAt radix middle free inherited cutoff length
  obtain ⟨v,D,n,exec,user,paid,ready,frame⟩ := prepare p u S clockAt radix middle
    (fun j hj => free (headerRegs j) hj) inherited
  have preserved j (a : j ≠ r 3) (b : j ≠ r 4) := frame j a b
  have fresh (j : Fin 38) (hj : 5 ≤ j.val) : D.R (r j) = [] := by
    have ne3 : j ≠ 3 := by intro e; subst j; contradiction
    have ne4 : j ≠ 4 := by intro e; subst j; contradiction
    exact (preserved _ (r.injective.ne ne3) (r.injective.ne ne4)).2.trans (free _ (by omega))
  obtain ⟨z,F,m,run,same,bill,headers,rest⟩ := generate c v D (child ▸ ready)
    ((preserved _ (cutOff 3) (cutOff 4)).2.trans cutoff) ((preserved _ (rowOff 3) (rowOff 4)).2.symm ▸ length)
    (fun j hj => fresh (clockRegs j) ((by decide : ∀ j, j ≠ 0 → 5 ≤ (clockRegs j).val) j hj))
    (fun j hj => fresh (powerRegs j) ((by decide : ∀ j, j ≠ 0 → 5 ≤ (powerRegs j).val) j hj))
    (fun j => fresh (divRegs j) (by change 5 ≤ 27+j.val; omega))
  refine ⟨z,F,n+m,exec.seq run,same.trans user,paid.seq bill,headers,?_⟩
  intro j untouched
  have ne (k : Fin 38) (mem : k ∈ [3,4,12,13,18,20,29]) : j ≠ r k :=
    fun eq => untouched (eq ▸ List.mem_map_of_mem mem)
  have kept := rest j ⟨ne 12 (by decide),ne 13 (by decide),ne 18 (by decide),ne 20 (by decide)⟩ (ne 29 (by decide))
  have old := preserved j (ne 3 (by decide)) (ne 4 (by decide))
  exact ⟨kept.1.trans old.1,kept.2.trans old.2⟩

/-- Count the actual record payload in groups of 142080, restoring it even
when its physical storage contains trailing blanks. Only the binary result survives. -/
theorem movePayloadRowLength {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (payload tmp : Fin T) (r : Fin 9 ↪ Fin T) (apart : [payload,tmp,r 0].Nodup)
    {V : ℕ} (m : ℕ) (size : V = m*142080) (x : Fin V → ZMod 2) u (S : Stacks T prime)
    (input : RecordPayload payload (fun _ => blank) 0 x S)
    (left : S.L tmp = []) (right : S.R tmp = []) (empty : ∀ j, S.R (r j) = []) :
    let F := {S with R := Function.update S.R (r 2) (binSyms m.size m)}
    ∃ z t, Exec body (((loadCompactWord payload tmp (r 0)).seq (intervalCounter r)).seq (bclear (r 0)))
      (mk u S) t (mk z F) ∧ z.user = u.user ∧ CleanupBound S F t (14*V+25*m+28) := by
  intro F
  have reads : WordAtZero x (S.L payload) (S.R payload) := by
    intro j
    rw [← encodedOwnerCell]
    simpa only [sub_zero,List.map_ofFn] using input j
  obtain ⟨v,same,copy⟩ := loadCompactWord_exec body payload tmp (r 0) apart x u S reads left right
  rw [empty 0,List.append_nil] at copy
  let D := {S with R := Function.update S.R (r 0) (List.ofFn fun i => SparseRoleCircuit.encode (x i))}
  obtain ⟨a,n,user,time,divide⟩ := intervalCounter_exec body r m v D (by simp [D,size])
    (fun j ne => by simp [D,r.injective.ne ne,empty])
  rw [canonicalBits_symbols] at divide
  let E := {D with R := Function.update D.R (r 2) (binSyms m.size m)}
  obtain ⟨z,zu,_,erase⟩ := bclear_exec body (r 0) a E
  have length : (E.R (r 0)).length = V := by simp [E,D,r.injective.eq_iff]
  have final : {E with R := Function.update E.R (r 0) []} = F := by
    unfold E F D
    congr 1
    funext j
    by_cases h : j = r 0
    · subst j; simp [empty,r.injective.eq_iff]
    · simp [Function.update_of_ne h,Function.update_apply]
  rw [final,length] at erase
  refine ⟨z,_,(copy.seq divide).seq erase,zu.trans (user.trans same),?_⟩
  intro js nd
  have grow := prependedWordCharge S (r 2) (binSyms m.size m) js nd
  rw [empty 2,List.append_nil,length_binSyms] at grow
  change tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+2*m.size at grow
  change _ + tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+_
  have digits : m.size ≤ m := Nat.size_le.mpr Nat.lt_two_pow_self
  omega

/-- Produce all twelve loader inputs from the scheduled MOVE payload and parent
fields. The caller supplies neither a child descriptor word nor a length tape. -/
theorem scheduledMovePayloadHeaders {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (r : Fin 38 ↪ Fin T) (fields : Fin 6 → Fin T) (cut payload tmp : Fin T) (count : Fin 9 ↪ Fin T)
    (apart : [payload,tmp,count 0].Nodup)
    (fieldOff : ∀ i j, fields i ≠ r j) (cutOff : ∀ j, cut ≠ r j) (rowOff : ∀ j, count 2 ≠ r j)
    (inheritedOff : ∀ i, fields i ≠ count 2) (cutRow : cut ≠ count 2) (i : Fin nodeChildren5.length) :
    ∃ code, ∀ (p c : CutoffNodeInput), c.node = scheduledChild prime p.node i →
      ∀ u (S : Stacks T prime) (x : Fin p.cells → ZMod 2),
      RecordPayload payload (fun _ => blank) 0 x S → S.L tmp = [] → S.R tmp = [] →
      (∀ j, S.R (count j) = []) → (S.R (r 0)).length = p.w →
      S.R (r 1) = binSyms (prime^(p.w+1)).size (prime^(p.w+1)) →
      S.R (r 2) = (Routines.hdr p.node 4).map bitSymbol →
      (∀ j : Fin 38, 3 ≤ j.val → S.R (r j) = []) →
      (∀ j, j ≠ 3 → j ≠ 4 → S.R (fields j) = (Routines.hdr (role p.node 142080) j).map bitSymbol) →
      S.R cut = binSyms c.root.width.size c.cutoff →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (512022*p.cells+(nodeHeaderSetupRate+25)*c.cells+28) ∧
        (∀ j, F.R (moveSeedHeaders r fields cut j) = nodeSeedWords c j) ∧
        ∀ j, j ∉ count 2 :: moveSeedOutputs r → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨headers,prepare⟩ := scheduledMoveSeedHeaders body r fields cut (count 2) fieldOff cutOff rowOff i
  refine ⟨(((loadCompactWord payload tmp (count 0)).seq (intervalCounter count)).seq (bclear (count 0))).seq headers,?_⟩
  intro p c child u S x data left right empty clock radix middle free inherited cutoff
  have size : p.cells = c.cells*142080 := by rw [c.cells_share,child,scheduledChildVolume]
  obtain ⟨a,n,measure,user,cost⟩ := movePayloadRowLength body payload tmp count apart c.cells size x u S data left right empty
  let D := {S with R := Function.update S.R (count 2) (binSyms c.cells.size c.cells)}
  have reg j : D.R (r j) = S.R (r j) := Function.update_of_ne (rowOff j).symm ..
  have length : LengthControl (D.R (count 2)) c.cells := by
    refine ⟨[],?_,rfl⟩
    simp [D]
  obtain ⟨z,F,m,run,same,paid,words,frame⟩ := prepare p c child a D ((reg 0) ▸ clock)
    ((reg 1).trans radix) ((reg 2).trans middle) (fun j h => (reg j).trans (free j h))
    (fun j h k => (Function.update_of_ne (inheritedOff j) ..).trans (inherited j h k))
    ((Function.update_of_ne cutRow ..).trans cutoff) length
  refine ⟨z,F,n+m,measure.seq run,same.trans user,?_,words,?_⟩
  · have bill := cost.seq paid
    convert bill using 1; ring
  · intro j off
    have ne : j ≠ count 2 := fun eq => off (by simp [eq])
    have same := frame j (fun mem => off (List.mem_cons_of_mem _ mem))
    exact ⟨same.1,same.2.trans (Function.update_of_ne ne ..)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
