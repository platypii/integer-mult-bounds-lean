module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackLeafPlacement
public import IntegerMultBounds.MathlibTM2.Cover.FallbackLeafSchedule

/-! Execute the stopped-leaf schedule on the parent's placed column. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open M8 ActualAffineScaling FlatCoordinateLayout M8.Exchange IntegerMultBounds.Swap.Shear
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w W Q : ℕ}
local notation "fields" => d+1
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

/-- One control-state bank serves every stopped rank at this arity. -/
noncomputable def leafCapacity (arity : ℕ) : ℕ :=
  max columnCapacity (Finset.univ.sup fun j : Fin arity => (fieldSignProgram j true).1)

/-- The control program depends only on the selected pairs and their archive indices. -/
noncomputable def placedLeafProgram {n m : ℕ} (k t : Fin n → Fin m) (read : Fin n → ℕ)
    (capacity : columnCapacity ≤ Q) (signCapacity : ∀ a, (fieldSignProgram (k a) true).1 ≤ Q) :
    let total := Fintype.card (Σ a, Fin (22+fieldSignSlots (k a)))
    Pr P (62+(N-35)+total+1) Q prime U :=
  let width := fun a => 22+fieldSignSlots (k a)
  let total := Fintype.card (Σ a, Fin (width a))
  let ports := Fin.castAddEmb (n := N+1+total) 1
  let bank := leafScheduleBank N total (Nat.le_add_left ..)
  let program := fun a =>
    let host := Fin.castAddEmb (n := N+1) (width a)
    let sign := extendSignBank columnBank (fieldSignSlots (k a))
    statePlacedNormalized ((exchangeBank (N+1) width a).trans ports) (le_refl Q)
      (lt_of_lt_of_le columnCapacity_pos capacity) Empty.elim
      (.seq (statePlacedNormalized host capacity columnCapacity_pos Empty.elim (childExchange (read a) 0 (k a) (t a)))
        (.seq (installFieldHeaders ((installerPorts _).trans sign))
          (placedFieldNeg (k a) ((signPorts _).trans sign) (signCapacity a))))
  statePlacedNormalized bank (le_refl Q) (lt_of_lt_of_le columnCapacity_pos capacity) Empty.elim
    ((List.finRange n).foldr (fun a rest => .seq (program a) rest) (.act .done))

omit [M8.Machine.Net] in
theorem clearPrivateAfter {T A : ℕ} (firstPrivate : ℕ) (body : P → Pr P T Q A U) (prog : Pr P T Q A U)
    (v u : HS T Q A U) (S D : Stacks T A) (n push : ℕ) (run : Exec body prog (mk v S) n (mk u D))
    (hp : Fast.Main.mnProgPush prog ≤ push) (hb : ∀ f, Fast.Main.mnProgPush (body f) ≤ push)
    (free : ∀ i : Fin T, firstPrivate ≤ i.val → S.L i = [] ∧ S.R i = []) :
    let work := (List.finRange T).filter fun i => firstPrivate ≤ i.val
    ∃ z F l, z.user = u.user ∧ l ≤ n+(4*work.length+1+work.length*(6*(push*n))) ∧
      Exec body (.seq prog (clearWorkTapes work)) (mk v S) l (mk z F) ∧
      (∀ i : Fin T, i.val < firstPrivate → F.L i = D.L i ∧ F.R i = D.R i) ∧
      ∀ i : Fin T, firstPrivate ≤ i.val → F.L i = [] ∧ F.R i = [] := by
  intro work
  obtain ⟨z,hz,clear⟩ := clearWorkTapes_exec body work ((List.nodup_finRange _).filter _) u D
  have bound := cleanup_cost_le work run hp hb
  have base : (work.map fun i => 4*(S.L i).length+2*(S.R i).length+4).sum = 4*work.length := by
    have eq := List.map_congr_left (l := work) (f := fun i => 4*(S.L i).length+2*(S.R i).length+4)
      (g := fun _ => 4) (fun i hi => by
        have h := free i (by simpa [work] using hi)
        simp [h])
    rw [eq]
    simp [Nat.mul_comm]
  rw [base] at bound
  exact ⟨z,_,_,hz,Nat.add_le_add_left bound n,Exec.seq run clear,
    fun i hi => by simp [work,Nat.not_le.mpr hi],fun i hi => by simp [work,hi]⟩

theorem placedPackedLeaf_exec (rank g : ℕ) (dim : fields = rank+g) (weight inv : Fin rank → ZMod M)
    (unit : ∀ i, weight i * inv i = 1) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(fields+fields)*W : ℕ) → dest z = blank)
    (original : Fin (M^(fields+fields)*W) → ZMod 2) :
    let coords := (List.finRange fields).filter (fun i => i.val < rank)
    let read := fun a : Fin coords.length => (⟨(coords.get a).val,
      of_decide_eq_true (List.mem_filter.mp (coords.get_mem a)).2⟩ : Fin rank)
    let k : Fin coords.length → Fin ((fields+d)+1) := fun a => (coords.get a).castAdd fields
    let t : Fin coords.length → Fin ((fields+d)+1) := fun a => (coords.get a).rev.natAdd fields
    let Q := leafCapacity ((fields+d)+1)
    let capacity : columnCapacity ≤ Q := le_max_left ..
    let signCapacity : ∀ a, (fieldSignProgram (k a) true).1 ≤ Q := fun a =>
      (Finset.le_sup (f := fun j => (fieldSignProgram j true).1) (Finset.mem_univ (k a))).trans (le_max_right ..)
    let width := fun a => 22+fieldSignSlots (k a)
    let total := Fintype.card (Σ a, Fin (width a))
    let host := ((Fin.castAddEmb (n := 62) (N-35)).trans (Fin.castAddEmb total)).trans (Fin.castAddEmb 1)
    let bank := leafScheduleBank N total (Nat.le_add_left ..)
    let record := binSyms (A := prime) H (1 : ZMod M).val ++ tail
    let archive := (List.ofFn fun i => binSyms (A := prime) H (inv i).val).flatten ++ rest
    let cost := fun a => exchangeTime U (read a).val 0 (k a) (t a) (width a) w W H J
    let ready := fun words => ColumnRecordReady (leafColumn.trans host) H J words SparseRoleCircuit.encode
      (fun _ => blank) dest 0 q original
    let prog := placedLeafProgram (P := P) (U := U) k t (fun a => (read a).val) capacity signCapacity
    let release := prog.seq (Node.usub (host 2) (host 61) (host 0))
    let budget := 1+((List.finRange coords.length).map cost).sum+1+(4*H+4)
    ∀ (body : P → Pr P (62+(N-35)+total+1) Q prime U) v S,
      ready record id S → S.R (host 56) = archive → (∀ j, 62 ≤ j.val → S.L j = [] ∧ S.R j = []) →
      ∃ z F l, ∃ after : Fin (M^(fields+fields)*W) → ZMod 2, z.user = v.user ∧ l ≤ budget ∧
        Exec body release (mk v S) l (mk z F) ∧
        (∀ (hg tg : Fin g → ZMod M) (x : State (Fin rank) (ZMod M)) (j : Fin W),
          let addr := fun y => let t := childFields hg tg y
                               index (Fin.append (fun i : Fin fields => t.1 (i.cast dim))
                                 (fun i : Fin fields => t.2 (i.cast dim))) j
          after (addr (Weighted.child rank weight inv x)) = original (addr x)) ∧
        (∀ k, RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0
          (List.ofFn (SparseRoleCircuit.encode ∘ after)) k) =
          readAt blank (F.L (host 24)) (F.R (host 24)) (k-0)) ∧
        F.R (host 56) = S.R (host 56) ∧
        ∀ h, (∀ i, bank i ≠ h) → F.L h = S.L h ∧ F.R h = S.R h := by
  intro coords read k t Q capacity signCapacity width total host bank record archive cost ready
  have inner := packedLeaf_exec (P := Empty) (U := U) rank weight inv unit H J hm hw hW tail rest dest q
    empty original capacity signCapacity
  unfold CorrectedScheduleRuns at inner
  extract_lets innerWidth innerTotal ports shared slots innerRecord innerWeights innerReady program innerCost at inner
  let positive := lt_of_lt_of_le columnCapacity_pos capacity
  let schedule : Pr Empty (N+1+total+1) Q prime U :=
    (List.finRange coords.length).foldr (fun a rest => .seq (program a) rest) (.act .done)
  intro prog release budget body v S before weights free
  obtain ⟨layout,clean,stored,privateTapes⟩ := leafSchedule_ready total H J record archive _ _ dest 0 q
    original id S before weights free
  have singleton : innerRecord = record := by simp [innerRecord,record,List.ofFn_succ]
  obtain ⟨u,D,n,hu,hn,run,after,spare⟩ := inner Empty.elim (stateLiftDown positive (embDn bank v)) (embStk bank S)
    ⟨singleton.symm ▸ layout,clean,stored⟩ privateTapes
  obtain ⟨z,F,hz,placed,out,projection,frame⟩ := leafSchedule_place_exec total (le_refl Q) positive body schedule v S H J
    record _ _ dest 0 q original _ u D n run (singleton ▸ after.1)
  change n ≤ ((List.finRange coords.length).map cost).sum+1 at hn
  have reciprocal : bank (((Fin.last N).castAdd total).castAdd 1) = host 56 := by
    apply Fin.ext
    rw [show bank = leafScheduleBank N total (Nat.le_add_left ..) from rfl,leafScheduleBank_shared]
    exact leafShared_reciprocal _
  have saved := after.2.2
  rw [← projection] at saved
  change F.R (bank (((Fin.last N).castAdd total).castAdd 1)) = archive at saved
  rw [reciprocal] at saved
  let column := leafColumn.trans host
  obtain ⟨word,layout,action⟩ := out
  have count : (F.R (host 2)).length = H :=
    (congrArg List.length layout.modulus).trans (length_binSyms ..)
  obtain ⟨z',hz',drop⟩ := Node.usub_exec body (host.injective.ne (by decide : (2 : Fin 62) ≠ 61))
    (host.injective.ne (by decide : (2 : Fin 62) ≠ 0)) (host.injective.ne (by decide : (61 : Fin 62) ≠ 0))
    z F (layout.scratch 0 (by decide)).2
  have top : F.R (host 61) = binSyms H (1 : ZMod M).val ++ tail := layout.archive
  have suffix : ((binSyms H (1 : ZMod M).val) ++ tail).drop H = tail := by
    simpa only [length_binSyms] using List.drop_left (l₁ := binSyms H (1 : ZMod M).val) (l₂ := tail)
  rw [count,top,suffix] at drop
  let G := {F with R := Function.update F.R (host 61) tail}
  have keep (h) (ne : h ≠ host 61) : G.R h = F.R h := Function.update_of_ne ne _ _
  have returned : ready tail (fun x => let y := Weighted.child rank (extendLeafWeight weight) (extendLeafWeight inv) (leafFields x); Fin.append (m := fields) (n := fields) y.1 y.2) G := by
    apply ColumnRecordReady.replaceArchive (S := F) (F := G) (bank := column) ⟨word,layout,action⟩ rfl
    · intro i ne
      exact keep _ (column.injective.ne ne)
    · exact Function.update_self (host 61) tail F.R
  have ticks : 1+n+(4*H+4) ≤ budget := by dsimp only [budget]; omega
  obtain ⟨after,output,effect⟩ := packedLeaf_return dim weight inv column H J tail
    SparseRoleCircuit.encode (fun _ => blank) dest 0 q original G returned
  refine ⟨z',G,_,after,hz'.trans (hz.trans hu),ticks,Exec.seq placed drop,effect,fun j => (output.src j).symm,
    (keep _ (host.injective.ne (by decide : (56 : Fin 62) ≠ 61))).trans (saved.trans weights.symm),?_⟩
  intro h off
  have hit := DFunLike.congr_fun (leafSchedule_column total (Nat.le_add_left ..)) (34 : Fin 35)
  have ne : h ≠ host 61 := fun eq => off _ (hit.trans eq.symm)
  exact ⟨(frame h off).1,(keep h ne).trans (frame h off).2⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
