module

public import IntegerMultBounds.MathlibTM2.M6.BitPackedAllocated

/-! Compose packed invocations on the stage owner bank with a single recursive bill. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Each run uses the helper slots installed by its strict prefix in the stage. -/
noncomputable def packedStageEffect (n : Fin 9) (p : Fin 32 × Fin 5) (w B W : ℕ) :=
  let M := prime^w
  let L := B*prime^(64*(w*64))
  let K := M^112*W
  let V := M^16*(L*K)
  let before := (stageRuns.take (stageRuns.idxOf p)).foldl (fun c r => helperChartsAfter n r c) (fun _ => none)
  fun (data out : Fin 142081 → Fin V → ZMod 2) => ∃ packed,
    HelperLabelTrace w L W (scheduledSlotChanges n p before) data packed ∧ InvocationEffect n p.1 p.2 w B K packed out

/-- On the 222 active ports the whole stage has the endpoint of their
unique invocation. Its helper packing leaves the incoming active words intact. -/
theorem packedStage_active (n : Fin 9) (run : Fin 32 × Fin 5) (w B W : ℕ) (x y)
    (trace : stageRuns.foldr (fun k next a => ∃ b, packedStageEffect n k w B W a b ∧ next b)
      (fun a => a = y) x) :
    let port := fun j : Fin 222 => ownerTape n run.1 run.2 (j.castLE (by decide))
    ∃ a b, InvocationEffect n run.1 run.2 w B ((prime^w)^112*W) a b ∧
      (∀ j, a (port j) = x (port j)) ∧ (∀ j, b (port j) = y (port j)) := by
  intro port
  let view := fun z : Fin 142081 → Fin ((prime^w)^16*(B*prime^(64*(w*64))*((prime^w)^112*W))) → ZMod 2 => z ∘ port
  apply (uniqueTraceRead run view (fun u v => ∃ a b,
    InvocationEffect n run.1 run.2 w B ((prime^w)^112*W) a b ∧
    (∀ j, a (port j) = u j) ∧ (∀ j, b (port j) = v j)) (fun k => packedStageEffect n k w B W)
    ?_ ?_ stageRuns stageRuns_nodup x y trace).1 (mem_stageRuns run)
  · rintro x y ⟨a,pack,act⟩
    refine ⟨a,y,act,fun j => labelTrace_off _ _ _ pack _ ?_,fun _ => rfl⟩
    rintro q mem eqn
    obtain ⟨h,_,rfl⟩ := List.mem_map.mp mem
    have same := congrArg Fin.val (ownerTape_injective n run.1 run.2 eqn)
    change 222+h.val = j.val at same
    omega
  · rintro k other x y ⟨a,pack,act⟩
    funext j
    have miss := fun i => otherRunMissesPort n k run other i (j.castLE (by decide)) j.isLt
    apply (act.2 (port j) (Fin.castSucc_ne_last _) miss).trans
    apply labelTrace_off _ _ _ pack
    rintro q mem
    obtain ⟨h,_,rfl⟩ := List.mem_map.mp mem
    exact miss _

open Swap.Modular M8.Exchange in
/-- A span exchange swaps the live halves in its helper slot and fixes
every digit beyond the label. -/
theorem helperFieldCell_exchange (c : PortCertificate) (checked : c.Checked) (slot : Fin 56)
    (w : ℕ) (s : Swap.Shear.State Axis (ZMod (prime^w))) {L W : ℕ} (label : Fin L) (j : Fin W) :
    let digits := helperSlotField c (some slot) w s
    let live := digits ∘ Fin.castAdd 112
    let state : Swap.Shear.State (Fin 8) (ZMod (prime^w)) := (live ∘ Fin.castAdd 8,live ∘ Fin.natAdd 8)
    helperFieldCell (helperSlotField c (some slot) w
      (exchange (reduce (prime^w) (c.span slot (slot+8 : ℕ))) s)) label j =
      helperLabelCell (AffineFieldCoordinates.embed state.swap) label (digits ∘ Fin.natAdd 16) j := by
  intro digits live state
  let H := (reduce (prime^w) (c.helperChart slot (by omega))).transpose
  let u := transform H H s
  let v := transform H H (exchange (reduce (prime^w) (c.span slot (slot+8 : ℕ))) s)
  have swap := helperChartAddress_swap c checked slot (by omega) w s j
  dsimp only at swap
  rw [chartAddress_local _ _ Prod.swap] at swap
  have coord : v = chartHalves.symm ((chartHalves u).1.swap,(chartHalves u).2) :=
    congrArg Prod.fst (chartAddress.injective swap)
  unfold helperFieldCell
  rw [helperSlotField_some]
  change helperLabelCell (((Sum.elim v.1 v.2) ∘ helperDigits) ∘ Fin.castAdd 112) label
    (((Sum.elim v.1 v.2) ∘ helperDigits) ∘ Fin.natAdd 16) j = _
  rw [coord]
  dsimp only [state,live,digits]
  rw [helperSlotField_some]
  congr 1
  · funext i
    refine Fin.addCases (m := 8) (n := 8) (fun a => ?_) (fun a => ?_) i
    all_goals simp only [AffineFieldCoordinates.embed,Fin.addCases_left,Fin.addCases_right,Prod.swap,
      Function.comp_apply,helperDigits,Equiv.trans_apply,@finSumFinEquiv_symm_apply_castAdd 16 112,
      @finSumFinEquiv_symm_apply_castAdd 8 8,@finSumFinEquiv_symm_apply_natAdd 8 8,
      Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr] <;> rfl
  · funext i
    refine Fin.addCases (m := 56) (n := 56) (fun a => ?_) (fun a => ?_) i
    all_goals simp only [Function.comp_apply,helperDigits,Equiv.trans_apply,
      @finSumFinEquiv_symm_apply_natAdd 16 112,@finSumFinEquiv_symm_apply_castAdd 56 56,
      @finSumFinEquiv_symm_apply_natAdd 56 56,Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr] <;> rfl

open Cover in
/-- Reading the final helper through its certified frames recovers the cell
at the slot held on entry, even when this invocation repacked the owner. -/
theorem packedStageEffect_helper (n : Fin 9) (p : Fin 32 × Fin 5) (w B W : ℕ)
    (x y) (step : packedStageEffect n p w B W x y) (h : Fin 439)
    (c : PortCertificate) (checked : c.Checked) (s : Swap.Shear.State Axis (ZMod (prime^w)))
    (g : LabelPadding.Label 64 w) (z : LabelEntry.Cell (copyLabelLayout w B ((prime^w)^112*W)) B)
    (j : Fin W) :
    let before := (stageRuns.take (stageRuns.idxOf p)).foldl (fun a k => helperChartsAfter n k a) (fun _ => none)
    let change := helperSlotChange n p before h
    let label : Fin (B*prime^(64*(w*64))) := ⟨z.b.val*prime^(64*(w*64))+(LabelAddress.address g).val,
      LabelShift.pack_lt z.b.isLt (by simpa only [← pow_mul,show w*(64*64) = 64*(w*64) by omega]
        using (LabelAddress.address g).isLt)⟩
    let slot := helperPosition (n,h)
    ext (y change.1) (helperFieldCell (helperSlotField c (some slot) w
      (M8.Exchange.exchange (Swap.Modular.reduce (prime^w) (c.span slot (slot+8 : ℕ))) s)) label j) =
      ext (x change.1) (helperFieldCell (helperSlotField c change.2.1 w s) label j) := by
  intro before change label slot
  rw [helperFieldCell_exchange c checked slot w s label j]
  let digits := helperSlotField c change.2.2 w s
  let live := digits ∘ Fin.castAdd 112
  let state : Swap.Shear.State (Fin 8) (ZMod (prime^w)) := (live ∘ Fin.castAdd 8, live ∘ Fin.natAdd 8)
  let cell := {z with after := FlatCoordinateLayout.index (digits ∘ Fin.natAdd 16) j}
  let i : Fin 661 := ⟨222+h.val,by omega⟩
  let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n p.1 p.2,ownerTape_injective ..⟩
  change ext (y change.1) (helperLabelCell (AffineFieldCoordinates.embed state.swap) label (digits ∘ Fin.natAdd 16) j) = _
  have output := helperLabelCell_invocation (W := W) (B := B) g cell
    (AffineFieldCoordinates.embed state.swap) (digits ∘ Fin.natAdd 16) j rfl
  rw [← output,ext_apply]
  have physical : phaseRead owner y (labelSpectator g cell) i.val state.swap =
      y change.1 (FlatCoordinateLayout.index (AffineFieldCoordinates.embed state.swap) (labelSpectator g cell)) := by
    simp only [phaseRead,Copy.extendStored,dite_eq_left i.isLt]
    rfl
  rw [← physical]
  obtain ⟨packed,pack,act⟩ := step
  obtain ⟨hi,hf⟩ := Nine.helper_refs h.val h.isLt
  rw [act.otherRead g cell i (Or.inr (by dsimp [i]; omega)),
    show Frames.finalRefs i.val = 1 from hf, fullFrame_read,
    show Frames.initialRefs i.val = 0 from hi, emptyFrame_decode]
  change phaseRead owner packed (labelSpectator g cell) i.val state = _
  have embed : AffineFieldCoordinates.embed state = live := by
    funext k
    exact Fin.addCases (fun a => Fin.addCases_left ..) (fun a => Fin.addCases_right ..) k
  simp only [phaseRead,Copy.extendStored,dite_eq_left i.isLt,embed]
  have addr := helperLabelCell_invocation (W := W) (B := B) g cell live (digits ∘ Fin.natAdd 16) j rfl
  have read := scheduledLabelRead n p before x packed pack h c s label j
  rw [← show (FlatCoordinateLayout.index live (labelSpectator g cell)).val =
    helperFieldCell digits label j from addr, ext_apply] at read
  exact read

open Swap.Modular Matrix in
private theorem hostedExchange_fold (n : Fin 9) (ρ : Role) (w : ℕ) :
    let P := fun k : Fin 32 × Fin 5 => hostSpan n k.1 k.2 ρ
    ∀ s, stageRuns.foldl (fun a k => M8.Exchange.exchange (reduce (prime^w) (P k)) a) s =
      M8.Exchange.exchange (reduce (prime^w) (familySum n ρ)) s := by
  intro P
  let m := prime^w
  have sumAdm {ι : Type} (ls : List ι) (f : ι → Matrix Axis Axis ℚ)
      (ok : ∀ i ∈ ls, Admissible m (f i)) : Admissible m (ls.map f).sum := by
    induction ls with
    | nil => intro i j; simp
    | cons i ls ih =>
      exact ModularFrameSchedule.admissible_add m (ok i List.mem_cons_self)
        (ih (fun j hj => ok j (List.mem_cons_of_mem _ hj)))
  have adm (p) : Admissible m (P p) := by
    apply sumAdm
    intro h _
    split
    · exact portSpan_admissible _ (Nine.port_checked _ (Nat.mod_lt _ (by decide))) _ _ w
    · intro i j; simp
  have zero : reduce m (0 : Matrix Axis Axis ℚ) = 0 := by ext i j; simp [reduce,ratMod]
  rw [← hostSpan_sum n ρ]
  suffices fold : ∀ ks : List (Fin 32 × Fin 5), ks.Nodup → ∀ s,
      ks.foldl (fun a k => M8.Exchange.exchange (reduce m (P k)) a) s =
      M8.Exchange.exchange (reduce m (ks.map P).sum) s from fold _ stageRuns_nodup
  intro ks
  induction ks with
  | nil => intro _ s; simp [zero,M8.Exchange.exchange]
  | cons k ks ih =>
    intro nd s
    obtain ⟨fresh,nd⟩ := List.nodup_cons.mp nd
    have tail := sumAdm ks P (fun j _ => adm j)
    have orth : (ks.map P).sum * P k = 0 := by
      rw [← List.sum_map_mul_right]
      apply List.sum_eq_zero
      intro a ha
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
      exact hostSpan_orthogonal n j k (fun eq => fresh (eq ▸ hj)) ρ
    have reduced := reduce_mul m tail (adm k)
    rw [orth,zero] at reduced
    rw [List.foldl_cons,ih nd,List.map_cons,List.sum_cons,ModularFrameSchedule.reduce_add m (adm k) tail]
    apply Prod.ext <;> simp only [M8.Exchange.exchange,mulVec_add,mulVec_sub,mulVec_mulVec,
      Matrix.sub_mul,Matrix.one_mul,reduced.symm,sub_mulVec,add_mulVec,
      zero_mulVec,one_mulVec] <;> abel

open Cover Swap.Modular M8.Exchange in
/-- Across a stage an inactive owner's parent coordinates undergo exactly the
span exchanges of its helper uses. Its last slot locates the final read. -/
theorem packedStage_inactive (n : Fin 9) (w B W : ℕ) (x y)
    (trace : stageRuns.foldr (fun p next a => ∃ b, packedStageEffect n p w B W a b ∧ next b)
      (fun a => a = y) x) (ρ : Role) (inactive : ρ.bank.val / 2 ≠ BitHosting.activePair n.val)
    (g : LabelPadding.Label 64 w)
    (z : LabelEntry.Cell (copyLabelLayout w B ((prime^w)^112*W)) B) (j : Fin W) :
    let c := Nine.port ρ.port.val
    let tape := ((Fin.cast card_role) (Fintype.equivFin Role ρ)).castSucc
    let label : Fin (B*prime^(64*(w*64))) := ⟨z.b.val*prime^(64*(w*64))+(LabelAddress.address g).val,
      LabelShift.pack_lt z.b.isLt (by simpa only [← pow_mul,show w*(64*64) = 64*(w*64) by omega]
        using (LabelAddress.address g).isLt)⟩
    let chart := fun (runs : List (Fin 32 × Fin 5)) =>
      (runs.foldl (fun a k => helperChartsAfter n k a) (fun _ => none) tape).map helperPosition
    let read := fun word slot s => ext word (helperFieldCell (helperSlotField c slot w s) label j)
    ∀ s, read (y tape) (chart stageRuns) (M8.Exchange.exchange (reduce (prime^w) (familySum n ρ)) s) = read (x tape) none s := by
  classical
  intro c tape label chart read
  let move := fun s (p : Fin 32 × Fin 5) => M8.Exchange.exchange (reduce (prime^w) (hostSpan n p.1 p.2 ρ)) s
  suffices follow : ∀ past runs, past ++ runs = stageRuns → ∀ a,
      runs.foldr (fun p next u => ∃ b, packedStageEffect n p w B W u b ∧ next b) (· = y) a →
      ∀ s, read (y tape) (chart stageRuns) (runs.foldl move s) = read (a tape) (chart past) s from
    fun s => (hostedExchange_fold n ρ w s) ▸ follow [] stageRuns rfl x trace s
  intro past runs
  induction runs generalizing past with
  | nil =>
    intro order a eqn s
    cases eqn
    simp_all
  | cons p ps ih =>
    intro order a trace s
    obtain ⟨b,step,rest⟩ := trace
    rw [List.foldl_cons,ih (past++[p]) (by simpa using order) b rest]
    have nd := order.symm ▸ stageRuns_nodup
    have absent : p ∉ past := fun mem => (List.nodup_append.mp nd).2.2 p mem p List.mem_cons_self rfl
    have pos : stageRuns.idxOf p = past.length := by simp [← order,List.idxOf_append,absent]
    have pre : stageRuns.take (stageRuns.idxOf p) = past := by rw [pos,← order]; simp
    by_cases hit : ∃ h : Fin 439, ownerTape n p.1 p.2 ⟨222+h.val,by omega⟩ = tape
    · have eqn := hit.choose_spec
      have role : hostRole n p.1 p.2 hit.choose = ρ := by
        have same := (Fintype.equivFin Role).injective (Fin.cast_injective _ (Fin.castSucc_injective _ eqn))
        simpa [owner] using same
      have portEq := congrArg (fun r : Role => r.port.val) role
      have spanEq : hostSpan n p.1 p.2 ρ = helperSpan n hit.choose := by
        apply sum_single _ List.nodup_range _ _ _ (List.mem_range.mpr hit.choose.isLt) role
        intro h hm hh
        have bound := List.mem_range.mp hm
        have same := owner_injective n p.1 p.2 (222+h) (by omega) (222+hit.choose.val) (by omega)
          (by simpa [owner] using hh.trans role.symm)
        omega
      have align : helperSpan n hit.choose = c.span (helperPosition (n,hit.choose)) ((helperPosition (n,hit.choose) : ℕ)+8) := by
        unfold helperSpan
        rw [show (IntegerMultBounds.MathlibTM2.M6.BitNode.slotOf n hit.choose).copy % 111 = ρ.port.val from portEq]
        rfl
      have atSlot := packedStageEffect_helper n p w B W a b step hit.choose c (Nine.port_checked _ ρ.port.isLt) s g z j
      dsimp only [helperSlotChange] at atSlot
      simp only [pre,eqn] at atSlot
      simpa only [read,move,chart,List.foldl_append,List.foldl_cons,List.foldl_nil,
        helperChartsAfter,dif_pos hit,Option.map_some,spanEq,align] using atSlot
    · have miss (i : Fin 661) : ownerTape n p.1 p.2 i ≠ tape := by
        intro eqn
        have same : owner n p.1 p.2 i = ρ :=
          (Fintype.equivFin Role).injective (Fin.cast_injective _ (Fin.castSucc_injective _ eqn))
        by_cases data : i.val < 222
        · simp only [owner,data,ite_true] at same
          exact inactive (same ▸ side_pair n p.1 p.2 _ (by unfold regSide; split <;> omega) _)
        · apply hit
          refine ⟨⟨i.val-222,by omega⟩,?_⟩
          convert eqn using 2 <;> apply Fin.ext <;> dsimp <;> omega
      obtain ⟨packed,pack,act⟩ := step
      have fixed := (act.2 tape (Fin.castSucc_ne_last _) miss).trans (labelTrace_off _ _ _ pack tape (by
        rintro q mem
        obtain ⟨h,_,rfl⟩ := List.mem_map.mp mem
        exact miss _))
      have zero : hostSpan n p.1 p.2 ρ = 0 := by
        apply sum_none
        intro h mem hosted
        apply hit
        exact ⟨⟨h,List.mem_range.mp mem⟩,by simp [ownerTape,owner,hosted,tape]⟩
      have reduced : reduce (prime^w) (0 : Matrix Axis Axis ℚ) = 0 := by
        ext a b
        simp [reduce,ratMod]
      simp only [fixed,zero,reduced,chart,List.foldl_append,List.foldl_cons,List.foldl_nil,helperChartsAfter,move,dif_neg hit,M8.Exchange.exchange,Matrix.zero_mulVec,sub_zero,Matrix.one_mulVec,zero_add,add_zero,Prod.mk.eta]

noncomputable def stageFinalSlot (n : Fin 9) (t : Fin 142081) : Option (Fin 56) :=
  (stageRuns.foldl (fun a k => helperChartsAfter n k a) (fun _ => none) t).map helperPosition

open Cover Swap.Modular in
/-- After slot restoration both sides of the inactive stage read use caller coordinates. -/
theorem restoredStage_inactive (n : Fin 9) (w B W : ℕ) (x y out)
    (trace : stageRuns.foldr (fun p next a => ∃ b, packedStageEffect n p w B W a b ∧ next b)
      (fun a => a = y) x)
    (restore : HelperLabelTrace w (B*prime^(64*(w*64))) W (restoreSlotChanges (stageFinalSlot n)) y out)
    (ρ : Role) (inactive : ρ.bank.val / 2 ≠ BitHosting.activePair n.val)
    (g : LabelPadding.Label 64 w)
    (z : LabelEntry.Cell (copyLabelLayout w B ((prime^w)^112*W)) B) (j : Fin W) :
    let c := Nine.port ρ.port.val
    let tape := ((Fin.cast card_role) (Fintype.equivFin Role ρ)).castSucc
    let label : Fin (B*prime^(64*(w*64))) := ⟨z.b.val*prime^(64*(w*64))+(LabelAddress.address g).val,
      LabelShift.pack_lt z.b.isLt (by simpa only [← pow_mul,show w*(64*64) = 64*(w*64) by omega]
        using (LabelAddress.address g).isLt)⟩
    let read := fun word s => ext word (helperFieldCell (helperSlotField c none w s) label j)
    ∀ s, read (out tape) (M8.Exchange.exchange (reduce (prime^w) (familySum n ρ)) s) = read (x tape) s := by
  intro c tape label read s
  exact (restoreSlot_read (k := 142081) (w := w) (L := B*prime^(64*(w*64))) (W := W) (stageFinalSlot n) restore tape c _ label j).trans
    (packedStage_inactive n w B W x y trace ρ inactive g z j s)

theorem restoredStage_activePort (n : Fin 9) (run : Fin 32 × Fin 5) (j : Fin 222)
    {w L W V : ℕ} {data out : Fin 142081 → Fin V → ZMod 2}
    (restore : HelperLabelTrace w L W (restoreSlotChanges (stageFinalSlot n)) data out) :
    let t := ownerTape n run.1 run.2 (j.castLE (by decide))
    out t = data t := by
  intro t
  apply restoreSlot_off (k := 142081) (w := w) (L := L) (W := W) (V := V) (stageFinalSlot n) restore
  unfold stageFinalSlot
  rw [(helperCharts_unvisited n stageRuns t).mpr ?_]
  · rfl
  intro p _ h eqn
  by_cases same : p = run
  · subst p
    have sameReg := congrArg Fin.val (ownerTape_injective n run.1 run.2 eqn)
    change 222+h.val = j.val at sameReg
    omega
  · exact otherRunMissesPort n p run same _ _ j.isLt eqn

private def appendPrivate {t a n : ℕ} (S : Stacks t a) (words : Fin n → List (Fin (a+4))) : Stacks (t+n) a :=
  {S with L := Fin.addCases S.L (fun _ => []), R := Fin.addCases S.R words}

/-- A packed invocation's extra private tapes have a literal initial state:
row headers, three scalar inputs, and blank arithmetic and leaf workspaces. -/
theorem packedInvocationFrame [M8.Machine.Net] {t : ℕ} (fan : Fin (142081+2) ↪ Fin t)
    (prepared : Stacks t prime) (row : Descriptor) (w : ℕ) :
    let N := LeafCore.small
    let caller := (Fin.castAddEmb 273 (n := t+41)).trans (Fin.castAddEmb N)
    let original := (Fin.castAddEmb 41 (n := t)).trans caller
    let hdr := fun i : Fin 6 => (i.castAdd 35).natAdd t
    let regs := (Fin.natAddEmb 6 (m := 35)).trans (Fin.natAddEmb t)
    let M := prime^(w+1)
    ∃ initial : Stacks (((t+41)+273)+N) prime, embStk original initial = prepared ∧
      ∀ S : Stacks (((t+41)+273)+N) prime,
      (∀ j, (∀ h, (fan.trans original) h ≠ j) → S.L j = initial.L j ∧ S.R j = initial.R j) →
      (∀ k, (∀ h, fan h ≠ k) → S.L (original k) = prepared.L k ∧ S.R (original k) = prepared.R k) ∧
      S.R (caller (regs 2)) = binSyms M.size M ∧ S.R (caller (regs 28)) = binSyms 1 1 ∧
      (S.R (caller (regs 33))).length = w ∧
      (∀ i, S.R (caller (hdr i)) = (Routines.hdr row i).map bitSymbol) ∧
      (∀ j : Fin 273, S.L ((j.natAdd (t+41)).castAdd N) = [] ∧ S.R ((j.natAdd (t+41)).castAdd N) = []) ∧
      ∀ j : Fin N, S.L (j.natAdd ((t+41)+273)) = [] ∧ S.R (j.natAdd ((t+41)+273)) = [] := by
  intro N caller original hdr regs M
  let scalars := fun i : Fin 35 => if i = 2 then binSyms (A := prime) M.size M else if i = 28 then binSyms 1 1
    else if i = 33 then List.replicate w blank else []
  let init := appendPrivate (appendPrivate (appendPrivate prepared
    (Fin.addCases (fun i => (Routines.hdr row i).map bitSymbol) scalars)) (fun _ : Fin 273 => [])) (fun _ : Fin N => [])
  refine ⟨init,?_,?_⟩
  · cases prepared
    simp only [init,original,caller,embStk,appendPrivate,Function.comp_def,Function.Embedding.trans_apply,
      Fin.castAddEmb_apply,Fin.addCases_left]
  intro S fresh
  have external (j) (high : t ≤ j.val) := fresh j (fun h eq => by
    have v := congrArg Fin.val eq
    change (fan h).val = j.val at v
    omega)
  have kept (k : Fin t) (outside : ∀ h, fan h ≠ k) := fresh (original k) (fun h => original.injective.ne (outside h))
  constructor
  · intro k outside
    simpa only [init,original,caller,Function.Embedding.trans_apply,Fin.castAddEmb_apply,appendPrivate,
      Fin.addCases_left] using kept k outside
  have scalar (i : Fin 35) : S.R (caller (regs i)) = scalars i := by
    have h := (external (caller (regs i)) (by change t ≤ t+(6+i.val); omega)).2
    simpa only [init,appendPrivate,caller,regs,Function.Embedding.trans_apply,Fin.castAddEmb_apply,
      Fin.natAddEmb_apply,Fin.addCases_left,Fin.addCases_right] using h
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa [scalars] using scalar 2
  · simpa [scalars] using scalar 28
  · rw [scalar]; simp [scalars]
  · intro i
    have h := (external (caller (hdr i)) (by change t ≤ t+i.val; omega)).2
    simpa only [init,appendPrivate,caller,hdr,Function.Embedding.trans_apply,Fin.castAddEmb_apply,
      Fin.addCases_left,Fin.addCases_right] using h
  · intro j
    simpa only [init,appendPrivate,Fin.addCases_left,Fin.addCases_right] using
      external ((j.natAdd (t+41)).castAdd N) (by change t ≤ t+41+j.val; omega)
  · intro j
    simpa only [init,appendPrivate,Fin.addCases_right] using
      external (j.natAdd ((t+41)+273)) (by change t ≤ t+41+273+j.val; omega)

theorem packedStageRuns_exec [M8.Machine.Net] (n : Fin 9) (tapes : Fin 32 × Fin 5 → ℕ)
    (ports : ∀ i, Fin (142081+2) ↪ Fin (tapes i)) :
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ i, Fin (tapes i) ↪ Fin T),
    (∀ i j, bank i (ports i j) = fan j) ∧
    ∀ {P U : Type} {Q w B W : ℕ} (body : ∀ i, P → Pr P (tapes i) Q prime U)
      (code : ∀ i, Pr P (tapes i) Q prime U) (C : Fin 32 × Fin 5 → ℝ)
      (localCost : Fin 32 × Fin 5 → ℕ) (childTime : ℕ → ℕ)
      (initial : ∀ i, Stacks (tapes i) prime) (shared : Stacks (142081+2) prime),
    let V := (prime^w)^16*(B*prime^(64*(w*64))*((prime^w)^112*W))
    let packCost := fun i => C i*((V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)
    let children := fun i => ((List.range' (stageChildStart n+runChildStart i) Geometry.Moves.localPaid.length).map childTime).sum
    (∀ i (x : Fin 142081 → Fin V → ZMod 2) u S, HelperFan (ports i) x S →
      (∀ j, (∀ h, ports i h ≠ j) → S.L j = (initial i).L j ∧ S.R j = (initial i).R j) →
      ∃ z F t y, Exec (body i) (code i) (mk u S) t (mk z F) ∧ (t : ℝ) ≤ packCost i + (localCost i + children i : ℕ) ∧
        z.user = u.user ∧ HelperFan (ports i) y F ∧ packedStageEffect n i w B W x y) →
    let table := fun g : (Fin 32 × Fin 5) × P => embProg (bank g.1) (Prod.mk g.1) (body g.1 g.2)
    let placed := fun i => embProg (bank i) (Prod.mk i) (code i)
    ∃ prepared : Stacks T prime, embStk fan prepared = shared ∧
    ∀ x u S, HelperFan fan x S →
      (∀ j, (∀ h, fan h ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
      ∃ z F t y, Exec table (Prog.seqList (stageRuns.map placed)) (mk u S) t (mk z F) ∧
        t ≤ (stageRuns.map (fun i => ⌈packCost i⌉₊ + localCost i)).sum +
          ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map childTime).sum+1 ∧
        z.user = u.user ∧ HelperFan fan y F ∧
        stageRuns.foldr (fun i next a => ∃ b, packedStageEffect n i w B W a b ∧ next b) (fun a => a = y) x := by
  obtain ⟨T,fan,bank,selected,build⟩ := scheduledBanks_exec tapes ports
  refine ⟨T,fan,bank,selected,?_⟩
  intro P U Q w B W body code C localCost childTime initial shared V packCost children run table placed
  let ready := fun (x : Fin 142081 → Fin V → ZMod 2) (s : Stacks (142081+2) prime) =>
    RepT (PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0)
      (SparseRoleCircuit.encoded x) (FlatCoordinateSchedule.bits V)) s.L s.R
  let localBill := fun i => ⌈packCost i⌉₊ + localCost i
  obtain ⟨prepared,owners,stage⟩ := build body code ready (fun i => packedStageEffect n i w B W)
    (fun i => localBill i + children i) initial shared (by
      intro i x u S rep fresh
      obtain ⟨z,F,t,y,exec,paid,user,done,act⟩ := run i x u S rep fresh
      refine ⟨z,F,t,y,exec,?_,user,done,act⟩
      have bound := paid.trans (add_le_add (Nat.le_ceil (packCost i)) (le_refl _))
      dsimp only [localBill]
      rw [Nat.add_assoc]
      exact_mod_cast bound)
  refine ⟨prepared,owners,?_⟩
  intro x u S rep fresh
  obtain ⟨z,F,t,y,exec,paid,user,done,acts⟩ := stage stageRuns stageRuns_nodup x u S rep fresh
  refine ⟨z,F,t,y,exec,?_,user,done,acts⟩
  have sum (ls : List (Fin 32 × Fin 5)) :
      (ls.map (fun i => localBill i + children i)).sum = (ls.map localBill).sum + (ls.map children).sum := by
    induction ls with
    | nil => rfl
    | cons i ls ih => simp only [List.map_cons,List.sum_cons,ih]; omega
  rwa [sum,show (stageRuns.map children).sum = _ from scheduledChildBill (fun _ => Geometry.Moves.localPaid)
    childTime stageRuns stageRuns_nodup (stageChildStart n)] at paid

def PackedAllocatedStage [M8.Machine.Net] (n : Fin 9) : Prop :=
    let edges := Geometry.Moves.phaseEdges.filter positiveMove
    let R := Fin 32 × Fin 5
    let I := Fin edges.length
    let J := Fin Copy.lifecycles.length
    let child := fun (k : R) (i : I) => phaseChildPositions.choose (n,k,i)
    ∃ (moveTapes : R → I → ℕ) (regsPort : ∀ k i, Fin (rowSwapBlock.tapes+35) ↪ Fin (moveTapes k i))
      (phaseT : R → ℕ) (states : ℕ) (moveBank : ∀ k i, Fin (moveTapes k i) ↪ Fin (phaseT k))
      (copyTapes : R → J → ℕ) (copyRegs : ∀ k j, Fin (rowSwapBlock.tapes+35) ↪ Fin (copyTapes k j)),
    let tapes := fun k (i : Option J) => i.elim (phaseT k) (copyTapes k)
    ∃ (runT : R → ℕ) (bank : ∀ k i, Fin (tapes k i) ↪ Fin (runT k))
      (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (runBank : ∀ k : R, Fin (((runT k+41)+273)+LeafCore.small) ↪ Fin T),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q →
    ∀ (localMove : ∀ k i, P → Pr P (moveTapes k i) Q prime U) (f : R → I → P)
      (localCopy : ∀ k j, I × P → Pr (I × P) (copyTapes k j) Q prime U) (copyProc : R → J → I × P),
    let moveBody := fun k (g : I × P) => embProg (moveBank k g.1) (fun h => (g.1,h)) (localMove k g.1 g.2)
    let localBody := fun k => Option.rec (motive := fun i => I × P → Pr (I × P) (tapes k i) Q prime U)
      (moveBody k) (localCopy k)
    let runBody := fun k (g : Option J × (I × P)) => embProg (bank k g.1) (fun h => (g.1,h)) (localBody k g.1 g.2)
    let original := fun k : R => ((Fin.castAddEmb 41 (n := runT k)).trans (Fin.castAddEmb 273)).trans (Fin.castAddEmb LeafCore.small)
    let body := fun g : R × (Option J × (I × P)) => embProg (runBank g.1) (Prod.mk g.1) (embProg (original g.1) id (runBody g.1 g.2))
    let stageBank := (Fin.castAddEmb 41 (n := T)).trans ((Fin.castAddEmb 273).trans (Fin.castAddEmb LeafCore.small))
    let full := fan.trans stageBank
    let outer := fun g => embProg stageBank id (body g)
    ∃ (restoreRate : ℝ) (packRate : R → ℝ) (base swaps : R → I → ℕ) (copyBase copySwaps copyLeaf copyFixed : R → J → ℕ), ∀ (node : Descriptor) (w B rows : ℕ),
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    let M := prime^(w+1)
    let K := M^112*(node.beforeRows*rows*node.between*node.afterD)
    let W := B*prime^(64*((w+1)*64))*K
    let V := M^16*W
    0 < W → ∀ (record : R → I → List (Fin (prime+4))) (copyRecord : R → J → List (Fin (prime+4))),
    let desc := fun k i => scheduledChild prime node (child k i)
    ∃ position : ∀ k i, Fin (volume prime (desc k i)) ≃ Fin V,
    (∀ k i h, (position k i h).val = (CopyChildLayout.packActive (desc k i) h).val) ∧
    let copyChild := fun (k : R) (j : J) => copyChildPosition (n,k,j)
    let copyDesc := fun k j => scheduledChild prime node (copyChild k j)
    ∃ copyPosition : ∀ k j, Fin (volume prime (copyDesc k j)) ≃ Fin V,
    (∀ k j h, (copyPosition k j h).val = (CopyChildLayout.packActive (copyDesc k j) h).val) ∧
    ∀ childTime : ℕ → ℕ,
    (∀ k i, ScheduledChildExec node (desc k i) w W (regsPort k i) (record k i) (position k i)
      (localMove k i) (f k i) (childTime (child k i).val)) →
    (∀ k i, ScheduledChildExec node (copyDesc k i) w W (copyRegs k i) (copyRecord k i) (copyPosition k i)
      (localCopy k i) (copyProc k i) (childTime (copyChild k i).val)) →
    ∀ shared : Stacks (142081+2) prime,
    let represented := fun {t : ℕ} (e : Fin (142081+2) ↪ Fin t) (data : Fin 142081 → Fin V → ZMod 2) (S : Stacks t prime) =>
      RepT (PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0)
        (SparseRoleCircuit.encoded data) (FlatCoordinateSchedule.bits V)) (embStk e S).L (embStk e S).R
    let copyWork := fun k j => (copyBase k j+copySwaps k j*swapVolumeRate w)*V +
      copyLeaf k j * M8.RevMachine.LeafCore.coreCost V ((w+1)*64) + copyFixed k j
    let start := fun k => stageChildStart n + runChildStart k
    let work := fun k (j : ℕ) => if h : j-start k < edges.length then
      (base k ⟨j-start k,h⟩ + swaps k ⟨j-start k,h⟩ * swapVolumeRate w)*V else 0
    let localCost := fun k => ((sectionD++sectionA++(sectionB++sectionC)).map (fun g => 76*g.toCircuit.terms.length*V*(142081+7)+6)).sum +
      ((List.range' (start k) edges.length).map (work k)).sum + (List.ofFn (copyWork k)).sum + 3
    ∃ prepared : Stacks (((T+41)+273)+LeafCore.small) prime, embStk full prepared = shared ∧
    ∃ code, ∀ data u S, represented full data S →
      (∀ k, (∀ h, full h ≠ k) → S.L k = prepared.L k ∧ S.R k = prepared.R k) →
      ∃ z F t packed out, Exec outer code (mk u S) t (mk z F) ∧
      t ≤ ⌈restoreRate*((V : ℝ)*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)⌉₊ + ((stageRuns.map (fun k => ⌈packRate k*((V : ℝ)*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)⌉₊ + localCost k)).sum +
        ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map childTime).sum+1) ∧
        z.user = u.user ∧ represented full out F ∧
        stageRuns.foldr (fun k next a => ∃ b, packedStageEffect n k (w+1) B
          (node.beforeRows*rows*node.between*node.afterD) a b ∧ next b) (fun a => a = packed) data ∧
        HelperLabelTrace (w+1) node.beforeH (node.beforeRows*rows*node.between*node.afterD)
          (restoreSlotChanges (stageFinalSlot n)) packed out

theorem packedAllocatedStage_host [M8.Machine.Net] (n : Fin 9) : PackedAllocatedStage n := by
  classical
  unfold PackedAllocatedStage
  intro edges R I J child
  choose mt regs phaseT qs phaseFan mb ct cp cr runT rf bank phaseShared copyShared run using
    fun k : R => packedAllocatedInvocation_host n k.1 k.2
  let original := fun k : R => ((Fin.castAddEmb 41 (n := runT k)).trans (Fin.castAddEmb 273)).trans (Fin.castAddEmb LeafCore.small)
  obtain ⟨T,fan,runBank,selected,stage⟩ := packedStageRuns_exec n _ (fun k => (rf k).trans (original k))
  refine ⟨mt,regs,phaseT,max columnCapacity (Finset.univ.sup qs),mb,ct,cr,?_⟩
  intro tapes
  refine ⟨runT,bank,T,fan,runBank,?_⟩
  intro P U Q fits localMove f localCopy copyProc moveBody localBody runBody orig body stageBank full outer
  have cap : columnCapacity ≤ Q := (le_max_left ..).trans fits
  have capacity (k : R) : qs k ≤ Q := (Finset.le_sup (Finset.mem_univ k)).trans ((le_max_right ..).trans fits)
  choose C base swaps cb cs cl cf invoke using fun k => run k (capacity k) (localMove k) (f k) (localCopy k) (copyProc k)
    (stageRuns.take (stageRuns.idxOf k)) cap
  let hdr := fun i : Fin 6 => (i.castAdd 35).natAdd T
  let regs' := (Fin.natAddEmb 6 (m := 35)).trans (Fin.natAddEmb T)
  obtain ⟨restore,D,finish⟩ := parentSlotChanges_exec (restoreSlotChanges (stageFinalSlot n))
    (fan.trans (Fin.castAddEmb 41)) hdr regs' cap outer
  refine ⟨D,C,base,swaps,cb,cs,cl,cf,?_⟩
  intro node w B rows width split label M K W V pos record copyRecord desc
  choose position coords copyPosition copyCoords ready using fun k =>
    invoke k node w B rows width split label pos (record k) (copyRecord k)
  refine ⟨position,coords,?_⟩
  intro copyChild copyDesc
  refine ⟨copyPosition,copyCoords,?_⟩
  intro childTime recurse copyRecurse shared represented copyWork start work localCost
  choose initial owner code execute using fun k => ready k childTime (recurse k) (copyRecurse k) shared
  let row := role node 142080
  choose frame frameView privateFrame using fun k => packedInvocationFrame (rf k) (initial k) row w
  let localTable := fun k g => embProg (original k) id (runBody k g)
  obtain ⟨prepared,owners,runStage⟩ := stage (w := w+1) (B := B) (W := node.beforeRows*rows*node.between*node.afterD)
    localTable code C localCost childTime frame shared (by
      intro k x u S live fresh
      obtain ⟨privateRegs,radix,unit,clock,words,free,scratch⟩ := privateFrame k S fresh
      obtain ⟨z,F,t,packed,out,exec,paid,user,done,effect,trace⟩ := execute k x u S live privateRegs radix unit clock words free scratch
      refine ⟨z,F,t,out,exec,?_,user,done,packed,?_,effect⟩
      · apply paid.trans_eq
        dsimp only [localCost,copyWork,start,work,V,W,K,M]
        rw [Nat.add_right_comm _ _ 3]
      · rw [label] at trace
        exact trace)
  obtain ⟨init,view,entry⟩ := packedInvocationFrame fan prepared row w
  let sweep := Prog.seqList (stageRuns.map fun k => embProg (runBank k) (Prod.mk k) (code k))
  refine ⟨init,?_,.seq (embProg stageBank id sweep) restore,?_⟩
  · change embStk fan (embStk stageBank init) = shared
    rw [view,owners]
  intro data u S live fresh
  obtain ⟨inside,radix,unit,clock,words,free,scratch⟩ := entry S fresh
  obtain ⟨v,A,m,a,exec,paid,user,done,events⟩ :=
    runStage data (embDn stageBank u) (embStk stageBank S) live inside
  obtain ⟨v',A',placed,_,same,project,off⟩ := exec_emb (ι := id) (body' := outer)
    stageBank.injective (fun _ => rfl) exec u rfl S rfl
  rw [← project] at done
  have keep (j) (high : T ≤ j.val) := off j (fun i eqn => by
    have h := congrArg Fin.val eqn
    change i.val = j.val at h
    omega)
  have rowCount : row.rows = rows := by
    change node.rows/142080 = rows
    rw [split,Nat.mul_div_cancel_left _ (by decide)]
  have tailPos : 0 < node.beforeRows*rows*node.between*node.afterD :=
    Nat.pos_of_mul_pos_left (Nat.pos_of_mul_pos_left pos)
  have hrow : row.Positive := by
    exact ⟨Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right tailPos)),
      rowCount ▸ Nat.pos_of_mul_pos_left (Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right tailPos)),
      label ▸ Nat.pos_of_mul_pos_right pos,Nat.pos_of_mul_pos_left (Nat.pos_of_mul_pos_right tailPos),
      Nat.pos_of_mul_pos_left tailPos⟩
  have size : V = M^16*(row.beforeH*(M^112*(row.beforeRows*row.rows*row.between*row.afterD))) := by
    rw [rowCount]; change _ = M^16*(node.beforeH*K); rw [label]
  obtain ⟨z,F,t,out,uz,rest,price,representedOut,trace,_⟩ := finish row w V hrow size a v' A'
    ((keep _ (by change T ≤ T+(6+2); omega)).2.trans radix)
    ((keep _ (by change T ≤ T+(6+28); omega)).2.trans unit)
    (by rw [(keep _ (by change T ≤ T+(6+33); omega)).2]; exact clock)
    (fun i => (keep _ (by change T ≤ T+i.val; omega)).2.trans (words i))
    (fun j => ⟨(keep _ (by change T ≤ T+41+j.val; omega)).1.trans (free j).1,
      (keep _ (by change T ≤ T+41+j.val; omega)).2.trans (free j).2⟩)
    (fun j => ⟨(keep _ (by change T ≤ T+41+273+j.val; omega)).1.trans (scratch j).1,
      (keep _ (by change T ≤ T+41+273+j.val; omega)).2.trans (scratch j).2⟩) done
  refine ⟨z,F,m+t,a,out,Exec.seq placed rest,?_,uz.trans (same.trans user),representedOut,events,?_⟩
  · have bound : t ≤ ⌈D*((V : ℝ)*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)⌉₊ := by simpa only [Nat.ceil_natCast] using Nat.ceil_le_ceil price
    rw [Nat.add_comm m t]
    exact Nat.add_le_add bound paid
  · rwa [rowCount] at trace

end IntegerMultBounds.MathlibTM2.M6.BitNode
