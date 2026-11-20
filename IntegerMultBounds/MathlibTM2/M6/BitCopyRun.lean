module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthOriginalRun
public import IntegerMultBounds.MathlibTM2.M6.ModularScatter
public import IntegerMultBounds.MathlibTM2.M6.BitInvocation
public import IntegerMultBounds.Machine.ExactFrame
public import IntegerMultBounds.Networks.AffineFieldBijective
public import IntegerMultBounds.Machine.ArbitraryWidthSliceTranspose
public import IntegerMultBounds.Networks.AffineFieldCoordinates
public import IntegerMultBounds.Machine.SparseRoleCircuit

/-! Copy, fan out, and clear the PR589 temporary on the scheduled owner tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open IntegerMultBounds.Networks.Certificates.PR589
variable {a : ℕ}

private theorem fanout {t N : ℕ} (src : Fin t) (targets : List (Fin t)) (fresh : src ∉ targets)
    (unique : targets.Nodup) (data : Fin t → Fin N → ZMod 2) :
    let gates := targets.attach.map fun dst => (⟨src,dst.val,fun h => fresh (h ▸ dst.property)⟩ : PointwiseRoleGate.Gate t)
    PointwiseRoleCircuit.execute (PointwiseBinary.xorSymbol (a := a)) gates (SparseRoleCircuit.encoded data) =
      SparseRoleCircuit.encoded (fun j i => if j ∈ targets then data j i + data src i else data j i) := by
  induction targets generalizing data with
  | nil => rfl
  | cons j js ih =>
    have off : src ≠ j := fun eq => fresh (eq ▸ List.mem_cons_self)
    have tail : src ∉ js := fun mem => fresh (List.mem_cons_of_mem _ mem)
    let next := Function.update data j (fun i => data j i + data src i)
    have step : PointwiseRoleGate.applyGate ⟨src,j,off⟩ PointwiseBinary.xorSymbol
        (SparseRoleCircuit.encoded (a := a) data) = SparseRoleCircuit.encoded next := by
      funext k i
      by_cases h : k = j
      · subst k
        simp [PointwiseRoleGate.applyGate,SparseRoleCircuit.encoded,next,SparseRoleCircuit.encode_add]
      · simp [PointwiseRoleGate.applyGate,SparseRoleCircuit.encoded,next,h]
    simp only [List.attach_cons,List.map_cons,List.map_map,PointwiseRoleCircuit.execute,step]
    trans SparseRoleCircuit.encoded (fun k i => if k ∈ js then next k i + next src i else next k i)
    · exact ih tail unique.of_cons next
    congr 1
    funext k i
    by_cases eq : k = j
    · subst k
      simp [next,unique.notMem]
    · simp [next,eq,off]

/-- Fan out the common-frame temporary to every target of a selected COPY
window. All retained owners outside that window keep their original streams. -/
theorem copyAdds_hoare (n : Fin 9) (r : Fin 32) (d : Fin 5) (life : Copy.Lifecycle)
    (scheduled : life ∈ Copy.lifecycles) :
    let regs := life.targets.attach.map fun j => (⟨j.val,((Copy.target_bounds life scheduled _ j.property).2.trans (by decide : 222 < 661))⟩ : Fin 661)
    let tapes := regs.map (ownerTape n r d)
    ∃ (states : ℕ) (program : Program (142081+2) states a), ∀ {N : ℕ} (data : Fin 142081 → Fin N → ZMod 2)
      (background : Fin 142081 → ℤ → Fin (a+4)) (origins : Fin 142081 → ℤ)
      (bs : List Bool), Counter.value bs = N →
      HoareTime program (fun w => w = PointwiseRoleGate.bank background origins (SparseRoleCircuit.encoded data) bs)
        (fun w => w = PointwiseRoleGate.bank background origins (SparseRoleCircuit.encoded
          (fun j i => if j ∈ tapes then data j i + data (Fin.last 142080) i else data j i)) bs)
        (life.targets.length*(14*N+14*bs.length+34)) := by
  intro regs tapes
  have unique : regs.Nodup := by
    apply List.Nodup.of_map (f := Fin.val)
    simpa [regs,List.map_map,Function.comp_def] using (Copy.wellformed life scheduled).1
  have nodup := unique.map (ownerTape_injective n r d)
  have fresh : Fin.last 142080 ∉ tapes := by
    intro mem
    obtain ⟨j,_,eq⟩ := List.mem_map.mp mem
    exact Fin.castSucc_ne_last _ eq
  let gates := tapes.attach.map fun dst => (⟨Fin.last 142080,dst.val,fun h => fresh (h ▸ dst.property)⟩ : PointwiseRoleGate.Gate 142081)
  refine ⟨_,PointwiseRoleCircuit.program (PointwiseBinary.xorSymbol (a := a)) gates,?_⟩
  intro N data background origins bs count
  have exec := PointwiseRoleCircuit.circuit_hoare PointwiseBinary.xorSymbol gates background origins
    (SparseRoleCircuit.encoded data) bs count
  have action := fanout (a := a) _ tapes fresh nodup data
  change PointwiseRoleCircuit.execute _ gates _ = _ at action
  rw [action] at exec
  simpa only [gates,tapes,regs,List.length_map,List.length_attach] using exec

/-- Row-major tape address used by the flat coordinate stages, with the
spectator record following the two field halves. -/
noncomputable def copyAddress {Q W : ℕ} [NeZero Q] :
    Fin (Q^16*W) ≃ Swap.Shear.State (Fin 8) (ZMod Q) × Fin W :=
  let halves : Swap.Shear.State (Fin 8) (ZMod Q) ≃ (Fin 16 → ZMod Q) :=
    { toFun := AffineFieldCoordinates.embed
      invFun := fun x => (fun i => x (Fin.castAdd 8 i), fun i => x (Fin.natAdd 8 i))
      left_inv := fun s => Prod.ext (funext (AffineFieldCoordinates.embed_h s)) (funext (AffineFieldCoordinates.embed_d s))
      right_inv := fun x => by
        funext i
        exact Fin.addCases (fun _ => Fin.addCases_left _)
          (fun _ => Fin.addCases_right _) i }
  (((halves.trans FlatCoordinateLayout.rankEquiv).prodCongr (Equiv.refl (Fin W))).trans
    finProdFinEquiv).symm

@[simp] theorem copyAddress_index {Q W : ℕ} [NeZero Q]
    (s : Swap.Shear.State (Fin 8) (ZMod Q)) (j : Fin W) :
    copyAddress.symm (s,j) = FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j := rfl

/-- Split a charted parent address into its eight active axes and its eight
exterior blocks of seven, in each half. -/
def chartHalves {R : Type*} : Swap.Shear.State Nine.Axis R ≃
    Swap.Shear.State (Fin 8) R × Swap.Shear.State Nine.Exterior R where
  toFun s := ((s.1 ∘ Sum.inl,s.2 ∘ Sum.inl),(s.1 ∘ Sum.inr,s.2 ∘ Sum.inr))
  invFun p := (Sum.elim p.1.1 p.2.1,Sum.elim p.1.2 p.2.2)
  left_inv s := by
    apply Prod.ext <;> funext i <;> cases i <;> rfl
  right_inv _ := rfl

/-- Serialize all 112 exterior coordinates into the spectator record. Each
exterior half uses the source's block-major ordering on the 8 by 7 axes. -/
noncomputable def chartAddress {Q W : ℕ} [NeZero Q] :
    Swap.Shear.State Nine.Axis (ZMod Q) × Fin W ≃ Fin (Q^16*(Q^112*W)) :=
  let half : (Nine.Exterior → ZMod Q) ≃ (Fin 56 → ZMod Q) :=
    Equiv.arrowCongr finProdFinEquiv (Equiv.refl _)
  let exterior := (half.prodCongr half).trans (copyExterior (Q := Q))
  ((chartHalves.prodCongr (Equiv.refl _)).trans (Equiv.prodAssoc ..)).trans
    ((Equiv.prodCongr (Equiv.refl _) ((exterior.prodCongr (Equiv.refl _)).trans finProdFinEquiv)).trans
      copyAddress.symm)
where
  copyExterior {Q : ℕ} [NeZero Q] :
      Swap.Shear.State (Fin 56) (ZMod Q) ≃ Fin (Q^112) :=
    (Equiv.sumArrowEquivProdArrow (Fin 56) (Fin 56) (ZMod Q)).symm.trans
      ((Equiv.arrowCongr finSumFinEquiv (Equiv.refl _)).trans FlatCoordinateLayout.rankEquiv)

/-- Changing only the local state on a charted tape preserves the complete
exterior record and trailing position, exactly as required by the COPY read. -/
theorem chartAddress_local {Q W : ℕ} [NeZero Q] (s : Swap.Shear.State Nine.Axis (ZMod Q))
    (j : Fin W) (f : Swap.Shear.State (Fin 8) (ZMod Q) → Swap.Shear.State (Fin 8) (ZMod Q)) :
    let x := chartAddress (s,j)
    copyAddress.symm (f (copyAddress x).1,(copyAddress x).2) =
      chartAddress (chartHalves.symm (f (chartHalves s).1,(chartHalves s).2),j) := by
  simp [chartAddress,-copyAddress_index]

private theorem chartHalves_exchange {R : Type*} [CommRing R]
    (U : Matrix (Fin 8) (Fin 8) R) (L : Matrix Nine.Exterior Nine.Exterior R)
    (s : Swap.Shear.State Nine.Axis R) :
    chartHalves (M8.Exchange.exchange (Matrix.fromBlocks U 0 0 L) s) =
      (M8.Exchange.exchange U (chartHalves s).1,M8.Exchange.exchange L (chartHalves s).2) := by
  apply Prod.ext <;> apply Prod.ext <;> funext i <;>
    simp [chartHalves,M8.Exchange.exchange,Matrix.sub_mulVec,Matrix.fromBlocks_mulVec,Function.comp_def]

/-- The exterior prefix is exchanged in both stage frames. Their relative
move therefore fixes every spectator, including at the two end stages. -/
theorem chartAddress_exchange {Q W : ℕ} [NeZero Q] (n : Fin 9)
    (U V : Matrix (Fin 8) (Fin 8) (ZMod Q)) (s : Swap.Shear.State Nine.Axis (ZMod Q)) (j : Fin W) :
    let L := Matrix.diagonal fun i : Nine.Exterior => if i.1.val < n.val then (1 : ZMod Q) else 0
    let frame := fun P => M8.Exchange.exchange (Matrix.fromBlocks P 0 0 L)
    let x := chartAddress (s,j)
    copyAddress.symm (M8.Exchange.exchange V (M8.Exchange.exchange U (copyAddress x).1),(copyAddress x).2) =
      chartAddress (frame V (frame U s),j) := by
  intro L frame x
  rw [chartAddress_local s j (fun a => M8.Exchange.exchange V (M8.Exchange.exchange U a))]
  apply congrArg (fun a => chartAddress (a,j))
  apply chartHalves.injective
  rw [Equiv.apply_symm_apply]
  simp only [frame,chartHalves_exchange]
  refine Prod.ext rfl ?_
  apply Prod.ext <;> funext i <;> by_cases h : i.1.val < n.val <;>
    simp [L,M8.Exchange.exchange,Matrix.sub_mulVec,Matrix.mulVec_diagonal,h]

open IntegerMultBounds.Networks.Shared50ModularControl (prime)
/-- Every checked modular move reads precisely the relative stage-frame
address on the charted parent tape, with one projector table for all stages. -/
theorem chartAddress_selected (w : ℕ) [NeZero (prime^w)] :
    ∃ P : Fin 636 → Matrix (Fin 8) (Fin 8) (ZMod (prime^w)),
      ∀ p (checked : Geometry.Moves.CheckedPair p) (n : Fin 9) {W : ℕ}
        (s : Swap.Shear.State Nine.Axis (ZMod (prime^w))) (j : Fin W),
      let L := Matrix.diagonal fun i : Nine.Exterior => if i.1.val < n.val then (1 : ZMod (prime^w)) else 0
      let frame := fun k => M8.Exchange.exchange (Matrix.fromBlocks (P k) 0 0 L)
      let x := chartAddress (s,j)
      copyAddress.symm (AffineFieldProgram.run (selectedWord w p) (copyAddress x).1,(copyAddress x).2) =
        chartAddress (frame ⟨p.2,checked.2.1⟩ (frame ⟨p.1,checked.1⟩ s),j) := by
  obtain ⟨_,_,widths⟩ := modular_move_profile.choose_spec
  obtain ⟨P,_,_,action,_⟩ := widths w
  refine ⟨P,?_⟩
  intro p checked n W s j L frame x
  change ∀ p (h : Geometry.Moves.CheckedPair p) a, AffineFieldProgram.run (selectedWord w p) a =
    M8.Exchange.exchange (P ⟨p.2,h.2.1⟩) (M8.Exchange.exchange (P ⟨p.1,h.1⟩) a) at action
  rw [action p checked]
  exact chartAddress_exchange n _ _ s j

open FlatCoordinateLayout (rank)
open RecursiveInterchangeLayout (Descriptor volume)

/-- The two seven-coordinate prefixes form the H and D fields of one child. -/
noncomputable def copyChild (w W : ℕ) : Descriptor := ⟨1,1,1,7*w,prime^w,prime^w*W⟩

theorem copyChild_volume (w W : ℕ) : volume prime (copyChild w W) = (prime^w)^16*W := by
  simp only [volume, copyChild, one_mul, ← pow_mul, Nat.mul_comm w 16]
  rw [show 16*w = 7*w+w+7*w+w by omega]
  simp only [pow_add]
  ring

/-- Of the parent's 128 radix coordinates, a COPY window addresses sixteen.
The other 112 coordinates and the nonactive fields index spectator positions. -/
theorem copyChild_measures (v : Descriptor) (w rows : ℕ)
    (width : v.width = 64*w) (splitRows : v.rows = 142080*rows) :
    let W := (prime^w)^112 * (v.beforeRows*rows*v.beforeH*v.between*v.afterD)
    (copyChild w W).width * 64 = 7*v.width ∧
    volume prime (copyChild w W) * 142080 = volume prime v := by
  intro W
  constructor
  · change 7*w*64 = _
    rw [width]
    ring
  · rw [copyChild_volume]
    simp only [volume,width,splitRows,show 64*w = w*64 by omega,pow_mul,W]
    have powers (x : ℕ) : x^16*x^112 = x^64*x^64 := by
      rw [← pow_add, ← pow_add]
    calc
      _ = ((prime^w)^16*(prime^w)^112)*(v.beforeRows*rows*v.beforeH*v.between*v.afterD)*142080 := by ac_rfl
      _ = _ := by rw [powers]; ac_rfl

/-- Install header words next to their caller while keeping arithmetic scratch
outside the caller/header pair. -/
def headerPlacement (t : ℕ) : Fin ((15+6)+t) ≃ Fin ((t+6)+15) where
  toFun := Fin.addCases
    (Fin.addCases (Fin.natAdd (t+6)) (fun i => Fin.castAdd 15 (Fin.natAdd t i)))
    (fun i => Fin.castAdd 15 (Fin.castAdd 6 i))
  invFun := Fin.addCases
    (Fin.addCases (Fin.natAdd (15+6)) (fun i => Fin.castAdd t (Fin.natAdd 15 i)))
    (fun i => Fin.castAdd t (Fin.castAdd 6 i))
  left_inv := by
    intro i
    induction i using Fin.addCases with
    | left i => induction i using Fin.addCases <;> simp
    | right i => simp
  right_inv := by
    intro i
    induction i using Fin.addCases with
    | left i => induction i using Fin.addCases <;> simp
    | right i => simp

private theorem headerPlacement_bank {t : ℕ} (v : Tapes t prime) (h : Tapes 6 prime) (u : Tapes 15 prime) :
    ((u.append h).append v).reindex (headerPlacement t) = (v.append h).append u := by
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases with
  | left i => induction i using Fin.addCases <;> simp [Tapes.append,headerPlacement]
  | right i => simp [Tapes.append,headerPlacement]

open FlatCoordinateSchedule (bits) in
noncomputable def copyHeaderInput (w W : ℕ) :=
  (FlatCoordinateDimensions.input w W).append (DimensionProductDescriptor.input (bits w) (bits 7))

open FlatCoordinateSchedule (bits) in
noncomputable def copyHeaderOutput (w W : ℕ) :=
  (FlatCoordinateDimensions.output (0 : Fin 2) w W).append (DimensionProductDescriptor.output (bits w) (bits 7) 7 w)

noncomputable def copyHeaderSetup (k : ℕ) :=
  let arithmetic := FamilyPlacementAlphabet.sequence (FlatCoordinateDimensions.program (0 : Fin 2))
    (DimensionProductDescriptor.program (q := prime))
  let slots : Fin 6 → Fin (9+6) := ![5,5,5,10,4,7]
  Placement.placed (seq (extend arithmetic 6) (FixedHeaderBankCopy.program (by decide) slots)) (headerPlacement k)

open FlatCoordinateSchedule (bits bits_value bits_canonical) in
/-- Construct the rank-seven child dimensions from the binary width and spectator
count, using a second width input and the fixed rank in the product bank. -/
theorem copyChild_headers {k : ℕ} (caller : Tapes k prime) (w W : ℕ) (hw : 0 < w) (hW : 0 < W) :
    let hs := fun i => bits (RecursiveDimensionBank.values (copyChild w W) i)
    HoareTime (copyHeaderSetup k)
      (fun z => z = (caller.append (FixedHeaderBankCopy.empty 6)).append (copyHeaderInput w W))
      (fun z => z = (caller.append (FixedHeaderBankCopy.headerBank hs)).append (copyHeaderOutput w W))
      (500*((prime^w)^16*W)) ∧ RecursiveDimensionBank.Headers (copyChild w W) hs := by
  intro hs
  let t := (0 : Fin 2)
  let slots : Fin 6 → Fin (9+6) := ![5,5,5,10,4,7]
  let output := copyHeaderOutput w W
  have valid : RecursiveDimensionBank.Headers (copyChild w W) hs :=
    ⟨fun i => bits_value _,fun i => bits_canonical _⟩
  refine ⟨?_,valid⟩
  have build := FamilyPlacementAlphabet.sequence_hoare (FlatCoordinateDimensions.construct_hoare t w W hW)
    (DimensionProductDescriptor.construct_hoare (q := prime) (bits w) (bits 7) 7 w hw
      (bits_value _) (bits_value _) (bits_canonical _) (bits_canonical _))
  have generated (i : Fin 6) : output.head (slots i) = 1 ∧
      output.tape (slots i) = RadixZeroFill.encodedBinary (hs i) := by
    obtain ⟨q,p,b⟩ := FlatCoordinateDimensions.output_descriptors t w W
    have one : FlatCoordinateLayout.prefixSize (Q := ActualAffineScaling.modulus w) t = 1 := pow_zero _
    have tail : FlatCoordinateLayout.suffixSize (Q := ActualAffineScaling.modulus w) (W := W) t = prime^w*W := by
      change (prime^w)^1*W = _
      rw [pow_one]
    rw [one] at p
    rw [tail] at b
    fin_cases i <;> constructor <;> first | rfl | exact p | exact q | exact b
  let V := (prime^w)^16*W
  have pos := ActualAffineScaling.modulus_pos w
  have hV : 0 < V := Nat.mul_pos (pow_pos pos _) hW
  have childPos : (copyChild w W).Positive :=
    ⟨Nat.zero_lt_one,Nat.zero_lt_one,Nat.zero_lt_one,pos,Nat.mul_pos pos hW⟩
  have bound (i) : RecursiveDimensionBank.values (copyChild w W) i ≤ V := by
    rw [show V = volume prime (copyChild w W) from (copyChild_volume w W).symm]
    exact RecursiveHeaderBounds.values_le_volume FlatCoordinateDimensions.hprime _ childPos i
  have install := FixedHeaderBankCopy.constructs_linear (by decide) slots hs output
    (fun i => (generated i).2) (fun i => (generated i).1) V hV valid.2
    (fun i => (valid.1 i).le.trans (bound i))
  have run := (hoare_extend_eq build (FixedHeaderBankCopy.empty 6)).seq install
  have placed := hoare_place run (headerPlacement k) caller
  rw [headerPlacement_bank,headerPlacement_bank] at placed
  apply placed.consequence (fun _ h => h) (fun _ h => h)
  change 357*((prime^w)^2*W)+(53*(7*w)+28)+1+1+60*V ≤ 500*V
  have small : (prime^w)^2*W ≤ V := Nat.mul_le_mul_right W (Nat.pow_le_pow_right pos (by decide : 2 ≤ 16))
  have width : 7*w ≤ V := bound 3
  omega


section
variable {w W : ℕ}
local instance : NeZero (prime^w) := ⟨pow_ne_zero _ Shared50ModularControl.prime_prime.ne_zero⟩

open M8.Machine.Segments in
/-- A basis-change segment starts and ends in the same binary payload encoding
as the COPY child. Its fixed program charges one linear pass constant. -/
theorem copySegment_runs (ops : List (AffineFieldProgram.Op (Fin 8) ℚ)) (good : Good ops)
    (hW : 0 < W) (x : Fin ((prime^w)^16*W) → ZMod 2) :
    let q := ops.map (AffineFieldProgram.mapOp (IntegerMultBounds.Swap.Modular.ratMod (prime^w)))
    (∀ op ∈ q, AffineFieldProgram.Legal op) →
    let stages := description ops good
    let bank := fun (y : Fin ((prime^w)^16*W) → ZMod 2) => SharedBankStageInput.raw
      (FlatCoordinateShiftSharedBank.common (d := 16) (b := w) (W := W)
        (fun i => SparseRoleCircuit.encode (y i))) (FlatCoordinateCleanSchedule.tapeCount stages)
    ∃ y, HoareTime (FlatCoordinateCleanSchedule.program stages) (fun z => z = bank x)
      (fun z => z = bank y) (FlatCoordinateCleanSchedule.constant stages * ((prime^w)^16*W)) ∧
      ∀ s j, y (FlatCoordinateLayout.index (AffineFieldCoordinates.embed (AffineFieldProgram.run q s)) j) =
        x (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j) := by
  intro q legal stages bank
  let perm := Equiv.ofBijective _ (AffineFieldBijective.run_bijective q legal)
  let addr := copyAddress (Q := prime^w) (W := W)
  let y := fun i => x (addr.symm (perm.symm (addr i).1,(addr i).2))
  have moves (s) (j : Fin W) : y (addr.symm (perm s,j)) = x (addr.symm (s,j)) := by
    simp only [y,Equiv.apply_symm_apply,Equiv.symm_apply_apply]
  let encoded := fun i => SparseRoleCircuit.encode (a := 0) (x i)
  have exactArray : FlatCoordinateInitializedSchedule.array stages w W hW encoded =
      fun i => SparseRoleCircuit.encode (y i) := by
    funext i
    obtain ⟨⟨s,j⟩,rfl⟩ := addr.symm.surjective i
    obtain ⟨s,rfl⟩ := perm.surjective s
    rw [moves]
    exact array_entry ops good w W hW encoded s j
  refine ⟨y, ?_, moves⟩
  apply (realizes ops good w W hW encoded).consequence (fun _ h => h) _ le_rfl
  intro z hz
  exact hz.1.trans (congrArg (fun a => SharedBankStageInput.raw
    (FlatCoordinateShiftSharedBank.common a) (FlatCoordinateCleanSchedule.tapeCount stages)) exactArray)

noncomputable def copyChildAddress (h d : Fin 7 → ZMod (prime^w))
    (u v : Fin 1 → ZMod (prime^w)) (j : Fin W) : RecursiveInterchangeScaling.Address (copyChild w W) :=
  let field (x : Fin 7 → ZMod (prime^w)) : Fin (prime^(7*w)) := Fin.cast (by rw [← pow_mul, Nat.mul_comm w 7])
    (rank x)
  let low (x : Fin 1 → ZMod (prime^w)) := Fin.cast (pow_one _) (rank x)
  ⟨(0 : Fin 1),(0 : Fin 1),(0 : Fin 1),field h,low u,field d,finProdFinEquiv (low v,j)⟩

theorem copyChild_index (h d : Fin 7 → ZMod (prime^w)) (u v : Fin 1 → ZMod (prime^w)) (j : Fin W) :
    Fin.cast (copyChild_volume w W) (RecursiveInterchangeScaling.index (copyChildAddress h d u v j)) =
      FlatCoordinateLayout.index (AffineFieldCoordinates.embed (Fin.addCases h u, Fin.addCases d v)) j := by
  apply Fin.ext
  rw [Fin.val_cast, RecursiveInterchangeScaling.index_val, FlatCoordinateLayout.index_val]
  simp only [copyChildAddress, copyChild, RecursiveInterchangeLayout.index, Fin.val_zero,
    zero_mul, zero_add, Fin.val_cast, finProdFinEquiv, Equiv.coe_fn_mk]
  have packed := ArbitraryWidthSliceTranspose.rank_append (Fin.addCases h u) (Fin.addCases d v)
  change (rank (AffineFieldCoordinates.embed (Fin.addCases h u,Fin.addCases d v))).val = _ at packed
  rw [packed, ArbitraryWidthSliceTranspose.rank_append h u, ArbitraryWidthSliceTranspose.rank_append d v]
  have pack (q H D U V t z : ℕ) :
      ((H*q^w+U)*q^(7*w)+D)*(q^w*t)+(z+t*V) =
      ((H*(q^w)^1+U)*(q^w)^(7+1)+(D*(q^w)^1+V))*t+z := by
    have power : (q^w)^(7+1) = q^(7*w)*q^w :=
      (pow_succ _ 7).trans (congrArg (· * q^w) ((pow_mul q w 7).symm.trans
        (congrArg (q^·) (Nat.mul_comm w 7))))
    rw [power,pow_one]
    ring
  exact pack _ _ _ _ _ _ _

/-- One transpose on the child sends both prefixes to the opposite halves and
preserves the low coordinates and trailing record in the original array. -/
theorem copyChild_transpose {α : Type*} (x : Fin ((prime^w)^16*W) → α)
    (h d : Fin 7 → ZMod (prime^w)) (u v : Fin 1 → ZMod (prime^w)) (j : Fin W) :
    Shared50RecursiveNodeRows.transpose (v := copyChild w W) (one_dvd _)
      (fun i => x (Fin.cast (copyChild_volume w W) i))
      (RecursiveInterchangeScaling.index (copyChildAddress d h u v j)) =
      x (FlatCoordinateLayout.index (AffineFieldCoordinates.embed (Fin.addCases h u, Fin.addCases d v)) j) := by
  rw [← copyChild_index]
  exact Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1) _ _ (copyChildAddress h d u v j)

private theorem copyInterval_run {R : Type*} [CommRing R]
    (h d : Fin 7 → R) (u v : Fin 1 → R) :
    IntegerMultBounds.Swap.Shear.run (intervalSwaps 0 7) (Fin.append h u, Fin.append d v) =
      (Fin.append d u, Fin.append h v) := by
  rw [intervalSwaps_run]
  apply Prod.ext <;> funext k <;> refine Fin.addCases (m := 7) (n := 1) (fun i => ?_) (fun i => ?_) k
  all_goals simp [M8.Exchange.exchange, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_diagonal,
    Fin.append, Fin.val_castAdd, Fin.val_natAdd, i.isLt]

/-- The one child transpose realizes the selected interval instruction at every
address of the original temporary, including its spectator record. -/
theorem copyChild_interval {α : Type*} (x : Fin ((prime^w)^16*W) → α)
    (s : IntegerMultBounds.Swap.Shear.State (Fin 8) (ZMod (prime^w))) (j : Fin W) :
    let atState := fun t => FlatCoordinateLayout.index (AffineFieldCoordinates.embed t) j
    Shared50RecursiveNodeRows.transpose (v := copyChild w W) (one_dvd _)
      (fun i => x (Fin.cast (copyChild_volume w W) i))
      (Fin.cast (copyChild_volume w W).symm
        (atState (IntegerMultBounds.Swap.Shear.run (intervalSwaps 0 7) s))) = x (atState s) := by
  intro atState
  obtain ⟨h,d⟩ := s
  obtain ⟨h,u,rfl⟩ : ∃ (a : Fin 7 → _) (b : Fin 1 → _), h = Fin.append a b :=
    ⟨_,_,(Fin.append_castAdd_natAdd (m := 7) (n := 1)).symm⟩
  obtain ⟨d,v,rfl⟩ : ∃ (a : Fin 7 → _) (b : Fin 1 → _), d = Fin.append a b :=
    ⟨_,_,(Fin.append_castAdd_natAdd (m := 7) (n := 1)).symm⟩
  rw [copyInterval_run]
  dsimp only [atState, Fin.append]
  rw [← copyChild_index d h u v j, Fin.cast_cast, Fin.cast_eq_self]
  exact copyChild_transpose x h d u v j

open M8.Machine.ArbitraryWidthOriginalRun (input program cost)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)

/-- Execute the middle of COPY on the designated caller tape, with the
descriptor headers at their binary words and the private bank clean. -/
theorem copyChild_runs [M8.Machine.Net] {t : ℕ} (caller : Tapes t prime)
    (headers : Fin 6 → Fin t) (source : Fin t) (hw : 0 < w) (hW : 0 < W)
    (hs : Fin 6 → List Bool) (valid : RecursiveDimensionBank.Headers (copyChild w W) hs)
    (tapes : ∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i))
    (heads : ∀ i, caller.head (headers i) = 1)
    (x : Fin ((prime^w)^16*W) → ZMod 2)
    (payload : caller.tape source = sourceWord (fun i => x (Fin.cast (copyChild_volume w W) i)))
    (origin : caller.head source = 0) :
    ∃ y : Fin (volume prime (copyChild w W)) → ZMod 2,
      HoareTime (program headers source) (fun z => z = input caller)
        (fun z => z = input (SharedPlacementAlphabet.setTape caller source (sourceWord y) 0))
        (cost (copyChild w W) hs) ∧
      ∀ s j, y (Fin.cast (copyChild_volume w W).symm (FlatCoordinateLayout.index
        (AffineFieldCoordinates.embed (IntegerMultBounds.Swap.Shear.run (intervalSwaps 0 7) s)) j)) =
        x (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j) := by
  have pos := pow_pos Shared50ModularControl.prime_prime.pos w
  have hp : (copyChild w W).Positive := ⟨Nat.zero_lt_one, Nat.zero_lt_one, Nat.zero_lt_one, pos, Nat.mul_pos pos hW⟩
  exact ⟨_, M8.Machine.ArbitraryWidthOriginalRun.runs caller headers source _ hs hp
    (Nat.mul_pos (by decide) hw) valid tapes heads _ payload origin, copyChild_interval x⟩

private theorem sourceWord_cast {v : Descriptor} {N : ℕ} (size : volume prime v = N)
    (x : Fin N → ZMod 2) :
    sourceWord (fun i => x (Fin.cast size i)) =
      putWord (fun _ => blank) 0 (List.ofFn fun i => SparseRoleCircuit.encode (a := prime) (x i)) := by
  subst N
  rw [M8.Machine.ArbitraryWidthHighExchangeJoinEncoding.sourceWord_eq]
  unfold RadixHighBlockJoinLoop.word
  congr 2

def segmentSource (stages : List (FlatCoordinateSchedule.Op 16)) :
    Fin (FlatCoordinateCleanSchedule.tapeCount stages) :=
  ⟨0, by
    have h := FlatCoordinateInitializedSchedule.skeleton_tapes_ge stages
    unfold FlatCoordinateCleanSchedule.tapeCount
    omega⟩

/-- Slot zero of a clean basis-change bank is exactly the child's payload
tape, including its head position and its blank exterior. -/
theorem copySegment_source (stages : List (FlatCoordinateSchedule.Op 16))
    (x : Fin ((prime^w)^16*W) → ZMod 2) :
    let n := FlatCoordinateCleanSchedule.tapeCount stages
    let bank := SharedBankStageInput.raw (FlatCoordinateShiftSharedBank.common
      (d := 16) (b := w) (W := W) (fun i => SparseRoleCircuit.encode (x i))) n
    let slot := segmentSource stages
    bank.head slot = 0 ∧ bank.tape slot = sourceWord (fun i => x (Fin.cast (copyChild_volume w W) i)) := by
  intro n bank slot
  refine ⟨rfl,?_⟩
  apply congrArg (fun xs => FlatRepeatedControlNormalize.encoded (radix := prime)
    (putWord (fun _ => blank) 0 xs))
  exact List.ofFn_congr (copyChild_volume w W).symm (fun i => SparseRoleCircuit.encode (a := 0) (x i))


private theorem segmentWorkspace_eq (stages : List (FlatCoordinateSchedule.Op 16))
    (x y : Fin ((prime^w)^16*W) → ZMod 2) :
    let bank := fun (z : Fin ((prime^w)^16*W) → ZMod 2) => SharedBankStageInput.raw
      (FlatCoordinateShiftSharedBank.common (d := 16) (b := w) (W := W)
        (fun i => SparseRoleCircuit.encode (z i))) (FlatCoordinateCleanSchedule.tapeCount stages)
    let spare := fun z => SharedPlacementAlphabet.setTape (bank z) (segmentSource stages) (fun _ => blank) 0
    spare x = spare y := by
  intro bank spare
  apply congrArg₂ Tapes.mk
  · rfl
  · funext k
    by_cases eq : k = segmentSource stages
    · simp [eq]
    · simp only [Function.update_of_ne eq, bank, SharedBankStageInput.raw]
      split
      next h =>
        have nz : k.val ≠ 0 := fun zero => eq (Fin.ext zero)
        have i : (⟨k.val,h⟩ : Fin 4) = 1 ∨ (⟨k.val,h⟩ : Fin 4) = 2 ∨ (⟨k.val,h⟩ : Fin 4) = 3 := by
          simp only [Fin.ext_iff]; omega
        rcases i with e | e | e <;> rw [e] <;> rfl
      next => rfl

open M8.Machine.Segments SharedPlacementAlphabet in
/-- Place the basis change on a caller's selected tape, leaving all other
caller tapes stationary and the segment's original source slot blank. -/
theorem copySegment_placed {t : ℕ} (src : Fin t) (ops : List (AffineFieldProgram.Op (Fin 8) ℚ))
    (good : Good ops) (hW : 0 < W) (caller : Tapes t prime) (x : Fin ((prime^w)^16*W) → ZMod 2)
    (head : caller.head src = 0)
    (payload : caller.tape src = sourceWord (fun i => x (Fin.cast (copyChild_volume w W) i))) :
    let q := ops.map (AffineFieldProgram.mapOp (IntegerMultBounds.Swap.Modular.ratMod (prime^w)))
    (∀ op ∈ q, AffineFieldProgram.Legal op) →
    let stages := description ops good
    let slot := segmentSource stages
    let bank := fun (y : Fin ((prime^w)^16*W) → ZMod 2) => SharedBankStageInput.raw
      (FlatCoordinateShiftSharedBank.common (d := 16) (b := w) (W := W)
        (fun i => SparseRoleCircuit.encode (y i))) (FlatCoordinateCleanSchedule.tapeCount stages)
    let workspace := fun y => setTape (bank y) slot (fun _ => blank) 0
    ∃ y : Fin ((prime^w)^16*W) → ZMod 2, HoareTime (Placement.placed (FlatCoordinateCleanSchedule.program stages) (sharedPlacement src slot))
      (fun z => z = caller.append (workspace x))
      (fun z => z = (setTape caller src
        (sourceWord (fun i => y (Fin.cast (copyChild_volume w W) i))) 0).append (workspace x))
      (FlatCoordinateCleanSchedule.constant stages * ((prime^w)^16*W)) ∧
      ∀ s j, y (FlatCoordinateLayout.index (AffineFieldCoordinates.embed (AffineFieldProgram.run q s)) j) =
        x (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j) := by
  intro q legal stages slot bank workspace
  obtain ⟨y,run,moves⟩ := copySegment_runs ops good hW x legal
  have hx := copySegment_source stages x
  have hy := copySegment_source stages y
  change (bank x).head slot = 0 ∧ (bank x).tape slot = _ at hx
  change (bank y).head slot = 0 ∧ (bank y).tape slot = _ at hy
  have placed := shared_hoare run caller src slot (fun _ => blank) 0 (payload.trans hx.2.symm) (head.trans hx.1.symm)
  refine ⟨y,?_,moves⟩
  have same : workspace x = workspace y := segmentWorkspace_eq stages x y
  rw [← hy.2, ← hy.1]
  apply placed.consequence (fun _ h => h) _ le_rfl
  intro z hz
  exact hz.trans (congrArg _ same.symm)

open M8.Machine.Segments SharedPlacementAlphabet M8.Machine.ArbitraryWidthOriginalRun in
/-- Run one basis pass followed by the grouped child on the same caller tape.
The six prepared header tapes are outside the payload slot. -/
theorem copyEnterChild_runs [M8.Machine.Net] {t : ℕ} (src : Fin t) (headers : Fin 6 → Fin t)
    (distinct : ∀ i, headers i ≠ src) (ops : List (AffineFieldProgram.Op (Fin 8) ℚ))
    (good : Good ops) (hw : 0 < w) (hW : 0 < W) (caller : Tapes t prime)
    (x : Fin ((prime^w)^16*W) → ZMod 2) (hs : Fin 6 → List Bool)
    (valid : RecursiveDimensionBank.Headers (copyChild w W) hs)
    (tapes : ∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i))
    (heads : ∀ i, caller.head (headers i) = 1) (head : caller.head src = 0)
    (payload : caller.tape src = sourceWord (fun i => x (Fin.cast (copyChild_volume w W) i))) :
    let q := ops.map (AffineFieldProgram.mapOp (IntegerMultBounds.Swap.Modular.ratMod (prime^w)))
    (∀ op ∈ q, AffineFieldProgram.Legal op) →
    let stages := description ops good
    let n := FlatCoordinateCleanSchedule.tapeCount stages
    let slot := segmentSource stages
    let work := setTape (SharedBankStageInput.raw (FlatCoordinateShiftSharedBank.common
      (d := 16) (b := w) (W := W) (fun i => SparseRoleCircuit.encode (x i))) n) slot (fun _ => blank) 0
    let basis := Placement.placed (FlatCoordinateCleanSchedule.program stages) (sharedPlacement src slot)
    let enter := extendBanks (extend (extend basis 16) 19)
    let child := program (fun i => Fin.castAdd n (headers i)) (Fin.castAdd n src)
    ∃ y : Fin (volume prime (copyChild w W)) → ZMod 2,
      HoareTime (seq enter child) (fun z => z = input (caller.append work))
        (fun z => z = input ((setTape caller src (sourceWord y) 0).append work))
        (FlatCoordinateCleanSchedule.constant stages * ((prime^w)^16*W) + 1 + cost (copyChild w W) hs) ∧
      ∀ s j, y (Fin.cast (copyChild_volume w W).symm (FlatCoordinateLayout.index
        (AffineFieldCoordinates.embed (IntegerMultBounds.Swap.Shear.run (intervalSwaps 0 7)
          (AffineFieldProgram.run q s))) j)) =
        x (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j) := by
  intro q legal stages n slot work basis enter child
  obtain ⟨loaded,pass,move⟩ := copySegment_placed src ops good hW caller x head payload legal
  let next := setTape caller src (sourceWord (fun i => loaded (Fin.cast (copyChild_volume w W) i))) 0
  have lifted := extend_banks_hoare (hoare_extend_eq (hoare_extend_eq pass (FixedHeaderBankCopy.empty 16))
    M8.Machine.ArbitraryWidthHighPrepareShared.privateInput)
  change HoareTime enter (fun z => z = input (caller.append work)) (fun z => z = input (next.append work)) _ at lifted
  obtain ⟨y,swap,action⟩ := copyChild_runs (next.append work) (fun i => Fin.castAdd n (headers i))
    (Fin.castAdd n src) hw hW hs valid (x := loaded)
    (by intro i; simpa [Tapes.append,next,setTape,distinct] using tapes i)
    (by intro i; simpa [Tapes.append,next,setTape,distinct] using heads i)
    (by simp [Tapes.append,next,setTape]) (by simp [Tapes.append,next,setTape])
  rw [setTape_append_left] at swap
  simp only [next,setTape_setTape] at swap
  exact ⟨y,lifted.seq swap,fun s j => (action _ j).trans (move s j)⟩

noncomputable def basisWorkspace (stages : List (FlatCoordinateSchedule.Op 16))
    (x : Fin ((prime^w)^16*W) → ZMod 2) :=
  SharedPlacementAlphabet.setTape (SharedBankStageInput.raw (FlatCoordinateShiftSharedBank.common
    (d := 16) (b := w) (W := W) (fun i => SparseRoleCircuit.encode (x i)))
    (FlatCoordinateCleanSchedule.tapeCount stages)) (segmentSource stages) (fun _ => blank) 0

open M8.Machine.Segments SharedPlacementAlphabet M8.Machine.ArbitraryWidthOriginalRun in
/-- Both fixed basis passes surround one child call on the same payload tape.
Only the designated tape changes in the prepared caller bank. -/
theorem copyMove_runs [M8.Machine.Net] {t : ℕ} (src : Fin t) (headers : Fin 6 → Fin t)
    (distinct : ∀ i, headers i ≠ src) (C : Matrix (Fin 8) (Fin 8) ℚ)
    (rev : CopyBasisPass C.adjugate)
    (fwd : CopyBasisPass C)
    (hw : 0 < w) (hW : 0 < W) (caller : Tapes t prime)
    (x : Fin ((prime^w)^16*W) → ZMod 2) (hs : Fin 6 → List Bool)
    (valid : RecursiveDimensionBank.Headers (copyChild w W) hs)
    (tapes : ∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i))
    (heads : ∀ i, caller.head (headers i) = 1) (head : caller.head src = 0)
    (payload : caller.tape src = sourceWord (fun i => x (Fin.cast (copyChild_volume w W) i))) :
    let spec := List.map (AffineFieldProgram.mapOp (IntegerMultBounds.Swap.Modular.ratMod (prime^w)))
    let A := description _ rev.good
    let B := description _ fwd.good
    let n := FlatCoordinateCleanSchedule.tapeCount A
    let m := FlatCoordinateCleanSchedule.tapeCount B
    let bank := fun v : Tapes t prime => input ((v.append (basisWorkspace B x)).append (basisWorkspace A x))
    let source := Fin.castAdd m src
    let enter := Placement.placed (FlatCoordinateCleanSchedule.program A) (sharedPlacement source (segmentSource A))
    let child := program (fun i => Fin.castAdd n (Fin.castAdd m (headers i))) (Fin.castAdd n source)
    let leave := Placement.placed (FlatCoordinateCleanSchedule.program B) (sharedPlacement src (segmentSource B))
    let machine := seq (seq (extendBanks (extend (extend enter 16) 19)) child)
      (extendBanks (extend (extend (extend leave n) 16) 19))
    ∃ y : Fin ((prime^w)^16*W) → ZMod 2,
      HoareTime machine (fun z => z = bank caller)
        (fun z => z = bank (setTape caller src (sourceWord (fun i => y (Fin.cast (copyChild_volume w W) i))) 0))
        ((FlatCoordinateCleanSchedule.constant A + FlatCoordinateCleanSchedule.constant B) *
          ((prime^w)^16*W) + cost (copyChild w W) hs + 2) ∧
      ∀ s j, y (FlatCoordinateLayout.index (AffineFieldCoordinates.embed
        (AffineFieldProgram.run (spec (rationalMoveWord 0 7 C)) s)) j) =
        x (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j) := by
  intro spec A B n m bank source enter child leave machine
  obtain ⟨mid,first,action⟩ := copyEnterChild_runs source (fun i => Fin.castAdd m (headers i))
    (fun i eq => distinct i (Fin.ext (congrArg (fun k : Fin (t+m) => k.val) eq))) _ rev.good hw hW (caller.append (basisWorkspace B x))
    x hs valid (by intro i; simpa [Tapes.append] using tapes i)
    (by intro i; simpa [Tapes.append] using heads i) (by simpa [source,Tapes.append] using head)
    (by simpa [source,Tapes.append] using payload) (rev.legal w)
  let next := setTape caller src (sourceWord mid) 0
  let bits := fun i => mid (Fin.cast (copyChild_volume w W).symm i)
  obtain ⟨y,last,move⟩ := copySegment_placed src _ fwd.good hW next bits
    (by simp [next,setTape]) (by simp [next,setTape,bits]) (fwd.legal w)
  have same : basisWorkspace B bits = basisWorkspace B x := segmentWorkspace_eq B bits x
  change HoareTime leave (fun z => z = next.append (basisWorkspace B bits))
    (fun z => z = (setTape next src _ 0).append (basisWorkspace B bits)) _ at last
  rw [same] at last
  simp only [next,setTape_setTape] at last
  have lifted := extend_banks_hoare (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq last
    (basisWorkspace A x)) (FixedHeaderBankCopy.empty 16)) M8.Machine.ArbitraryWidthHighPrepareShared.privateInput)
  change HoareTime _ (fun z => z = bank caller)
    (fun z => z = input ((setTape (caller.append (basisWorkspace B x)) (Fin.castAdd m src) (sourceWord mid) 0).append
      (basisWorkspace A x))) _ at first
  rw [setTape_append_left] at first
  refine ⟨y, ?_, ?_⟩
  · have bill (a b N c : ℕ) : (a+b)*N+c+2 = (a*N+1+c)+1+b*N := by ring
    rw [bill]
    exact first.seq lifted
  · intro s j
    rw [rationalMoveWord_run, move]
    exact action s j

/-- The child starts directly on the pointwise gate's temporary. Its source
word and head already have the required representation on the owner bank. -/
theorem copyChild_bank_runs [M8.Machine.Net] {t : ℕ} (tmp : Fin t) (hw : 0 < w) (hW : 0 < W)
    (bs : List Bool) (data : Fin t → Fin ((prime^w)^16*W) → ZMod 2)
    (hs : Fin 6 → List Bool) (valid : RecursiveDimensionBank.Headers (copyChild w W) hs) :
    let bank := fun X => PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0)
      (SparseRoleCircuit.encoded X) bs
    let headerBank : Tapes 6 prime := ⟨fun _ => 1, fun i => RadixZeroFill.encodedBinary (hs i)⟩
    let caller := (bank data).append headerBank
    let src := Fin.castAdd 6 (Fin.castAdd 2 tmp)
    ∃ y : Fin ((prime^w)^16*W) → ZMod 2,
      HoareTime (program (Fin.natAdd (t+2)) src) (fun z => z = input caller)
        (fun z => z = input ((bank (Function.update data tmp y)).append headerBank))
        (cost (copyChild w W) hs) ∧
      ∀ s j, y (FlatCoordinateLayout.index
        (AffineFieldCoordinates.embed (IntegerMultBounds.Swap.Shear.run (intervalSwaps 0 7) s)) j) =
        data tmp (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j) := by
  intro bank headerBank caller src
  obtain ⟨changed,run,action⟩ := copyChild_runs caller (Fin.natAdd (t+2)) src hw hW hs valid
    (x := data tmp) (by intro i; simp [caller,Tapes.append,headerBank])
    (by intro i; simp [caller,Tapes.append,headerBank]) (by
      rw [sourceWord_cast]
      simp [caller,src,bank,PointwiseRoleGate.bank,Tapes.append]
      rfl) (by simp [caller,src,bank,PointwiseRoleGate.bank,Tapes.append])
  let y := fun i => changed (Fin.cast (copyChild_volume w W).symm i)
  refine ⟨y, ?_, action⟩
  have wordEq : sourceWord changed = putWord (fun _ => blank) 0
      (List.ofFn fun i => SparseRoleCircuit.encode (a := prime) (y i)) := by
    simpa only [y,Fin.cast_cast,Fin.cast_eq_self] using sourceWord_cast (copyChild_volume w W) y
  have updated : SharedPlacementAlphabet.setTape caller src (sourceWord changed) 0 =
      (bank (Function.update data tmp y)).append headerBank := by
    simp only [caller,src,bank,PointwiseRoleGate.bank,SharedPlacementAlphabet.setTape_append_left]
    congr 2
    apply congrArg₂ Tapes.mk <;> funext k <;> by_cases eq : k = tmp
    all_goals simp [eq,wordEq]
    all_goals congr 2; funext i; simp [SparseRoleCircuit.encoded,eq]
  rwa [updated] at run

end

/-- The physical COPY bank contains the caller, six descriptor headers,
both basis workspaces and the private tapes of the chosen child machine. -/
noncomputable def copyPrepared [M8.Machine.Net] {t w W : ℕ} (A B : List (FlatCoordinateSchedule.Op 16))
    (v : Tapes t prime) (hdr : Tapes 6 prime) (arithmetic : Tapes 15 prime) :=
  let x : Fin ((prime^w)^16*W) → ZMod 2 := 0
  M8.Machine.ArbitraryWidthOriginalRun.input ((((v.append hdr).append arithmetic).append (basisWorkspace B x)).append (basisWorkspace A x))

/-- Local work in the physical COPY window, including the join after setup. -/
def copyWindowWork (basis targets N digits : ℕ) :=
  (500+basis)*N + (targets+2)*(14*N+14*digits+34)+4

/-- A canonical payload counter makes the local charge linear with a constant
depending only on the two fixed basis passes and the scheduled fanout. -/
theorem copyWindowWork_linear (basis targets : ℕ) {N : ℕ} (positive : 0 < N)
    (bs : List Bool) (count : Counter.value bs = N) (canonical : GrowingCounterData.Canonical bs) :
    copyWindowWork basis targets N bs.length ≤ (504+basis+76*(targets+2))*N := by
  have digits := GrowingCounterData.canonical_width bs canonical
  rw [count] at digits
  have logBound := Nat.log2_le_self N
  have scan : 14*N+14*bs.length+34 ≤ 76*N := by omega
  have fanout := Nat.mul_le_mul_left (targets+2) scan
  unfold copyWindowWork
  nlinarith only [fanout,positive]

open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord) in
open M8.Machine.Segments M8.Machine.ArbitraryWidthOriginalRun SharedPlacementAlphabet in
/-- Copy the retained owner into the temporary, convert its frame, fan out,
then clear it. Header construction, both basis passes and the child transpose are charged. -/
theorem copyWindow_hoare [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5) (life : Copy.Lifecycle)
    (scheduled : life ∈ Copy.lifecycles) :
    let src := ownerTape n r d ⟨life.source,(Copy.source_bounds life scheduled).2⟩
    let tmp := Fin.last 142080
    let regs := life.targets.attach.map fun j => (⟨j.val,((Copy.target_bounds life scheduled _ j.property).2.trans (by decide : 222 < 661))⟩ : Fin 661)
    let targets := regs.map (ownerTape n r d)
    ∃ (C : Matrix (Fin 8) (Fin 8) ℚ) (rev : CopyBasisPass C.adjugate) (fwd : CopyBasisPass C),
      let A := description _ rev.good
      let B := description _ fwd.good
      ∃ (states : ℕ) (machine : Program _ states prime),
      ∀ (w : ℕ), 0 < w →
      let word := selectedWord w
      let S := Swap.Shear.State (Fin 8) (ZMod (Shared50ModularControl.prime^w))
      let frame := selectedFrame w
      LocalMoveProfile word ∧ AffineFieldProgram.interchanges (word (life.sourceFrame,0)) = 7 ∧
      let prepare := fun W => copyPrepared (t := 142081+2) (w := w) (W := W) A B
      ∀ {W : ℕ} (_hW : 0 < W),
      let N := (Shared50ModularControl.prime^w)^16 * W
      let _ : NeZero (Shared50ModularControl.prime^w) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos w)⟩
      let addr : Fin N ≃ S × Fin W := copyAddress
      ∀ (data : Fin 142081 → Fin N → ZMod 2)
      (bs : List Bool), Counter.value bs = N →
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild w W) i)
      let frameOf := fun j => tapeFrame addr (frame j)
      let common := fun i => data src (addr.symm
        (AffineFieldProgram.run (word (life.sourceFrame,0)) (addr i).1,(addr i).2))
      let bank := fun X => PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0) (SparseRoleCircuit.encoded X) bs
      let output := Function.update (fun j i => if j ∈ targets then data j i + common i else data j i) tmp 0
      let stored := Copy.extendStored (fun j => data (ownerTape n r d j))
      HoareTime machine (fun z => z = prepare W (bank data) (FixedHeaderBankCopy.empty 6) (copyHeaderInput w W)) (fun z => z = prepare W (bank output) (FixedHeaderBankCopy.headerBank hs) (copyHeaderOutput w W))
        (copyWindowWork (FlatCoordinateCleanSchedule.constant A + FlatCoordinateCleanSchedule.constant B)
          life.targets.length N bs.length + cost (copyChild w W) hs) ∧
      (∀ j : Fin 661, output (ownerTape n r d j) = Copy.execute frameOf life stored j) ∧
      output tmp = Copy.execute frameOf life stored 661 := by
  intro src tmp regs targets
  obtain ⟨C,shape,rev,fwd⟩ := modular_move_profile.choose_spec.1 _ (copySource_mem life scheduled)
  let gate : PointwiseRoleGate.Gate 142081 := ⟨src,tmp,Fin.castSucc_ne_last _⟩
  let copy := fun (s _ : Fin (prime+4)) => s
  let erase := fun (_ _ : Fin (prime+4)) => SparseRoleCircuit.encode (a := prime) 0
  obtain ⟨_,adds,addRun⟩ := copyAdds_hoare (a := prime) n r d life scheduled
  refine ⟨C,rev,fwd,?_⟩
  intro A B
  let site := Fin.castAdd 15 (Fin.castAdd 6 (Fin.castAdd 2 tmp))
  let nA := FlatCoordinateCleanSchedule.tapeCount A
  let nB := FlatCoordinateCleanSchedule.tapeCount B
  let liftCore {q} (g : Program ((142081+2+6)+15) q prime) :=
    extendBanks (extend (extend (extend (extend g nB) nA) 16) 19)
  let liftGate {q} (g : Program (142081+2) q prime) :=
    liftCore (extend (extend g 6) 15)
  let pre := Placement.placed (FlatCoordinateCleanSchedule.program A) (sharedPlacement (Fin.castAdd nB site) (segmentSource A))
  let child := program (fun i : Fin 6 => Fin.castAdd nA (Fin.castAdd nB (Fin.castAdd 15 (Fin.natAdd (142081+2) i))))
    (Fin.castAdd nA (Fin.castAdd nB site))
  let post := Placement.placed (FlatCoordinateCleanSchedule.program B) (sharedPlacement site (segmentSource B))
  let convert := seq (seq (extendBanks (extend (extend pre 16) 19)) child)
    (extendBanks (extend (extend (extend post nA) 16) 19))
  refine ⟨_,seq (liftCore (copyHeaderSetup _)) (seq (seq (seq (liftGate (PointwiseRoleGate.program gate copy)) convert) (liftGate adds))
    (liftGate (PointwiseRoleGate.program gate erase))), ?_⟩
  intro w hw word S frame
  obtain ⟨profile,windows⟩ := copyAddress_word w
  obtain ⟨seven,invol,read⟩ := windows life scheduled
  refine ⟨profile,seven,?_⟩
  intro prepare W hW N inst addr data bs count hs frameOf common bank output stored
  obtain ⟨setup,valid⟩ := copyChild_headers (bank data) w W hw hW
  let background := fun (_ : Fin 142081) (_ : ℤ) => (blank : Fin (prime+4))
  let origins := fun (_ : Fin 142081) => (0 : ℤ)
  let headers : Tapes 6 prime := ⟨fun _ => 1, fun i => RadixZeroFill.encodedBinary (hs i)⟩
  let copied := Function.update data tmp (data src)
  let caller := ((bank copied).append headers).append (copyHeaderOutput w W)
  have distinct (i : Fin 6) : Fin.castAdd 15 (Fin.natAdd (142081+2) i) ≠ site := by
    intro eq
    have h := congrArg Fin.val eq
    simp only [site,Fin.val_natAdd,Fin.val_castAdd] at h
    omega
  obtain ⟨moved,converted,forward⟩ := copyMove_runs site _ distinct C rev fwd hw hW caller (data src) hs valid
    (by intro i; simp [caller,Tapes.append,headers])
    (by intro i; simp [caller,Tapes.append,headers])
    (by simp [caller,bank,site,Tapes.append,PointwiseRoleGate.bank])
    (by rw [sourceWord_cast]; simp [caller,bank,site,Tapes.append,PointwiseRoleGate.bank,copied]; congr 2)
  have specialized : word (life.sourceFrame,0) = _ :=
    congrArg (List.map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (prime^w)))) shape
  rw [← specialized] at forward
  have agree : moved = common := by
    funext i
    obtain ⟨⟨s,j⟩,rfl⟩ := addr.symm.surjective i
    have h := forward (AffineFieldProgram.run (word (life.sourceFrame,0)) s) j
    rw [invol] at h
    simp only [common, Equiv.apply_symm_apply]
    exact h
  have updated : setTape caller site (sourceWord (fun i => moved (Fin.cast (copyChild_volume w W) i))) 0 =
      ((bank (Function.update data tmp moved)).append headers).append (copyHeaderOutput w W) := by
    rw [sourceWord_cast]
    simp only [caller,site,bank,PointwiseRoleGate.bank,setTape_append_left]
    congr 3
    apply congrArg₂ Tapes.mk <;> funext k <;> by_cases eq : k = tmp
    all_goals simp [eq]
    all_goals congr 2 <;> funext i <;> simp [SparseRoleCircuit.encoded,copied,eq]
  rw [updated, agree] at converted
  have clean (stages) : basisWorkspace stages (data src) = basisWorkspace stages (0 : Fin N → ZMod 2) :=
    segmentWorkspace_eq stages _ _
  simp only [clean] at converted
  have liftRun {q b} {g : Program (142081+2) q prime} {v v' : Tapes (142081+2) prime}
      (h : HoareTime g (fun z => z = v) (fun z => z = v') b) :
      HoareTime (liftGate g) (fun z => z = prepare W v headers (copyHeaderOutput w W)) (fun z => z = prepare W v' headers (copyHeaderOutput w W)) b :=
    extend_banks_hoare (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq
      (hoare_extend_eq (hoare_extend_eq h headers) (copyHeaderOutput w W)) (basisWorkspace B (0 : Fin N → ZMod 2))) (basisWorkspace A (0 : Fin N → ZMod 2)))
      (FixedHeaderBankCopy.empty 16)) M8.Machine.ArbitraryWidthHighPrepareShared.privateInput)
  have decoded : common = frameOf 0 ((frameOf life.sourceFrame).symm (data src)) := funext (read addr (data src))
  let loaded := Function.update data tmp common
  let added := fun j i => if j ∈ targets then loaded j i + loaded tmp i else loaded j i
  have add := addRun loaded background origins bs count
  change HoareTime adds (fun w => w = bank loaded) (fun w => w = bank added) _ at add
  have write (X : Fin 142081 → Fin N → ZMod 2) (op : Fin (prime+4) → Fin (prime+4) → Fin (prime+4))
      (value : Fin N → ZMod 2) (action : ∀ i, op (SparseRoleCircuit.encode (X src i))
        (SparseRoleCircuit.encode (X tmp i)) = SparseRoleCircuit.encode (value i)) :
      HoareTime (PointwiseRoleGate.program gate op) (fun w => w = bank X)
        (fun w => w = bank (Function.update X tmp value)) (14*N+14*bs.length+33) := by
    have step := PointwiseRoleGate.gate_hoare gate op background origins (SparseRoleCircuit.encoded X) bs count
    have same : PointwiseRoleGate.applyGate gate op (SparseRoleCircuit.encoded X) =
        SparseRoleCircuit.encoded (Function.update X tmp value) := by
      funext j i
      by_cases eq : j = tmp
      · subst j
        simpa [PointwiseRoleGate.applyGate,gate,SparseRoleCircuit.encoded] using action i
      · simp [PointwiseRoleGate.applyGate,gate,SparseRoleCircuit.encoded,eq]
    rw [same] at step
    exact step
  have done := (((liftRun (write data copy (data src) (fun _ => rfl))).seq converted).seq
    (liftRun add)).seq (liftRun (write added erase 0 (fun _ => rfl)))
  have cleaned : Function.update added tmp 0 =
      Function.update (fun j i => if j ∈ targets then data j i + common i else data j i) tmp 0 := by
    funext j i
    by_cases eq : j = tmp <;> simp [eq,added,loaded]
  rw [cleaned] at done
  have setupRun := extend_banks_hoare (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq setup
    (basisWorkspace B (0 : Fin N → ZMod 2))) (basisWorkspace A (0 : Fin N → ZMod 2)))
    (FixedHeaderBankCopy.empty 16)) M8.Machine.ArbitraryWidthHighPrepareShared.privateInput)
  have complete := setupRun.seq done
  refine ⟨?_,?_,?_⟩
  · convert complete using 1
    all_goals first | rfl | (dsimp only [N,copyWindowWork]; ring)
  · intro j
    have off : ownerTape n r d j ≠ tmp := Fin.castSucc_ne_last _
    have member : ownerTape n r d j ∈ targets ↔ j.val ∈ life.targets := by
      change ownerTape n r d j ∈ regs.map (ownerTape n r d) ↔ _
      rw [List.mem_map_of_injective (ownerTape_injective n r d)]
      constructor
      · intro mem
        obtain ⟨k,_,eq⟩ := List.mem_map.mp mem
        exact (congrArg Fin.val eq) ▸ k.property
      · intro mem
        exact List.mem_map.mpr ⟨⟨j.val,mem⟩,List.mem_attach ..,Fin.ext rfl⟩
    have wf := Copy.wellformed life scheduled
    have retained : stored life.source = data src := by
      simp [stored,Copy.extendStored,(Copy.source_bounds life scheduled).2,src]
    have old : stored j.val = data (ownerTape n r d j) := by simp [stored,Copy.extendStored,j.isLt]
    have distinct : j.val ≠ 661 := Nat.ne_of_lt j.isLt
    simp only [output,Function.update_of_ne off,Copy.execute,Function.update_of_ne distinct,
      Copy.addTargets_eq _ wf.1 wf.2.1,Function.update_self,old,retained,member,decoded]
    funext i
    split <;> rfl
  · simp [output,Copy.execute]

end IntegerMultBounds.MathlibTM2.M6.BitNode
