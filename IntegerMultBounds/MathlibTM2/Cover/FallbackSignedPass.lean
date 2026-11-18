module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackControlledPass
public import IntegerMultBounds.MathlibTM2.Cover.FallbackSignedHandoff

/-! Sign the unsigned records and apply their residual matrices on one shared host. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable [M8.Machine.Net] {T K Q d r w W : ℕ} {P U : Type}
local notation "N" => rowSwapBlock.tapes+35

open Record RecursiveInterchangeLayout
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

theorem signedResidualPass (regs : Fin 6 ↪ Fin T) (anchor : Fin (size d+T) ↪ Fin K)
    (ports : Fin (N+2) ↪ Fin K) (ext : Fin 6 ↪ Fin K) (off : ∀ i k, ports i ≠ ext k)
    (banks : ∀ i k, anchor i ≠ ports k) (external : ∀ i k, k ≠ 2 → anchor i ≠ ext k)
    (shared : anchor (port d regs 1) = ext 2)
    (capacity : (anchorProgram d true).1+(anchorProgram d false).1+1 ≤ Q)
    (table : Matrix (Fin r) (Fin r) (ZMod prime) → Matrix (Fin (d+1)) (Fin (d+1)) (ZMod prime))
    (body : P → Pr P K Q prime U) (rs : List (Pair (size d+T))) (hk : rs.length = r*r)
    (parents saved : Fin (size d+T)) (layout : (parents :: saved :: (slots rs ++ [port d regs 4])).Nodup)
    (cap : columnCapacity ≤ Q) (cs : List (Pair K)) (sizeC : cs.length = r*r) (parentsC savedC : Fin K)
    (maskRegs : (parentsC :: savedC :: (slots cs ++ [ext 0])).Nodup)
    (pivotRegs : (parentsC :: savedC :: (slots cs ++ [ports (Fin.last N).castSucc])).Nodup)
    (separate : ∀ k ∈ parentsC :: savedC :: slots cs, ∀ i, anchor i ≠ k) :
    ∃ prog, ∀ (v : Descriptor) (B : ℕ) (a : ScanData r d w W) (inputs : ℕ → Record.Array d 1 (w+1) W)
      (u : HS K Q prime U) (S : Stacks K prime), v.beforeH = B*prime^(r*((w+1)*r)) →
      a.records = LabelMask.records v → 0 < W →
      let D := embStk anchor S
      Ready d 1 (w+1) W D → ready (prime^w) D.R rs → D.R saved = [] →
      (D.R parents).length = v.beforeRows*v.rows*B →
      (D.R (port d regs 0)).length = ActualAffineScaling.modulus (w+1)^((d+1)*1)*W →
      a.signed = (List.range a.records).map inputs →
      (∀ i ∈ ([2,3,4,5] : List (Fin 6)), D.R (port d regs i) = []) →
      ScanReady a ports ext 0 (preparedPivots a (ports (Fin.last N).castSucc) S) →
      a.table = table → M < 2^a.H → W < 2^a.J → a.outputTail = [] → S.R (ext 0) = [] →
      ready (prime^w) S.R cs → S.R savedC = [] → (S.R parentsC).length = v.beforeRows*v.rows*B →
      (∀ j < a.records, Record.scalarArray (inputs j) = SparseRoleCircuit.encode ∘ a.input j) →
      (∀ j < a.records, LabelStock.live r (w+1) 1 j = true →
      ((a.matrix j).det = 1 ∨ (a.matrix j).det = -1) ∧
      (LabelRing.res prime (w+1) (by omega)).mapMatrix (a.matrix j) = table (LabelStock.residue r (w+1) 1 j)) →
      (∀ j < a.records, LabelStock.live r (w+1) 1 j = false →
      ∃ symbol, Record.scalarArray (inputs j) = fun _ => symbol) →
      let ins := signedInputs table (w+1) a.records inputs
    let output := (List.range a.records).flatMap (outputRecord (LabelStock.live r (w+1) 1) a.matrix a.input)
    ∃ z F n, z.user = u.user ∧ F.R (ext 2) = output ++ a.inputTail ∧ F.R (ext 5) = [] ∧
      F.R (ext 0) = [] ∧ F.R (ports (Fin.last N).castSucc) = a.pivotTail ∧
      F.R (ports (archivePorts 0 (columnBank 34))) = a.matrixTail ∧
      n ≤ (1+((v.beforeRows*v.rows*B)*(time (prime^w) (r*r) 1+5)+4 +
          ((ins.map (fun x => cost d T 1 (w+1) W x.1 + 2)).sum + 2) +
          (2*(a.records*(ActualAffineScaling.modulus (w+1)^((d+1)*1)*W))+2))) + (2*((v.beforeRows*v.rows*B)*(time (prime^w) (r*r) 1+5)+4) + (1+(((List.range a.records).map fun j => a.recordTime U j + 4).sum + 2 + (2*(a.records*(M^(d+1)*W))+2)))) ∧
      Exec body prog (mk u S) n (mk z F) := by
  obtain ⟨sign,signRun⟩ := anchorHandoff (w := w) (W := W) regs anchor ports ext off banks external shared
    capacity table body rs hk parents saved layout
  obtain ⟨pass,passRun⟩ := controlledPass_exec (w := w) (W := W) body cap ports ext off table cs sizeC
    parentsC savedC maskRegs pivotRegs
  refine ⟨.seq sign pass,?_⟩
  intro v B a inputs u S shape records hW D neutral radix free count width unsigned clean start tables hm hw
    fresh empty radixC freeC countC encoded liveSpec padding ins output
  obtain ⟨outs,y,F,t,correct,hy,exec,prepared,frame,ht⟩ :=
    signRun v B a inputs u S shape records hW neutral radix free count width unsigned clean start
  have keep (k) (h : k ∈ parentsC :: savedC :: slots cs) := frame k (separate k h)
  have counters : ready (prime^w) F.R cs := by
    intro pair h
    have member (k) (hk : k ∈ slots cs) : F.R k = S.R k := keep k (by simp [hk])
    rw [member _ (List.mem_flatMap.mpr ⟨pair,h,by simp⟩),member _ (List.mem_flatMap.mpr ⟨pair,h,by simp⟩)]
    exact radixC pair h
  obtain ⟨z,G,n,hz,queue,acc,mask,pivots,archive,hn,run⟩ :=
    passRun v B {a with signed := outs} records tables shape inputs encoded correct liveSpec padding hm hw hW y F
      counters ((keep _ (by simp)).trans freeC) ((congrArg List.length (keep _ (by simp))).trans countC)
      ((frame _ (fun i => external i 0 (by decide))).trans empty) fresh prepared
  exact ⟨z,G,t+n,hz.trans hy,queue,acc,mask,pivots,archive,Nat.add_le_add ht hn,.seq exec run⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
