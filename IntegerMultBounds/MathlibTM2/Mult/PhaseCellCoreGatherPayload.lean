module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedCoreGather
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaGatherData

/-! The generated ordered core sweep emits the packed supplier ABI directly.
All windows in a movement class are exposed together; numerical endpoint keys
remain distinct. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix

/-- Replica-major exposure for a whole movement class. A later rectangular
transpose can place replicas of each distinct numerical key together. -/
def coreGatherPayload {s : ℕ} (width radius L : ℕ)
    (Fs : List (ZMod s → GaussianInt)) : List GaussianInt :=
  Fs.flatMap (fun F => (coreGatherIndices s width radius L).flatMap
    (fun k => packedInterval (coreStart width k-radius) L F))

/-- The physical sweep's symbol windows are exactly packed ambient intervals. -/
theorem coreGatherPayload_symbols {A s : ℕ} (width radius L w : ℕ)
    (F : ZMod s → GaussianInt) :
    (coreGatherOrigins s width radius L w).flatMap
      (fun a => ((cstream A w (chirpLine s F)).drop a).take (L*w)) =
        cstream A w (coreGatherPayload width radius L [F]) := by
  rw [coreGather_packed]
  simp only [coreGatherPayload,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    cstream,List.flatMap_assoc]

@[simp] theorem coreGatherPayload_length {s : ℕ} (width radius L : ℕ)
    (Fs : List (ZMod s → GaussianInt)) :
    (coreGatherPayload width radius L Fs).length =
      Fs.length*(coreGatherIndices s width radius L).length*L := by
  have hrow (F : ZMod s → GaussianInt) :
      ((coreGatherIndices s width radius L).flatMap
        (fun k => packedInterval (coreStart width k-radius) L F)).length =
          (coreGatherIndices s width radius L).length*L := by
    rw [List.length_flatMap]
    have he : ((coreGatherIndices s width radius L).map
        (fun k => (packedInterval (coreStart width k-radius) L F).length)) =
          List.replicate (coreGatherIndices s width radius L).length L := by
      apply List.map_eq_replicate_iff.mpr
      intro k hk
      obtain ⟨hleft,hright,hlen⟩ := coreGatherIndices_spec s width radius L k hk
      apply packedInterval_length F
      omega
    rw [he,List.sum_replicate,smul_eq_mul]
  simp only [coreGatherPayload,List.length_flatMap,hrow,List.map_const',List.sum_replicate,smul_eq_mul]
  exact (Nat.mul_assoc ..).symm

/-- Each core's payload occupies one contiguous slot in the class archive. -/
theorem coreGatherPayload_slot {s : ℕ} (width radius L : ℕ)
    (F : ZMod s → GaussianInt) (i : Fin (coreGatherIndices s width radius L).length) :
    ((coreGatherPayload width radius L [F]).drop (i.val*L)).take L =
      packedInterval (coreStart width (coreGatherIndices s width radius L)[i.val]-radius) L F := by
  let rows := (coreGatherIndices s width radius L).map
    (fun k => packedInterval (coreStart width k-radius) L F)
  have hlen : ∀ row ∈ rows, row.length = L := by
    intro row hr
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hr
    obtain ⟨hleft,hright,hlen⟩ := coreGatherIndices_spec s width radius L k hk
    apply packedInterval_length F
    omega
  have hi : i.val < rows.length := by simpa only [rows,List.length_map] using i.isLt
  have h := flatten_uniform_window rows L 0 L i.val hlen hi (by omega)
  rw [List.getD_eq_getElem _ _ hi] at h
  simp only [Nat.add_zero,List.drop_zero] at h
  have ht : (rows[i.val]).take L = rows[i.val] :=
    List.take_of_length_le (by rw [hlen _ (List.getElem_mem hi)])
  rw [ht] at h
  simpa [coreGatherPayload,rows,List.flatMap_def] using h

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 168 Q A U}

/-- Actual generated controls and a restoring source sweep produce the packed
payload for every core in the class. No origin tape or control queue is assumed. -/
theorem initializedCoreGather_payload_exec {V s width radius L w : ℕ}
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V) (hLfit : L < 2^V)
    (hwV : w < 2^V) (hvol : s*w < 2^V) (hA : 4 ≤ A) (hVpos : 0 < V)
    (hgroup : 0 < (coreGatherIndices s width radius L).length)
    (C : ZMod s → GaussianInt) (v : HS 168 Q A U) (S : Stacks 168 A)
    (h163 : (S.R 163).length = V) (h115 : S.R 115 = []) (h103 : S.R 103 = []) (h105 : S.R 105 = [])
    (hs : S.R 145 = binSyms V s) (hw : S.R 150 = binSyms V width)
    (hr : S.R 152 = binSyms V radius) (hL : S.R 165 = binSyms V L) (hz : S.R 154 = [])
    (hblank : ∀ k : Fin 168, k.val < 31 → S.R k = [])
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = [])
    (hsource : S.R 110 = cstream A w (chirpLine s C))
    (hword : (S.R 94).length = w) (hcontrol : S.R 91 = [])
    (hclean : ∀ k ∈ [(92 : Fin 168),93,95,96,97,98,99,100,101,102], S.R k = [])
    (hfresh : ∀ k ∈ [(88 : Fin 168),89,90], S.R k = []) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ initializedCoreGatherCost V s width radius L w ∧
      Exec body initializedCoreGather (Host.mk v S) n (Host.mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      F.R 108 = cstream A w (coreGatherPayload width radius L [C]) ++ S.R 108 ∧
      F.R 91 = coreGatherControls A s width radius L w ∧
      F.R 109 = (coreGatherIndices s width radius L).flatMap
        (fun k => binSyms V (coreStart width k-radius)) ++ S.R 109 ∧
      F.R 116 = List.replicate (coreGatherIndices s width radius L).length tick ∧
      ∀ k, k ≠ 108 → k ≠ 91 → k ≠ 109 → k ≠ 116 → F.R k = S.R k := by
  obtain ⟨v',F,n,hu,hn,he,hi,ho,hl,hpayload,hc,horigins,hcount,hframe⟩ :=
    initializedCoreGather_exec (body := body) hwidth hwide hLfit hwV hvol hA hVpos hgroup v S
      h163 h115 h103 h105 hs hw hr hL hz hblank h104 h106 h116
      (cstream A w (chirpLine s C)) (by simp) hsource hword hcontrol hclean hfresh
  rw [coreGatherPayload_symbols] at hpayload
  exact ⟨v',F,n,hu,hn,he,hi,ho,hl,hpayload,hc,horigins,hcount,hframe⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
