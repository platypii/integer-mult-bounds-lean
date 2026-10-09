import IntegerMultBounds.Machine.ActiveRepairRecordFormatPlaced
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsDecodeEarly
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsDecodeLate
import IntegerMultBounds.Machine.CountedTapeRepairCleanupWord

namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyCommon
noncomputable section

 theorem left_frame {n s q a k : ℕ} {M : Program n s a} {x y : Tapes n a}
    (h : HoareTime M (fun v => v=x) (fun v => v=y) k) (v : Tapes q a) :
    HoareTime (Placement.placed M (finAddFlip : Fin (n+q) ≃ Fin (q+n)))
      (fun w => w=v.append x) (fun w => w=v.append y) k := by
  have he (z : Tapes n a) : Placement.combine finAddFlip z v=v.append z := by
    apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases <;> simp [Tapes.append,finAddFlip]
  have hh := Placement.hoare_at h finAddFlip (Placement.combine finAddFlip x v) (Placement.active_combine _ _ _)
  apply hh.consequence (fun w hw => hw.trans (he x).symm) _ le_rfl
  rintro w ⟨z,hz,rfl⟩
  subst z
  simpa only [Placement.replace,Placement.extra_combine] using he y

 theorem format_word (chunks : List (List Bool)) :
    ActiveRepairRecordFormatPlaced.encoded (a:=1) chunks=
      RepairScan.srcTape (ActiveRepairRecordFormatWords.records chunks) := by
  unfold ActiveRepairRecordFormatPlaced.encoded RepairScan.srcTape
  rw [DropFlag.encode_partition]
  rfl

 theorem records_payloads_plain {X : Type*} {M : ℕ} (e : X ≃ Fin M) (data : X → List Bool) :
    ActiveRepairRecordFormatWords.records ((Compact.plain e data).map Partition.Record.payload)=Compact.plain e data := by
  unfold Compact.plain ActiveRepairRecordFormatWords.records
  simp only [List.map_map]
  rfl

 theorem encoded_nonblank (chunks : List (List Bool)) :
    ∀ x∈DropFlag.encode (ActiveRepairRecordFormatWords.records chunks),x≠blank := by
  have h := ActiveRepairRecordFlattenEndpoint.encoded_nonblank (ActiveRepairRecordFormatWords.records chunks)
  have he : ActiveRepairRecordFlatten.encode (ActiveRepairRecordFormatWords.records chunks)=
      DropFlag.encode (ActiveRepairRecordFormatWords.records chunks) := by
    rw [ActiveRepairRecordFlatten.encode_partition,DropFlag.encode_partition]
  rwa [he] at h

 def cleanupProgram := seq (ScanEnd.program (a:=1)) (EraseBack.program (a:=1))
 theorem cleanup (chunks : List (List Bool)) :
    HoareTime cleanupProgram
      (fun v => v=CountedTapeRepairCleanupWord.one (RepairScan.srcTape (ActiveRepairRecordFormatWords.records chunks)) 0)
      (fun v => v=CountedTapeRepairCleanupWord.one (fun _ => blank) 0)
      (2*(DropFlag.encode (ActiveRepairRecordFormatWords.records chunks)).length+3) := by
  let xs := DropFlag.encode (ActiveRepairRecordFormatWords.records chunks)
  have hn := encoded_nonblank chunks
  have hscan := ScanEnd.scan_hoare (a:=1) (fun _ => blank) 0 xs hn rfl
  have he := EraseBack.erase_hoare (a:=1) (fun _ => blank) 0 xs hn rfl (by intro _ _; rfl)
  dsimp only [xs] at hscan he
  exact (hscan.seq he).consequence (fun _ h => h) (fun _ h => h) (by omega)

 def rawBank (chunks : List (List Bool)) : Tapes 1 1 :=
  ⟨fun _ => 0,fun _ => putWord (fun _ => blank) 0 (chunks.flatten.map bitSymbol)⟩

 theorem formatter_sources (chunks : List (List Bool)) (bs ns : List Bool) :
    ActiveRepairRecordFormatPlaced.sources (a:=1) chunks bs ns=
      ⟨![0,0,1,1],![putWord (fun _ => blank) 0 (chunks.flatten.map bitSymbol),fun _ => blank,
        CountedLoopReuseAlphabet.binary bs,CountedLoopReuseAlphabet.binary ns]⟩ := by
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i
    · change RowPaddingConstructedAlphabet.mapTape
        (putWord (fun _ => blank) 0 (ActiveRepairRecordFormatWords.raw chunks))=_
      rw [RowPaddingConstructedAlphabet.map_putWord]
      simp only [ActiveRepairRecordFormatWords.raw,List.map_map]
      rfl
    · rfl
    · exact CountedLoopReuseAlphabet.encoding_binary bs
    · change (fun j => (CountedLoopReuseAlphabet.encoding 1).encode
        (CountedLoopReuseAlphabet.binary (a:=0) ns j))=CountedLoopReuseAlphabet.binary ns
      have hbits (f : ℤ → Fin 4) (p : ℤ) (xs : List Bool) :
          CountedLoopAlphabet.putBits f p xs=putBits f p xs := by
        induction xs generalizing f p with
        | nil => rfl
        | cons x xs ih => simp only [CountedLoopAlphabet.putBits,putBits,ih]
      have hb : CountedLoopReuseAlphabet.binary (a:=0) ns=CountedCopyReuse.binary ns := by
        unfold CountedLoopReuseAlphabet.binary CountedCopyReuse.binary
        rw [hbits]
        rfl
      rw [hb]
      exact CountedLoopReuseAlphabet.encoding_binary ns

 def atProgram {t q : ℕ} (M : Program 1 q 1) (i : Fin t) := Placement.placed M (FiniteReturnStackAt.placement i)
 theorem at_runs {t q B : ℕ} (M : Program 1 q 1) (v : Tapes t 1) (i : Fin t)
    (f g : ℤ → Fin 5) (p r : ℤ) (ht : v.tape i=f) (hp : v.head i=p)
    (h0 : HoareTime M (fun w => w=CountedTapeRepairCleanupWord.one f p)
      (fun w => w=CountedTapeRepairCleanupWord.one g r) B) :
    HoareTime (atProgram M i) (fun w => w=v) (fun w => w=SharedPlacementAlphabet.setTape v i g r) B := by
  have h := Placement.hoare_at h0 (FiniteReturnStackAt.placement i) v (by
    rw [FiniteReturnStackAt.active_bank,ht,hp]; rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank _ _) = _
  rw [FiniteReturnStackAt.replace_bank]

 theorem flatten_cost_le (rs : List Partition.Record) (R : ℕ)
    (hw : ∀ r∈rs,r.payload.length≤R) :
    ActiveRepairRecordFlattenOriginal.cost rs≤5*rs.length*(R+1)+12 := by
  obtain ⟨he,hr⟩ := ActiveRepairRecordFlattenEndpoint.length_bounds rs R hw
  unfold ActiveRepairRecordFlattenOriginal.cost ActiveRepairRecordFlattenEndpoint.cost
  nlinarith

 theorem format_cost_le (chunks : List (List Bool)) (bs ns : List Bool) (R : ℕ)
    (hw : ∀ xs∈chunks,xs.length=R) (hbits : bs.length≤R+1) :
    ActiveRepairRecordFormatEndpoint.cost chunks bs ns R≤35*chunks.length*(R+1)+7*ns.length+40 := by
  obtain ⟨hr,he⟩ := ActiveRepairRecordFormatEndpoint.lengths chunks R hw
  unfold ActiveRepairRecordFormatEndpoint.cost
  rw [hr,he]
  nlinarith

 theorem source_length (chunks : List (List Bool)) (R : ℕ) (hw : ∀ xs∈chunks,xs.length=R) :
    (DropFlag.encode (ActiveRepairRecordFormatWords.records chunks)).length=chunks.length*(R+2) := by
  rw [DropFlag.encode_partition,List.length_map]
  exact (ActiveRepairRecordFormatEndpoint.lengths chunks R hw).2

 theorem decode_cost_absorb (C N R P Q : ℕ) (hp : 1≤R)
    (hP : P≤C*(N*R)) (hQ : Q≤5*N*(R+1)+12) :
    P+1+Q≤(C+10)*(N*R)+13 := by
  nlinarith [Nat.mul_le_mul_left N hp]

 theorem assembly_cost_absorb (C N R F Q L H : ℕ) (hp : 1≤R)
    (hF : F≤35*N*(R+1)+7*H+40) (hQ : Q≤(C+10)*(N*R)+13) (hL : L=N*(R+2)) :
    F+1+Q+1+(2*L+3)≤(C+86)*(N*R)+7*H+58 := by
  rw [hL]
  nlinarith [Nat.mul_le_mul_left N hp]

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyCommon
