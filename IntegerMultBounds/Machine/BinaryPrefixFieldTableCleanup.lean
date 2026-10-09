import IntegerMultBounds.Machine.BinaryPrefixFieldTableGather

/-! Erase the generated full-address table, marked dummy stream and every
copied or derived descriptor; only originals and the field table remain. -/
namespace IntegerMultBounds.Machine.BinaryPrefixFieldTableCleanup
noncomputable section
open SharedPlacementAlphabet (setTape)
open CompactGadgetReservationHeadersCore (bank)
open BinaryPrefixFieldTableData (dummy word)
open RecursiveChildQuotientsConstant (bits)
variable {t : ℕ}

def eraseAt (i : Fin t) := Placement.placed (EraseBack.program (a := 0)) (FiniteReturnStackAt.placement i)
def returnAt (i : Fin t) := Placement.placed (ReturnOrigin.program (a := 0)) (FiniteReturnStackAt.placement i)

theorem erases (v : Tapes t 0) (i : Fin t) (xs : List (Fin 4))
    (hx : ∀ x∈xs, x≠blank) (ht : v.tape i=putWord (fun _ => blank) 0 xs) (hh : v.head i=xs.length) :
    HoareTime (eraseAt i) (fun z => z=v)
      (fun z => z=setTape v i (fun _ => blank) 0) (xs.length+2) := by
  have h := Placement.hoare_at (EraseBack.erase_hoare (fun _ => (blank : Fin 4)) 0 xs hx rfl (by intros; rfl))
    (FiniteReturnStackAt.placement i) v (by
      rw [FiniteReturnStackAt.active_bank,ht,hh]; simp only [zero_add]; rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  exact FiniteReturnStackAt.replace_bank _ _ _ _

theorem returns (v : Tapes t 0) (i : Fin t) (xs : List Bool)
    (ht : v.tape i=putWord (fun _ => blank) 0 (xs.map bitSymbol)) (hh : v.head i=xs.length) :
    HoareTime (returnAt i) (fun z => z=v)
      (fun z => z=setTape v i (putWord (fun _ => blank) 0 (xs.map bitSymbol)) 0) (xs.length+2) := by
  have hr := ReturnOrigin.return_hoare (a := 0) (xs.map bitSymbol) (ReturnOrigin.bits_nonblank xs)
  simp only [List.length_map] at hr
  have h := Placement.hoare_at hr (FiniteReturnStackAt.placement i) v (by
    rw [FiniteReturnStackAt.active_bank,ht,hh]; rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  exact FiniteReturnStackAt.replace_bank _ _ _ _

theorem binary_full (xs : List Bool) :
    CountedCopyReuse.binary xs=putWord (fun _ => blank) 0 (separator::xs.map (bitSymbol (a := 0))) := by
  rw [CountedCopyReuse.binary,BinaryAddressTableStep.bits_word,putWord_cons]
  congr 1
  funext z
  simp [CountedCopyReuse.empty,Function.update_apply]

def noTable (hs : Fin 3 → List Bool) (W start d : ℕ) (h : start+d≤W) :=
  setTape (BinaryPrefixFieldTableGather.output hs W start d h) 5 (fun _ => blank) 0
def noDummy (hs : Fin 3 → List Bool) (W start d : ℕ) (h : start+d≤W) :=
  setTape (noTable hs W start d h) 6 (fun _ => blank) 0
def noCount (hs : Fin 3 → List Bool) (W start d : ℕ) (h : start+d≤W) :=
  setTape (noDummy hs W start d h) 3 (fun _ => blank) 0
def noZero (hs : Fin 3 → List Bool) (W start d : ℕ) (h : start+d≤W) :=
  setTape (noCount hs W start d h) 4 (fun _ => blank) 0
def noCopy (hs : Fin 3 → List Bool) (W start d : ℕ) (h : start+d≤W) :=
  setTape (noZero hs W start d h) 8 (fun _ => blank) 0
def output (hs : Fin 3 → List Bool) (W start d : ℕ) (h : start+d≤W) :=
  setTape (BinaryPrefixFieldTableSetup.base hs) 7 (putWord (fun _ => blank) 0 ((word W start d h).map bitSymbol)) 0

def core := seq (seq (seq (seq (seq (eraseAt (5 : Fin 9)) (eraseAt 6))
  (BinaryDescriptorCleanupList.oneProgram 3)) (BinaryDescriptorCleanupList.oneProgram 4))
  (BinaryDescriptorCleanupList.oneProgram 8)) (returnAt 7)
def program := extend core 15

def cost (hs : Fin 3 → List Bool) (W d : ℕ) :=
  (2^W*W+2)+1+(2^W+3)+1+(2*(bits (2^W)).length+4)+1+4+1+(2*(hs 2).length+4)+1+(2^W*d+2)

theorem core_runs (hs : Fin 3 → List Bool) (W start d : ℕ) (h : start+d≤W) :
    HoareTime core (fun v => v=BinaryPrefixFieldTableGather.output hs W start d h)
      (fun v => v=output hs W start d h) (cost hs W d) := by
  have h0 := erases (BinaryPrefixFieldTableGather.output hs W start d h) 5
    ((BinaryAddressTableData.table W (2^W)).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl
    (by simp [BinaryPrefixFieldTableGather.output,setTape])
  have h1 := erases (noTable hs W start d h) 6
    (separator::(dummy W).map bitSymbol)
    (by intro x hx; rcases List.mem_cons.mp hx with rfl | hx
        · decide
        · exact ReturnOrigin.bits_nonblank _ x hx)
    (by change CountedCopyReuse.binary (dummy W)=_; exact binary_full _)
    (by simp [noTable,BinaryPrefixFieldTableGather.output,setTape,dummy]; omega)
  have h2 := BinaryDescriptorCleanupList.one_hoare (3 : Fin 9) (noDummy hs W start d h) (bits (2^W))
    (by rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]; rfl) rfl
  have h3 := BinaryDescriptorCleanupList.one_hoare (4 : Fin 9) (noCount hs W start d h) []
    (by rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]; rfl) rfl
  have h4 := BinaryDescriptorCleanupList.one_hoare (8 : Fin 9) (noZero hs W start d h) (hs 2)
    (by rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]; rfl) rfl
  have h5 := returns (noCopy hs W start d h) 7 (word W start d h) rfl
    (by simp [noCopy,noZero,noCount,noDummy,noTable,BinaryPrefixFieldTableGather.output,setTape])
  have he : setTape (noCopy hs W start d h) 7
      (putWord (fun _ => blank) 0 ((word W start d h).map bitSymbol)) 0 = output hs W start d h := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h5
  have hall := ((((h0.seq h1).seq h2).seq h3).seq h4).seq h5
  simpa only [core,cost,List.length_map,BinaryAddressTableData.table_length,List.length_cons,
    dummy,List.length_replicate,List.length_nil,BinaryPrefixFieldTableData.word_length] using hall

theorem cleans (hs : Fin 3 → List Bool) (W start d : ℕ) (h : start+d≤W) :
    HoareTime program (fun v => v=bank (BinaryPrefixFieldTableGather.output hs W start d h))
      (fun v => v=bank (output hs W start d h)) (cost hs W d) :=
  hoare_extend_eq (core_runs hs W start d h) (SharedBank.empty 15 0)

end
end IntegerMultBounds.Machine.BinaryPrefixFieldTableCleanup
