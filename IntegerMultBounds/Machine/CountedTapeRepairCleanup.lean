import IntegerMultBounds.Machine.CountedTapeRepairCleanupAt

/-! Complete physical cleanup of fourteen scan/stage tapes, retaining source
and repaired output at their origins and restoring all stage work to blank. -/
namespace IntegerMultBounds.Machine.CountedTapeRepairCleanup
noncomputable section
open SharedPlacementAlphabet
open CountedTapeRepairCleanupWord
open CountedTapeRepairCleanupAt

def output (v : Tapes 42 1) (xs10 xs11 : List (Fin 5)) :=
  setTape (setTape (setTape (setTape (setTape (setTape (setTape (setTape (setTape (setTape (setTape (setTape (setTape (setTape (v) 0 (fun _ => blank) 0) 1 (fun _ => blank) 0) 2 (fun _ => blank) 0) 3 (fun _ => blank) 0) 4 (fun _ => blank) 0) 5 (fun _ => blank) 0) 6 (fun _ => blank) 0) 7 (fun _ => blank) 0) 8 (fun _ => blank) 0) 9 (fun _ => blank) 0) 10 (putWord (fun _ => blank) 0 xs10) 0) 11 (putWord (fun _ => blank) 0 xs11) 0) 12 (fun _ => blank) 0) 13 (fun _ => blank) 0

def program := seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (markedEndAt 0) (markedScanAt 1)) (markedEndAt 2)) (markedEndAt 3)) (markedEndAt 4)) (markedEndAt 5)) (markedEndAt 6)) (markedScanAt 7)) (plainEndAt 8)) (plainEndAt 9)) (plainBackAt 10)) (plainBackAt 11)) (markedEndAt 12)) (counterAt 13)

theorem runs (v : Tapes 42 1) (xs0 xs1 xs7 xs8 xs9 xs10 xs11 : List (Fin 5)) (cs13 : List Bool)
    (h0t : v.tape 0=marked xs0) (h0p : v.head 0=xs0.length)
    (h1t : v.tape 1=marked xs1) (h1p : v.head 1=0)
    (h2t : v.tape 2=marked []) (h2p : v.head 2=0)
    (h3t : v.tape 3=marked []) (h3p : v.head 3=0)
    (h4t : v.tape 4=marked []) (h4p : v.head 4=0)
    (h5t : v.tape 5=marked []) (h5p : v.head 5=0)
    (h6t : v.tape 6=marked []) (h6p : v.head 6=0)
    (h7t : v.tape 7=marked xs7) (h7p : v.head 7=0)
    (h8t : v.tape 8=putWord (fun _ => blank) 0 xs8) (h8p : v.head 8=xs8.length)
    (h9t : v.tape 9=putWord (fun _ => blank) 0 xs9) (h9p : v.head 9=xs9.length)
    (h10t : v.tape 10=putWord (fun _ => blank) 0 xs10) (h10p : v.head 10=xs10.length)
    (h11t : v.tape 11=putWord (fun _ => blank) 0 xs11) (h11p : v.head 11=xs11.length)
    (h12t : v.tape 12=marked []) (h12p : v.head 12=0)
    (h13t : v.tape 13=RepairScan.ctrTape cs13) (h13p : v.head 13=1)
    (hx0 : ∀ x ∈ xs0,x≠blank)
    (hx1 : ∀ x ∈ xs1,x≠blank)
    (hx7 : ∀ x ∈ xs7,x≠blank)
    (hx8 : ∀ x ∈ xs8,x≠blank)
    (hx9 : ∀ x ∈ xs9,x≠blank)
    (hx10 : ∀ x ∈ xs10,x≠blank)
    (hx11 : ∀ x ∈ xs11,x≠blank)
    : HoareTime program (fun w => w=v) (fun w => w=output v xs10 xs11)
      (xs0.length+2*xs1.length+2*xs7.length+xs8.length+xs9.length+xs10.length+xs11.length+2*cs13.length+72) := by
  let A1 := setTape v 0 (fun _ => blank) 0
  have h1 := clears_marked_end v 0 xs0 h0t h0p hx0
  let A2 := setTape A1 1 (fun _ => blank) 0
  have h2 := clears_marked_scan A1 1 xs1 (by simpa [A1,setTape] using h1t) (by simpa [A1,setTape] using h1p) hx1
  let A3 := setTape A2 2 (fun _ => blank) 0
  have h3 := clears_marked_end A2 2 [] (by simpa [A2,A1,setTape] using h2t) (by simpa [A2,A1,setTape] using h2p) (by simp)
  let A4 := setTape A3 3 (fun _ => blank) 0
  have h4 := clears_marked_end A3 3 [] (by simpa [A3,A2,A1,setTape] using h3t) (by simpa [A3,A2,A1,setTape] using h3p) (by simp)
  let A5 := setTape A4 4 (fun _ => blank) 0
  have h5 := clears_marked_end A4 4 [] (by simpa [A4,A3,A2,A1,setTape] using h4t) (by simpa [A4,A3,A2,A1,setTape] using h4p) (by simp)
  let A6 := setTape A5 5 (fun _ => blank) 0
  have h6 := clears_marked_end A5 5 [] (by simpa [A5,A4,A3,A2,A1,setTape] using h5t) (by simpa [A5,A4,A3,A2,A1,setTape] using h5p) (by simp)
  let A7 := setTape A6 6 (fun _ => blank) 0
  have h7 := clears_marked_end A6 6 [] (by simpa [A6,A5,A4,A3,A2,A1,setTape] using h6t) (by simpa [A6,A5,A4,A3,A2,A1,setTape] using h6p) (by simp)
  let A8 := setTape A7 7 (fun _ => blank) 0
  have h8 := clears_marked_scan A7 7 xs7 (by simpa [A7,A6,A5,A4,A3,A2,A1,setTape] using h7t) (by simpa [A7,A6,A5,A4,A3,A2,A1,setTape] using h7p) hx7
  let A9 := setTape A8 8 (fun _ => blank) 0
  have h9 := clears_plain_end A8 8 xs8 (by simpa [A8,A7,A6,A5,A4,A3,A2,A1,setTape] using h8t) (by simpa [A8,A7,A6,A5,A4,A3,A2,A1,setTape] using h8p) hx8
  let A10 := setTape A9 9 (fun _ => blank) 0
  have h10 := clears_plain_end A9 9 xs9 (by simpa [A9,A8,A7,A6,A5,A4,A3,A2,A1,setTape] using h9t) (by simpa [A9,A8,A7,A6,A5,A4,A3,A2,A1,setTape] using h9p) hx9
  let A11 := setTape A10 10 (putWord (fun _ => blank) 0 xs10) 0
  have h11 := returns_plain A10 10 xs10 (by simpa [A10,A9,A8,A7,A6,A5,A4,A3,A2,A1,setTape] using h10t) (by simpa [A10,A9,A8,A7,A6,A5,A4,A3,A2,A1,setTape] using h10p) hx10
  let A12 := setTape A11 11 (putWord (fun _ => blank) 0 xs11) 0
  have h12 := returns_plain A11 11 xs11 (by simpa [A11,A10,A9,A8,A7,A6,A5,A4,A3,A2,A1,setTape] using h11t) (by simpa [A11,A10,A9,A8,A7,A6,A5,A4,A3,A2,A1,setTape] using h11p) hx11
  let A13 := setTape A12 12 (fun _ => blank) 0
  have h13 := clears_marked_end A12 12 [] (by simpa [A12,A11,A10,A9,A8,A7,A6,A5,A4,A3,A2,A1,setTape] using h12t) (by simpa [A12,A11,A10,A9,A8,A7,A6,A5,A4,A3,A2,A1,setTape] using h12p) (by simp)
  let A14 := setTape A13 13 (fun _ => blank) 0
  have h14 := clears_counter A13 13 cs13 (by simpa [A13,A12,A11,A10,A9,A8,A7,A6,A5,A4,A3,A2,A1,setTape] using h13t) (by simpa [A13,A12,A11,A10,A9,A8,A7,A6,A5,A4,A3,A2,A1,setTape] using h13p)
  exact (((((((((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8).seq h9).seq h10).seq h11).seq h12).seq h13).seq h14).consequence (fun _ h => h) (fun _ h => h) (by simp only [List.length_nil]; omega)

end
end IntegerMultBounds.Machine.CountedTapeRepairCleanup
