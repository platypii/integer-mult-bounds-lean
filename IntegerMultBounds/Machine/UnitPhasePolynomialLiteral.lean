import IntegerMultBounds.Machine.UnitPhasePolynomialStream

/-! Discharge every source context and row/coefficient adjacency premise
from one literal flattened row-major polynomial array. Each address owns R
consecutive coefficients; the final nonexistent coefficient is never read. -/
namespace IntegerMultBounds.Machine.UnitPhasePolynomialLiteral
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open ButterflyStreamData (Coefficient full)
variable {s : Shape} {N R : ℕ}

def contexts (f : ℤ → Fin 6) (p : ℤ) (xs : Fin (N*R) → Coefficient) (i j : ℕ) :=
  UnitPhaseStreamData.contexts f p xs (i*R+j)
def tail (f g : ℤ → Fin 6) (p r : ℤ) (xs : Fin (N*R) → Coefficient) : Tapes 4 2 :=
  ⟨![p,0,r,0],![full f p xs,(fun _ => blank),g,(fun _ => blank)]⟩

theorem index_lt (i j : ℕ) (hi : i<N) (hj : j<R) : i*R+j<N*R := by
  have hm := Nat.mul_le_mul_right R (show i+1≤N by omega)
  nlinarith

theorem widths (f : ℤ → Fin 6) (p : ℤ) (xs : Fin (N*R) → Coefficient) (w : ℕ)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w) :
    ∀ i<N,∀ j<R,(contexts f p xs i j).re.length=w ∧ (contexts f p xs i j).im.length=w := by
  intro i hi j hj
  exact UnitPhaseStreamData.widths f p xs w hw (i*R+j) (index_lt i j hi hj)

theorem adjacent (f : ℤ → Fin 6) (p : ℤ) (xs : Fin (N*R) → Coefficient) :
    ∀ i<N,∀ j,j+1<R → (contexts f p xs i (j+1)).tape=(contexts f p xs i j).tape ∧
      (contexts f p xs i (j+1)).start=(contexts f p xs i j).start+
        (contexts f p xs i j).re.length+(contexts f p xs i j).im.length+2 := by
  intro i hi j hj
  have h := UnitPhaseStreamData.adjacent f p xs (i*R+j)
    (by simpa only [Nat.add_assoc] using index_lt i (j+1) hi hj)
  simpa only [contexts,Nat.add_assoc] using h

theorem boundary (f : ℤ → Fin 6) (p : ℤ) (xs : Fin (N*R) → Coefficient) (hR : 0<R) :
    ∀ i,i+1<N → (contexts f p xs (i+1) 0).tape=(contexts f p xs i (R-1)).tape ∧
      (contexts f p xs (i+1) 0).start=(contexts f p xs i (R-1)).start+
        (contexts f p xs i (R-1)).re.length+(contexts f p xs i (R-1)).im.length+2 := by
  intro i hi
  have he : i*R+(R-1)+1=(i+1)*R := by nlinarith [Nat.sub_add_cancel (show 1≤R by omega)]
  have h := UnitPhaseStreamData.adjacent f p xs (i*R+(R-1))
    (by rw [he]; simpa only [Nat.add_zero] using index_lt (i+1) 0 hi hR)
  simpa only [contexts,Nat.add_zero,he] using h

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (hr : 0<rows) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (hm : 0<m) (hslots : m≤v.slots) (hl : m=ws.length)
    (hspan : SparsePhaseHeadersData.offset v axis m+(m-1)*(v.f*s.chunk)<s.bits)
    (f g : ℤ → Fin 6) (p r : ℤ) (ell w : ℕ)
    (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w) :
    HoareTime (UnitPhasePolynomialStream.program m ws)
      (fun t => t=UnitPhasePolynomialStreamInit.input order v rows axis (tail f g p r xs) ell)
      (fun t => t=UnitPhasePolynomialStream.output order v rows axis m ws (contexts f p xs) (tail f g p r xs) ell)
      (FixedBasePowerDescriptor.constant 2*2^ell+UnitPhaseFullStreamInit.cost order v rows axis+1+
        CountedLoopHeaderClean.cost (rows*2^s.bits) (RecursiveChildQuotientsConstant.bits (rows*2^s.bits))
          (UnitPhasePolynomialStreamLoop.bodyCost v axis m (2^ell) w)+1+
        (5*s.bits+11+BinaryDescriptorCleanupList.cost UnitPhasePolynomialStreamClean.slots
          (UnitPhasePolynomialStreamClean.words (rows*2^s.bits) (2^ell))+1)+1) := by
  apply UnitPhasePolynomialStream.runs order v rows axis m ws hm hslots hl hspan
    (contexts f p xs) (tail f g p r xs) ell w (widths f p xs w hw) _ ⟨rfl,rfl⟩ ⟨rfl,rfl⟩
    (adjacent f p xs) (boundary f p xs (by positivity))
  have hn : 0<(rows*2^s.bits)*2^ell := by positivity
  rw [contexts,show 0*2^ell+0=0 by omega,UnitPhaseStreamData.tape _ _ _ _ hn,
    UnitPhaseStreamData.start _ _ _ _ hn]
  exact ⟨rfl,by simp [tail,ButterflyStreamData.position,CyclicRowCycle.rowPrefix]⟩

end
end IntegerMultBounds.Machine.UnitPhasePolynomialLiteral
