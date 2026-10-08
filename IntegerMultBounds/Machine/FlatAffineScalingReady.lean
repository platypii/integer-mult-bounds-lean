import IntegerMultBounds.Machine.FlatAffineScalingBootstrap
import IntegerMultBounds.Machine.FlatAffineScalingNormalize

/-! Actual affine scaling from blank generated storage through complete payload
normalization. Canonical B/Q/P words are marker-free inputs; marker creation,
metadata synthesis, all data motion, erasure and head restoration are charged. -/
namespace IntegerMultBounds.Machine.FlatAffineScalingReady
open Networks
open ActualAffineScaling (modulus)
open FlatAffineScalingBootstrap (setup scratch)
noncomputable section
variable {P B b : ℕ}

def program {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) :=
  seq (FlatAffineScalingBootstrap.markerProgram hr) (FlatAffineScalingNormalize.program hr)

abbrev input := @FlatAffineScalingBootstrap.input

def output {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (bs qs ns : List Bool) (source dest : ℤ → Fin 4) :=
  FlatAffineScalingNormalize.output hr a ns (setup r.num.natAbs bs qs) (setup r.den bs qs) scratch
    source 0 (fun _ => blank) 0 (fun _ => blank) 0 dest 0

theorem output_payload {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (bs qs ns : List Bool) (source dest : ℤ → Fin 4) :
    let v := output hr a bs qs ns source dest
    v.tape (FlatAffineScaling.sourceSlot r) =
      putWord (putWord source 0 (List.ofFn a)) 0 (FlatAffineScalingNormalize.word hr a) ∧
    v.tape (ActualAffineScalingStream.destinationSlot r) = dest ∧
    v.head (FlatAffineScaling.sourceSlot r) = 0 ∧ v.head (ActualAffineScalingStream.destinationSlot r) = 0 :=
  FlatAffineScalingNormalize.output_payload hr a ns (setup r.num.natAbs bs qs) (setup r.den bs qs) scratch
    source 0 (fun _ => blank) 0 (fun _ => blank) 0 dest 0

theorem output_symbol {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (bs qs ns : List Bool) (source dest : ℤ → Fin 4)
    (i : Fin P) (y : Fin (modulus b)) (j : Fin B) :
    (output hr a bs qs ns source dest).tape (FlatAffineScaling.sourceSlot r)
      (((i.val*(modulus b*B)+(Swap.Modular.ratMod (modulus b) r*(y.val : ZMod (modulus b))).val*B+j.val : ℕ) : ℤ)) =
      a (FiberLayoutData.index i y j) := by
  simpa only [output,zero_add] using FlatAffineScalingNormalize.output_symbol hr a ns
    (setup r.num.natAbs bs qs) (setup r.den bs qs) scratch source 0 (fun _ => blank) 0 (fun _ => blank) 0 dest 0 i y j

/-- Exact ready bank and all source-array symbols after initialization,
actual rational scaling, and physical payload cleanup. -/
theorem realizes_hoare {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (hB : 0 < B) (hP : 0 < P)
    (bs qs ns : List Bool) (hb : Counter.value bs = B) (hq : Counter.value qs = modulus b)
    (hn : Counter.value ns = P) (cb : GrowingCounterData.Canonical bs)
    (cq : GrowingCounterData.Canonical qs) (cn : GrowingCounterData.Canonical ns)
    (source dest : ℤ → Fin 4)
    (hdblank : ∀ z, 0 ≤ z → z < ((P*(modulus b*B) : ℕ) : ℤ) → dest z = blank) :
    HoareTime (program hr)
      (fun v => v = input hr a bs qs ns source dest)
      (fun v => v = output hr a bs qs ns source dest ∧
        ∀ (i : Fin P) (y : Fin (modulus b)) (j : Fin B),
        v.tape (FlatAffineScaling.sourceSlot r)
          (((i.val*(modulus b*B)+(Swap.Modular.ratMod (modulus b) r*(y.val : ZMod (modulus b))).val*B+j.val : ℕ) : ℤ)) =
          a (FiberLayoutData.index i y j))
      ((2064+120*(r.num.natAbs+r.den))*(P*(modulus b*B))+254) := by
  have hs := FlatAffineScalingNormalize.realizes_hoare hr a hB hP ns hn cn
    (setup r.num.natAbs bs qs) (setup r.den bs qs) scratch
    (FlatAffineScalingBootstrap.setup_valid _ _ _ bs qs hb hq cb cq)
    (FlatAffineScalingBootstrap.setup_valid _ _ _ bs qs hb hq cb cq)
    (by intros; rfl) source 0 (fun _ => blank) 0 (fun _ => blank) 0 dest 0
    (by intros; rfl) (by intros; rfl) (by simpa only [zero_add] using hdblank)
  apply ((FlatAffineScalingBootstrap.bootstrap_hoare hr a bs qs ns source dest).seq hs).consequence
    (fun _ h => h) ?_ (by omega)
  rintro v rfl
  exact ⟨rfl,fun i y j => output_symbol hr a bs qs ns source dest i y j⟩

end
end IntegerMultBounds.Machine.FlatAffineScalingReady
