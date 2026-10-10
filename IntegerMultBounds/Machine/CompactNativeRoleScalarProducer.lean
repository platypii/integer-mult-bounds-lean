import IntegerMultBounds.Machine.CompactNativeRoleStageCopy

/-! Paid scalar-to-original13 preparation. The complementary caller bank is
preserved literally, including the genuine native source at caller tape43.
Six retained runtime controller ports occupy the end of that bank. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleScalarProducer
noncomputable section
open ActiveRepairRankHeadersCommands (State bank caller)
open CompactNativeRoleStageCopy
variable {u : ℕ}

private theorem right_frame {n s t a k : ℕ} {M : Program n s a} {x y : Tapes n a}
    (h : HoareTime M (fun v => v=x) (fun v => v=y) k) (v : Tapes t a) :
    HoareTime (Placement.placed M (Equiv.refl (Fin (n+t))))
      (fun w => w=x.append v) (fun w => w=y.append v) k := by
  have he (z : Tapes n a) : Placement.combine (Equiv.refl (Fin (n+t))) z v=z.append v := by
    apply congrArg₂ Tapes.mk <;> funext i <;> rfl
  have hh := Placement.hoare_at h (Equiv.refl (Fin (n+t)))
    (Placement.combine (Equiv.refl (Fin (n+t))) x v) (Placement.active_combine _ _ _)
  apply hh.consequence (fun w hw => hw.trans (he x).symm) _ le_rfl
  rintro w ⟨z,hz,rfl⟩
  subst z
  simpa only [Placement.replace,Placement.extra_combine] using he y

def geometryPorts (u : ℕ) : Fin 9 → Fin (43+(u+6)) :=
  fun j => Fin.castAdd (u+6) (CompactNativeRoleScalarHeaders.sources j)
def controllerPorts (u : ℕ) : Fin 6 → Fin (43+(u+6)) :=
  fun j => Fin.natAdd 43 (Fin.natAdd u j)
def focus (u : ℕ) := sources (geometryPorts u) (controllerPorts u)

theorem focus_injective (u : ℕ) : Function.Injective (focus u) := by
  intro i j h
  have hv := congrArg Fin.val h
  fin_cases i <;> fin_cases j <;>
    simp [focus,sources,geometryPorts,controllerPorts,CompactNativeRoleScalarHeaders.sources] at hv ⊢ <;> omega

def controller (vs : Fin 6 → ℕ) : Tapes 6 2 :=
  ⟨fun _ => 1,fun i => RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits (vs i))⟩

def outputState (c m D K rho ell q d G : ℕ) (ctrl : Fin 6 → ℕ) : State :=
  metadata (values (CompactNativeRoleScalarHeaders.values c m D K rho ell q d G) ctrl)

theorem outputState_raw (c m D K rho ell q d G : ℕ) (ctrl : Fin 6 → ℕ) :
    outputState c m D K rho ell q d G ctrl=
      CompactSpectatorLeafSetup.raw (CompactGlobalReservation.shape c m d D G K 1)
        (CompactGlobalRowPadding.initialRows c m d K) ell
        (CompactNativeRoleReservedBridge.precision c m d D K q) rho
        (ctrl 2) (ctrl 1) (ctrl 0) (ctrl 3) (ctrl 4) (ctrl 5) := by
  funext i
  fin_cases i <;> rfl

theorem copy_runs (c m D K rho ell q d G : ℕ) (ctrl : Fin 6 → ℕ) (payload : Tapes u 2) :
    HoareTime (CompactNativeRoleStageCopy.program (focus u))
      (fun v => v=((bank (CompactNativeRoleScalarHeaders.prepared c m D K rho ell q d G)).append
        (payload.append (controller ctrl))).append (SharedBank.empty 28 2))
      (fun v => v=((bank (CompactNativeRoleScalarHeaders.prepared c m D K rho ell q d G)).append
        (payload.append (controller ctrl))).append (caller (outputState c m D K rho ell q d G ctrl)))
      (BinaryDescriptorInstallMarkedList.cost (instructions (focus u))
        (wordAt (focus u) (values (CompactNativeRoleScalarHeaders.values c m D K rho ell q d G) ctrl))) := by
  apply CompactNativeRoleStageCopy.runs
  · intro j
    fin_cases j <;>
      simp [focus,sources,geometryPorts,controllerPorts,Tapes.append,values,controller]
    all_goals exact CompactNativeRoleScalarHeaders.sources_ready c m D K rho ell q d G _
  · intro i j h
    rw [focus_injective u h]

def prepare (c m u : ℕ) :=
  seq (Placement.placed (CompactGlobalRowHeaderOps.compile (a:=2)
    (CompactNativeRolePrecisionHeaders.schedule c m)).2 (Equiv.refl (Fin (43+(u+6)))))
    (Placement.placed (CompactChildHeadersArithmetic.compile (a:=2)
      CompactNativeRoleScalarHeaders.schedule).2 (Equiv.refl (Fin (43+(u+6)))))

theorem prepare_runs (c m D K rho ell q d G : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hG : 0<G) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) (hDp : 0<D)
    (tail : Tapes (u+6) 2) :
    HoareTime (prepare c m u)
      (fun v => v=(bank (CompactReservedHeaders.initial D K rho ell q d G)).append tail)
      (fun v => v=(bank (CompactNativeRoleScalarHeaders.prepared c m D K rho ell q d G)).append tail)
      (CompactGlobalRowHeaderOps.scheduleCost (CompactNativeRolePrecisionHeaders.schedule c m)
        (CompactReservedHeaders.initial D K rho ell q d G)+1+
       CompactChildHeadersArithmetic.scheduleCost CompactNativeRoleScalarHeaders.schedule
        (CompactNativeRolePrecisionHeaders.prepared c m D K rho ell q d G)) := by
  have hrow : CompactGlobalRowPadding.rowAxes c m d≤D := by
    unfold CompactGlobalReservation.reservedAxes at hD
    omega
  exact (right_frame (CompactNativeRolePrecisionHeaders.runs c m D K rho ell q d G hc hm hd hK hrow hDp) tail).seq
    (right_frame (CompactNativeRoleScalarHeaders.runs c m D K rho ell q d G hK hd hG hD) tail)


def restore (u : ℕ) :=
  seq (Placement.placed (CompactChildHeadersArithmetic.compile (a:=2)
    CompactNativeRoleScalarHeaders.cleanup).2 (Equiv.refl (Fin (43+(u+6)))))
    (Placement.placed (CompactGlobalRowHeaderOps.compile (a:=2)
      CompactNativeRolePrecisionHeaders.cleanup).2 (Equiv.refl (Fin (43+(u+6)))))

theorem restore_runs (c m D K rho ell q d G : ℕ) (tail : Tapes (u+6) 2) :
    HoareTime (restore u)
      (fun v => v=(bank (CompactNativeRoleScalarHeaders.prepared c m D K rho ell q d G)).append tail)
      (fun v => v=(bank (CompactReservedHeaders.initial D K rho ell q d G)).append tail)
      (CompactChildHeadersArithmetic.scheduleCost CompactNativeRoleScalarHeaders.cleanup
        (CompactNativeRoleScalarHeaders.prepared c m D K rho ell q d G)+1+
       CompactGlobalRowHeaderOps.scheduleCost CompactNativeRolePrecisionHeaders.cleanup
        (CompactNativeRolePrecisionHeaders.prepared c m D K rho ell q d G)) := by
  exact (right_frame (CompactNativeRoleScalarHeaders.cleanup_runs c m D K rho ell q d G) tail).seq
    (right_frame (CompactNativeRolePrecisionHeaders.cleanup_runs c m D K rho ell q d G) tail)

def program (c m u : ℕ) :=
  seq (seq (extend (prepare c m u) 28) (CompactNativeRoleStageCopy.program (focus u)))
    (extend (restore u) 28)

def cost (c m D K rho ell q d G u : ℕ) (ctrl : Fin 6 → ℕ) :=
  CompactGlobalRowHeaderOps.scheduleCost (CompactNativeRolePrecisionHeaders.schedule c m)
    (CompactReservedHeaders.initial D K rho ell q d G)+1+
  CompactChildHeadersArithmetic.scheduleCost CompactNativeRoleScalarHeaders.schedule
    (CompactNativeRolePrecisionHeaders.prepared c m D K rho ell q d G)+1+
  BinaryDescriptorInstallMarkedList.cost (instructions (focus u))
    (wordAt (focus u) (values (CompactNativeRoleScalarHeaders.values c m D K rho ell q d G) ctrl))+1+
  (CompactChildHeadersArithmetic.scheduleCost CompactNativeRoleScalarHeaders.cleanup
    (CompactNativeRoleScalarHeaders.prepared c m D K rho ell q d G)+1+
   CompactGlobalRowHeaderOps.scheduleCost CompactNativeRolePrecisionHeaders.cleanup
    (CompactNativeRolePrecisionHeaders.prepared c m D K rho ell q d G))

theorem runs (c m D K rho ell q d G : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hG : 0<G) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) (hDp : 0<D)
    (ctrl : Fin 6 → ℕ) (payload : Tapes u 2) :
    HoareTime (program c m u)
      (fun v => v=((bank (CompactReservedHeaders.initial D K rho ell q d G)).append
        (payload.append (controller ctrl))).append (SharedBank.empty 28 2))
      (fun v => v=((bank (CompactReservedHeaders.initial D K rho ell q d G)).append
        (payload.append (controller ctrl))).append (caller (outputState c m D K rho ell q d G ctrl)))
      (cost c m D K rho ell q d G u ctrl) := by
  exact ((hoare_extend_eq (prepare_runs c m D K rho ell q d G hc hm hd hG hK hD hDp
    (payload.append (controller ctrl))) (SharedBank.empty 28 2)).seq
    (copy_runs c m D K rho ell q d G ctrl payload)).seq
    (hoare_extend_eq (restore_runs c m D K rho ell q d G (payload.append (controller ctrl)))
      (caller (outputState c m D K rho ell q d G ctrl)))

end
end IntegerMultBounds.Machine.CompactNativeRoleScalarProducer
