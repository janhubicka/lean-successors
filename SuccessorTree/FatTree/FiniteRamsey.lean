import SuccessorTree.FatTree.A4ReviewComplete

/-!
# Finite colourings from the fat-tree Ellentuck theorem

This file records the finite-partition consequence of the topological Ramsey
property that will be used for the alternative proof of the shape-preserving
Ramsey theorem.  It is deliberately independent of the direct shape-fusion
proof.
-/

namespace RamseySpace

universe u v w

namespace ApproximationSystem

variable {S : ApproximationSystem.{u, v}}

/-- A colour class determined by one fixed approximation level is open in the
Ellentuck topology. -/
theorem isOpen_approxColourClass
    {κ : Type w} (m : Nat) (colour : S.Approx m → κ) (c : κ) :
    @IsOpen S.Point S.ellentuckTopology
      {X | colour (S.approx m X) = c} := by
  rw [S.isOpen_ellentuck_iff]
  intro X hX
  refine ⟨m, S.approx m X, X, ⟨S.le_refl X, rfl⟩, ?_⟩
  intro Y hY
  change colour (S.approx m Y) = c
  change colour (S.approx m X) = c at hX
  rw [hY.2]
  exact hX

end ApproximationSystem

/-- A finite colouring of one approximation level is homogeneous on a
refined basic neighbourhood in every topological Ramsey space. -/
theorem finiteApproximationColouring
    {S : ApproximationSystem.{u, v}}
    (hTR : IsTopologicalRamseySpaceOnBasicNeighborhoods (S := S))
    {κ : Type w} [Fintype κ]
    {n m : Nat} (a : S.Approx n) (A : S.Point)
    (hne : (S.neighborhood a A).Nonempty)
    (colour : S.Approx m → κ) :
    ∃ B, B ∈ S.neighborhood a A ∧
      ∀ X, X ∈ S.neighborhood a B →
        ∀ Y, Y ∈ S.neighborhood a B →
          colour (S.approx m X) = colour (S.approx m Y) := by
  classical
  let class : κ → Set S.Point :=
    fun c => {X | colour (S.approx m X) = c}

  have hdecide :
      ∀ s : Finset κ, ∀ B : S.Point,
        B ∈ S.neighborhood a A →
        ∃ C, C ∈ S.neighborhood a B ∧
          ((∃ c ∈ s, S.neighborhood a C ⊆ class c) ∨
            ∀ c ∈ s, Disjoint (S.neighborhood a C) (class c)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro B hBA
        refine ⟨B, ⟨S.le_refl B, hBA.2⟩, Or.inr ?_⟩
        simp
    | @insert c s hc ih =>
        intro B hBA
        obtain ⟨C, hCB, hC⟩ := ih B hBA
        rcases hC with hhit | havoid
        · exact ⟨C, hCB, Or.inl (by
            rcases hhit with ⟨d, hd, hsub⟩
            exact ⟨d, Finset.mem_insert_of_mem hd, hsub⟩)⟩
        · have hneC : (S.neighborhood a C).Nonempty :=
            ⟨C, S.le_refl C, hCB.2⟩
          have hopen :
              @BaireMeasurableSet S.Point S.ellentuckTopology (class c) :=
            (S.isOpen_approxColourClass m colour c).baireMeasurableSet
          obtain ⟨D, hDC, hhom⟩ :=
            hTR.1 (class c) hopen a C hneC
          refine ⟨D, hDC, ?_⟩
          rcases hhom with hsub | hdis
          · exact Or.inl ⟨c, Finset.mem_insert_self c s, hsub⟩
          · apply Or.inr
            intro d hd
            rcases Finset.mem_insert.mp hd with hdc | hds
            · subst d
              exact hdis
            · exact (havoid d hds).mono_left
                (S.neighborhood_mono hDC.1)

  obtain ⟨B0, hB0A⟩ := hne
  obtain ⟨B, hBB0, hfinal⟩ :=
    hdecide Finset.univ B0 hB0A
  have hBA : B ∈ S.neighborhood a A :=
    S.neighborhood_mono hB0A.1 hBB0
  rcases hfinal with hhit | havoid
  · rcases hhit with ⟨c, _, hsub⟩
    refine ⟨B, hBA, ?_⟩
    intro X hX Y hY
    exact (hsub hX).trans (hsub hY).symm
  · exfalso
    let c : κ := colour (S.approx m B)
    have hdis := havoid c (Finset.mem_univ c)
    have hB : B ∈ S.neighborhood a B :=
      ⟨S.le_refl B, hBB0.2⟩
    have hBc : B ∈ class c := rfl
    exact Set.disjoint_left.1 hdis hB hBc

end RamseySpace
