import Mathlib.Algebra.Exact.Basic

/-! Chapter 3 -/

variable {R : Type*} [CommRing R]
variable {Z : Type*} [AddCommGroup Z] [Module R Z] [Subsingleton Z]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-! Section 7 -/

lemma zeromap_injective
    {M' : Type*} [AddCommGroup M'] [Module R M']
    (f : Z →ₗ[R] M) (g : M →ₗ[R] M') (hexact : Function.Exact f g) :
    Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨z, rfl⟩ := (hexact a).mp ha
    rw [Subsingleton.elim z 0]
    apply map_zero

lemma surjective_zeromap
    {M' : Type*} [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M') (g : M' →ₗ[R] Z) (hexact : Function.Exact f g) :
    Function.Surjective f := by
    intro b
    exact (hexact b).mp (Subsingleton.eq_zero (g b))

-- 7.1
theorem exercise_7_1
    (f : Z →ₗ[R] M) (φ : M →ₗ[R] Z) (hexact : Function.Exact f φ) :
    Subsingleton M := by
    constructor
    intro a b
    apply zeromap_injective f φ hexact
    exact Subsingleton.elim (φ a) (φ b)

-- 7.2
noncomputable def exercise_7_2
    {Z M M' Z' : Type*} [AddCommGroup Z] [Module R Z] [Subsingleton Z]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup Z'] [Module R Z'] [Subsingleton Z']
    (f : Z →ₗ[R] M) (ψ : M →ₗ[R] M') (φ : M' →ₗ[R] Z')
    (hM : Function.Exact f ψ) (hM' : Function.Exact ψ φ) :
    M ≃ₗ[R] M' :=
    LinearEquiv.ofBijective ψ
        ⟨zeromap_injective f ψ hM,
         surjective_zeromap ψ φ hM'⟩
