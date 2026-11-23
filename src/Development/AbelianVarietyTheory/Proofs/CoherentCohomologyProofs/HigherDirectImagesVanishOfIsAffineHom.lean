module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PushComparisonBijectiveOfIsClosedEmbedding
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsPowMulPowEqOfIsZeroCechH
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SubsingletonOfSheafPullback
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite

universe w t v u

noncomputable section

namespace GlobalTheory

section Space

open SheafPull SheafLES

attribute [-instance] hasSheafify_topCat hasExt_sheaf_topCat

variable {X Y : TopCat.{u}} [HasExt.{u} (AbSheaf X)] [HasExt.{u} (AbSheaf Y)] (f : Y ⟶ X)
  {F F' : AbSheaf X} {G G' : AbSheaf Y} (φ : F ⟶ (push f).obj G) (n : ℕ)
  {V V' : Opens X} {W W' : Opens Y}

theorem SheafPull.pull_map (s : F' ⟶ F) (i : W ⟶ (Opens.map f).obj V) (x : Sheaf.H'.{u} F' n V) :
    pull.{u, u} f φ n i (map s n V x) = pull.{u, u} f (s ≫ φ) n i x :=
  sitePull_map _ _ _ n _ x

theorem SheafPull.map_pull (s : G ⟶ G') (i : W ⟶ (Opens.map f).obj V) (x : Sheaf.H'.{u} F n V) :
    map s n W (pull.{u, u} f φ n i x) = pull.{u, u} f (φ ≫ (push f).map s) n i x :=
  map_sitePull _ _ _ n _ x

theorem SheafPull.pull_res (k : V' ⟶ V) (i : W ⟶ (Opens.map f).obj V') (x : Sheaf.H'.{u} F n V) :
    pull.{u, u} f φ n i (res F n k x) = pull.{u, u} f φ n (i ≫ (Opens.map f).map k) x :=
  sitePull_res _ _ n _ _ x

theorem SheafPull.equivZero_pull (i : W ⟶ (Opens.map f).obj V) (x : Sheaf.H'.{u} F 0 V) :
    equivZero G W (pull.{u, u} f φ 0 i x) = G.obj.map i.op (φ.hom.app (op V) (equivZero F V x)) :=
  equivZero_sitePull _ _ _ x

theorem SheafPull.pull_δ {A : ShortComplex (AbSheaf X)} {B : ShortComplex (AbSheaf Y)}
    (hA : A.ShortExact) (hB : B.ShortExact) (ψ : A ⟶ B.map (push f))
    (i : W ⟶ (Opens.map f).obj V) (x : Sheaf.H'.{u} A.X₃ n V) :
    pull.{u, u} f (G := B.X₁) ψ.τ₁ (n + 1) i (δ hA n V x) =
      δ hB n W (pull.{u, u} f (G := B.X₃) ψ.τ₃ n i x) :=
  sitePull_δ _ hA hB ψ n i x

end Space

section Morphism

variable {X Y : Scheme.{u}} {g : Y ⟶ X}

theorem smulHom_pushforward (g : Y ⟶ X) (G : Y.Modules) (r : Γ(X, ⊤)) :
    smulHom ((Scheme.Modules.pushforward g).obj G) r =
      (Scheme.Modules.pushforward g).map (smulHom G (g.appTop r)) := by
  refine Scheme.Modules.hom_ext _ _ fun W => ?_
  ext x
  have h : g.app W (restrictGlobal X W r) = restrictGlobal Y (g ⁻¹ᵁ W) (g.appTop r) :=
    ConcreteCategory.congr_hom (g.naturality (homOfLE le_top : W ⟶ ⊤).op) r
  exact congrArg (fun a : Γ(Y, g ⁻¹ᵁ W) => (a • (show Γ(G, g ⁻¹ᵁ W) from x) : Γ(G, g ⁻¹ᵁ W))) h

section Pull

variable {F F' : X.Modules} {G G' : Y.Modules}

def toAbSheafPush (φ : F ⟶ (Scheme.Modules.pushforward g).obj G) :
    (toAbSheaf (X := X)).obj F ⟶ (SheafPull.push g.base).obj ((toAbSheaf (X := Y)).obj G) :=
  (toAbSheaf (X := X)).map φ

theorem toAbSheafPush_comp (s : F' ⟶ F) (φ : F ⟶ (Scheme.Modules.pushforward g).obj G) :
    toAbSheafPush (s ≫ φ) = (toAbSheaf (X := X)).map s ≫ toAbSheafPush φ := rfl

theorem toAbSheafPush_comp_map (φ : F ⟶ (Scheme.Modules.pushforward g).obj G) (s : G ⟶ G') :
    toAbSheafPush (φ ≫ (Scheme.Modules.pushforward g).map s) =
      toAbSheafPush φ ≫ (SheafPull.push g.base).map ((toAbSheaf (X := Y)).map s) := rfl

-- `hasExt_sheaf_scheme X` carries `TopCat.Sheaf.instAbelian`, whereas `Sheaf.H'` and `sitePull`
-- expect `CategoryTheory.sheafIsAbelian`. Transporting along this `rfl` equality once avoids
-- repeated kernel unfolding of `@[reducible] def HasExt` during `isDefEq`.
private theorem abelian_scheme_eq (X : Scheme.{u}) :
    (@TopCat.Sheaf.instAbelian X.toSheafedSpace.toPresheafedSpace.carrier AddCommGrpCat.{u} _
      (hasSheafify_scheme X) _) =
      CategoryTheory.sheafIsAbelian (J := Opens.grothendieckTopology ↥X) (D := AddCommGrpCat.{u}) :=
  rfl

private theorem hasExt_scheme_site (X : Scheme.{u}) :
    @HasExt.{u} (Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}) _
      (CategoryTheory.sheafIsAbelian (J := Opens.grothendieckTopology ↥X) (D := AddCommGrpCat.{u})) :=
  Eq.mp (congrArg (fun a => @HasExt.{u} _ _ a) (abelian_scheme_eq X)) (hasExt_sheaf_scheme X)

private def sitePullScheme (g : Y ⟶ X)
    {F : Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}}
    {G : Sheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}}
    (φ : F ⟶ (SheafPull.push g.base).obj G) (n : ℕ)
    {V : X.Opens} {W : Y.Opens} (i : W ⟶ (Opens.map g.base).obj V) :
    @Sheaf.H'.{u} _ _ (Opens.grothendieckTopology ↥X) (hasSheafify_scheme X) (hasExt_scheme_site X) F n V →+
    @Sheaf.H'.{u} _ _ (Opens.grothendieckTopology ↥Y) (hasSheafify_scheme Y) (hasExt_scheme_site Y) G n W :=
  @SheafPull.sitePull.{u, u} _ _ _ _ (Opens.grothendieckTopology ↥X) (Opens.grothendieckTopology ↥Y)
    (hasSheafify_scheme X) (hasSheafify_scheme Y) (Opens.map g.base) inferInstance
    (inferInstanceAs (SheafPull.push g.base).IsRightAdjoint)
    (SheafPull.preservesFiniteLimits_sheafPullback g.base)
    (hasExt_scheme_site X) (hasExt_scheme_site Y) F G φ n V W i

private theorem sitePullScheme_map (g : Y ⟶ X)
    {F F' : Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}}
    {G : Sheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}}
    (φ : F ⟶ (SheafPull.push g.base).obj G) (s : F' ⟶ F) (n : ℕ)
    {V : X.Opens} {W : Y.Opens} (i : W ⟶ (Opens.map g.base).obj V)
    (x : @Sheaf.H'.{u} _ _ (Opens.grothendieckTopology ↥X) (hasSheafify_scheme X)
      (hasExt_scheme_site X) F' n V) :
    sitePullScheme g φ n i (@SheafLES.map.{u} _ _ (Opens.grothendieckTopology ↥X)
      (hasSheafify_scheme X) (hasExt_scheme_site X) _ _ s n V x) =
      sitePullScheme g (s ≫ φ) n i x :=
  @SheafPull.sitePull_map.{u, u} _ _ _ _ (Opens.grothendieckTopology ↥X)
    (Opens.grothendieckTopology ↥Y) (hasSheafify_scheme X) (hasSheafify_scheme Y) (Opens.map g.base)
    inferInstance (inferInstanceAs (SheafPull.push g.base).IsRightAdjoint)
    (SheafPull.preservesFiniteLimits_sheafPullback g.base)
    (hasExt_scheme_site X) (hasExt_scheme_site Y) _ _ _ φ s n V W i x

private theorem map_sitePullScheme (g : Y ⟶ X)
    {F : Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}}
    {G G' : Sheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}}
    (φ : F ⟶ (SheafPull.push g.base).obj G) (s : G ⟶ G') (n : ℕ)
    {V : X.Opens} {W : Y.Opens} (i : W ⟶ (Opens.map g.base).obj V)
    (x : @Sheaf.H'.{u} _ _ (Opens.grothendieckTopology ↥X) (hasSheafify_scheme X)
      (hasExt_scheme_site X) F n V) :
    @SheafLES.map.{u} _ _ (Opens.grothendieckTopology ↥Y) (hasSheafify_scheme Y)
      (hasExt_scheme_site Y) _ _ s n W (sitePullScheme g φ n i x) =
      sitePullScheme g (φ ≫ (SheafPull.push g.base).map s) n i x :=
  @SheafPull.map_sitePull.{u, u} _ _ _ _ (Opens.grothendieckTopology ↥X)
    (Opens.grothendieckTopology ↥Y) (hasSheafify_scheme X) (hasSheafify_scheme Y) (Opens.map g.base)
    inferInstance (inferInstanceAs (SheafPull.push g.base).IsRightAdjoint)
    (SheafPull.preservesFiniteLimits_sheafPullback g.base)
    (hasExt_scheme_site X) (hasExt_scheme_site Y) _ _ _ φ s n V W i x

private def toH'Site (F : X.Modules) (U : X.Opens) (n : ℕ) :
    cohOn F U n ≃+
      @Sheaf.H'.{u} _ _ (Opens.grothendieckTopology ↥X) (hasSheafify_scheme X) (hasExt_scheme_site X)
        ((toAbSheaf (X := X)).obj F) n U :=
  cohOn.toH' F U n

private theorem toH'Site_smul {R : Type v} [CommRing R] [Algebra R Γ(X, ⊤)]
    {F : X.Modules} {U : X.Opens} {n : ℕ} (r : R) (x : cohOn F U n) :
    toH'Site F U n (r • x) =
      @SheafLES.map.{u} _ _ (Opens.grothendieckTopology ↥X) (hasSheafify_scheme X)
        (hasExt_scheme_site X) _ _ ((toAbSheaf (X := X)).map (smulHom F (algebraMap R Γ(X, ⊤) r)))
        n U (toH'Site F U n x) :=
  cohOn.toH'_smul r x

private theorem toH'Site_map {R : Type v} [CommRing R] [Algebra R Γ(X, ⊤)]
    {F F' : X.Modules} (s : F' ⟶ F) {V : X.Opens} {n : ℕ} (x : cohOn F' V n) :
    toH'Site F V n (cohOn.map R s V n x) =
      @SheafLES.map.{u} _ _ (Opens.grothendieckTopology ↥X) (hasSheafify_scheme X)
        (hasExt_scheme_site X) _ _ ((toAbSheaf (X := X)).map s) n V (toH'Site F' V n x) :=
  cohOn.toH'_map R s x

private theorem toH'Site_res {R : Type v} [CommRing R] [Algebra R Γ(X, ⊤)]
    {F : X.Modules} {V V' : X.Opens} (k : V' ≤ V) {n : ℕ} (x : cohOn F V n) :
    toH'Site F V' n (cohOn.res R F k n x) =
      @SheafLES.res.{u} _ _ (Opens.grothendieckTopology ↥X) (hasSheafify_scheme X)
        (hasExt_scheme_site X) _ n _ _ (homOfLE k) (toH'Site F V n x) :=
  cohOn.toH'_res R k x

private theorem toΓ_zeroEquiv_site {R : Type v} [CommRing R] [Algebra R Γ(X, ⊤)]
    {F : X.Modules} {V : X.Opens} (x : cohOn F V 0) :
    sectionsOn.toΓ F V (cohOn.zeroEquiv R F V x) =
      @SheafLES.equivZero.{u} _ _ (Opens.grothendieckTopology ↥X) (hasSheafify_scheme X)
        (hasExt_scheme_site X) ((toAbSheaf (X := X)).obj F) V (toH'Site F V 0 x) :=
  cohOn.toΓ_zeroEquiv R x

variable {R : Type v} [CommRing R] [Algebra R Γ(X, ⊤)] {S : Type t} [CommRing S]
  [Algebra S Γ(Y, ⊤)] {σ : R →+* S}
  (hσ : ∀ r, g.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap S Γ(Y, ⊤) (σ r))

include hσ in
private theorem cohOn.pull_map_smul (φ : F ⟶ (Scheme.Modules.pushforward g).obj G)
    {V : X.Opens} {W : Y.Opens} (h : W ≤ g ⁻¹ᵁ V) (n : ℕ) (r : R) (x : cohOn F V n) :
    (toH'Site G W n).symm (sitePullScheme g (toAbSheafPush φ) n (homOfLE h) (toH'Site F V n (r • x))) =
      σ r • (toH'Site G W n).symm
        (sitePullScheme g (toAbSheafPush φ) n (homOfLE h) (toH'Site F V n x)) := by
  have e : smulHom F (algebraMap R Γ(X, ⊤) r) ≫ φ = φ ≫ (Scheme.Modules.pushforward g).map
      (smulHom G (algebraMap S Γ(Y, ⊤) (σ r))) := by
    rw [smulHom_comp, smulHom_pushforward, hσ]
  have h₁ := sitePullScheme_map g (toAbSheafPush φ)
    ((toAbSheaf (X := X)).map (smulHom F (algebraMap R Γ(X, ⊤) r))) n (homOfLE h) (toH'Site F V n x)
  have h₂ := map_sitePullScheme g (toAbSheafPush φ)
    ((toAbSheaf (X := Y)).map (smulHom G (algebraMap S Γ(Y, ⊤) (σ r)))) n (homOfLE h) (toH'Site F V n x)
  rw [← toAbSheafPush_comp, e] at h₁
  rw [← toAbSheafPush_comp_map] at h₂
  apply (toH'Site G W n).injective
  rw [AddEquiv.apply_symm_apply, toH'Site_smul, toH'Site_smul, AddEquiv.apply_symm_apply]
  exact h₁.trans h₂.symm

def cohOn.pull (φ : F ⟶ (Scheme.Modules.pushforward g).obj G) {V : X.Opens} {W : Y.Opens}
    (h : W ≤ g ⁻¹ᵁ V) (n : ℕ) : cohOn F V n →ₛₗ[σ] cohOn G W n where
  toAddHom := (cohOn.toH' G W n).symm.toAddHom.comp
    ((@SheafPull.sitePull.{u, u} _ _ _ _ (Opens.grothendieckTopology ↥X)
      (Opens.grothendieckTopology ↥Y) (hasSheafify_scheme X) (hasSheafify_scheme Y)
      (Opens.map g.base) inferInstance
      (inferInstanceAs (SheafPull.push g.base).IsRightAdjoint)
      (SheafPull.preservesFiniteLimits_sheafPullback g.base)
      (Eq.mp (congrArg (fun a => @HasExt.{u} _ _ a)
        (show (@TopCat.Sheaf.instAbelian X.toSheafedSpace.toPresheafedSpace.carrier AddCommGrpCat.{u} _
          (hasSheafify_scheme X) _) =
          CategoryTheory.sheafIsAbelian (J := Opens.grothendieckTopology ↥X) (D := AddCommGrpCat.{u}) from rfl))
        (hasExt_sheaf_scheme X))
      (Eq.mp (congrArg (fun a => @HasExt.{u} _ _ a)
        (show (@TopCat.Sheaf.instAbelian Y.toSheafedSpace.toPresheafedSpace.carrier AddCommGrpCat.{u} _
          (hasSheafify_scheme Y) _) =
          CategoryTheory.sheafIsAbelian (J := Opens.grothendieckTopology ↥Y) (D := AddCommGrpCat.{u}) from rfl))
        (hasExt_sheaf_scheme Y))
      _ _ (toAbSheafPush φ) n V W (homOfLE h)).toAddHom.comp
      (cohOn.toH' F V n).toAddHom)
  map_smul' r x := by exact cohOn.pull_map_smul hσ φ h n r x

variable (φ : F ⟶ (Scheme.Modules.pushforward g).obj G) {V V' : X.Opens} {W W' : Y.Opens} {n : ℕ}

private theorem cohOn.toH'Site_pull (h : W ≤ g ⁻¹ᵁ V) (x : cohOn F V n) :
    toH'Site G W n (cohOn.pull hσ φ h n x) =
      sitePullScheme g (toAbSheafPush φ) n (homOfLE h) (toH'Site F V n x) :=
  rfl

theorem cohOn.toH'_pull (h : W ≤ g ⁻¹ᵁ V) (x : cohOn F V n) :
    cohOn.toH' G W n (cohOn.pull hσ φ h n x) =
      SheafPull.pull.{u, u} g.base (toAbSheafPush φ) n (homOfLE h) (cohOn.toH' F V n x) :=
  cohOn.toH'Site_pull hσ φ h x

theorem cohOn.pull_map (s : F' ⟶ F) (h : W ≤ g ⁻¹ᵁ V) (x : cohOn F' V n) :
    cohOn.pull hσ φ h n (cohOn.map R s V n x) = cohOn.pull hσ (s ≫ φ) h n x := by
  apply (toH'Site G W n).injective
  rw [cohOn.toH'Site_pull, cohOn.toH'Site_pull, toH'Site_map, toAbSheafPush_comp]
  exact sitePullScheme_map g (toAbSheafPush φ) ((toAbSheaf (X := X)).map s) n (homOfLE h) _

theorem cohOn.map_pull (s : G ⟶ G') (h : W ≤ g ⁻¹ᵁ V) (x : cohOn F V n) :
    cohOn.map S s W n (cohOn.pull hσ φ h n x) =
      cohOn.pull hσ (φ ≫ (Scheme.Modules.pushforward g).map s) h n x := by
  apply (toH'Site G' W n).injective
  rw [toH'Site_map, cohOn.toH'Site_pull, cohOn.toH'Site_pull, toAbSheafPush_comp_map]
  exact map_sitePullScheme g (toAbSheafPush φ) ((toAbSheaf (X := Y)).map s) n (homOfLE h) _

theorem cohOn.pull_res (k : V' ≤ V) (h : W ≤ g ⁻¹ᵁ V') (x : cohOn F V n) :
    cohOn.pull hσ φ h n (cohOn.res R F k n x) =
      cohOn.pull hσ φ (h.trans (g.preimage_mono k)) n x := by
  apply (toH'Site G W n).injective
  rw [cohOn.toH'Site_pull, cohOn.toH'Site_pull, toH'Site_res]
  exact @SheafPull.sitePull_res.{u, u} _ _ _ _
    (Opens.grothendieckTopology ↥X) (Opens.grothendieckTopology ↥Y)
    (hasSheafify_scheme X) (hasSheafify_scheme Y) (Opens.map g.base) inferInstance
    (inferInstanceAs (SheafPull.push g.base).IsRightAdjoint)
    (SheafPull.preservesFiniteLimits_sheafPullback g.base)
    (hasExt_scheme_site X) (hasExt_scheme_site Y) _ _ (toAbSheafPush φ) n V V' W
    (homOfLE h) (homOfLE k) _

theorem cohOn.zeroEquiv_pull (h : W ≤ g ⁻¹ᵁ V) (x : cohOn F V 0) :
    cohOn.zeroEquiv S G W (cohOn.pull hσ φ h 0 x) =
      sectionsOn.res S G h (sectionsOn.mapOver hσ φ V (cohOn.zeroEquiv R F V x)) := by
  apply (sectionsOn.toΓ G W).injective
  rw [toΓ_zeroEquiv_site, cohOn.toH'Site_pull, sectionsOn.toΓ_res, sectionsOn.toΓ_mapOver,
    toΓ_zeroEquiv_site]
  exact @SheafPull.equivZero_sitePull.{u, u} _ _ _ _
    (Opens.grothendieckTopology ↥X) (Opens.grothendieckTopology ↥Y)
    (hasSheafify_scheme X) (hasSheafify_scheme Y) (Opens.map g.base) inferInstance
    (inferInstanceAs (SheafPull.push g.base).IsRightAdjoint)
    (SheafPull.preservesFiniteLimits_sheafPullback g.base)
    (hasExt_scheme_site X) (hasExt_scheme_site Y) _ _ (toAbSheafPush φ) V W (homOfLE h) _

theorem cohOn.pull_bijective_of_toAbSheaf (h : W ≤ g ⁻¹ᵁ V)
    (H : Function.Bijective (SheafPull.pull.{u, u} g.base (toAbSheafPush φ) n (homOfLE h))) :
    Function.Bijective (cohOn.pull hσ φ h n) :=
  (EquivLike.comp_bijective _ (cohOn.toH' G W n)).1
    ((congrArg Function.Bijective (funext (cohOn.toH'_pull hσ φ h))).mpr
      (H.comp (cohOn.toH' F V n).bijective))

theorem higherDirectImagesVanish_of_isAffineHom (g : Y ⟶ X) [IsAffineHom g] (G : Y.Modules)
    [G.IsQuasicoherent] :
    SheafPull.HigherDirectImagesVanish.{u} g.base ((toAbSheaf (X := Y)).obj G) :=
  SheafPull.higherDirectImagesVanish_of_basis _ _ fun V x hx => by
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
    refine ⟨W, hWV, hxW, fun n hn => ?_⟩
    have := cohOn.subsingleton_of_isAffineOpen G (IsAffineOpen.preimage hW g) hn
    exact (cohOn.toH' G (g ⁻¹ᵁ W) n).symm.injective.subsingleton


variable (G V n) in
theorem cohOn.pull_id_bijective [IsAffineHom g] [G.IsQuasicoherent] :
    Function.Bijective (cohOn.pull hσ (𝟙 ((Scheme.Modules.pushforward g).obj G))
      (le_refl (g ⁻¹ᵁ V)) n) :=
  cohOn.pull_bijective_of_toAbSheaf hσ _ _
    (SheafPull.pushComparison_bijective.{u, u} (higherDirectImagesVanish_of_isAffineHom g G) n V)


variable (F n) in
theorem cohOn.pull_restrict_bijective [IsOpenImmersion g] (h : W ≤ g ⁻¹ᵁ V) (h' : V ≤ g ''ᵁ W) :
    Function.Bijective
      (cohOn.pull hσ (G := F.restrict g) ((Scheme.Modules.restrictAdjunction g).unit.app F) h n) :=
  cohOn.pull_bijective_of_toAbSheaf hσ _ _
    (SheafPull.pull_restrUnit_bijective.{u, u} g.isOpenEmbedding ((toAbSheaf (X := X)).obj F) n
      (homOfLE h) h')

end Pull

section Linear

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] [Algebra R Γ(Y, ⊤)]
  (hg : ∀ r, g.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(Y, ⊤) r)

section Push

variable [IsAffineHom g] (G : Y.Modules) [G.IsQuasicoherent]

def cohOn.pushforwardEquiv (V : X.Opens) (n : ℕ) :
    cohOn ((Scheme.Modules.pushforward g).obj G) V n ≃ₗ[R] cohOn G (g ⁻¹ᵁ V) n :=
  LinearEquiv.ofBijective _ (cohOn.pull_id_bijective (G := G) (σ := RingHom.id R) (V := V) (n := n) hg)

theorem cohOn.pushforwardEquiv_apply (V : X.Opens) (n : ℕ)
    (x : cohOn ((Scheme.Modules.pushforward g).obj G) V n) :
    cohOn.pushforwardEquiv R hg G V n x =
      cohOn.pull (σ := RingHom.id R) hg (𝟙 _) (le_refl (g ⁻¹ᵁ V)) n x := rfl


variable {G} in
theorem cohOn.pushforwardEquiv_map {G' : Y.Modules} [G'.IsQuasicoherent] (s : G ⟶ G')
    (V : X.Opens) (n : ℕ) (x : cohOn ((Scheme.Modules.pushforward g).obj G) V n) :
    cohOn.pushforwardEquiv R hg G' V n
        (cohOn.map R ((Scheme.Modules.pushforward g).map s) V n x) =
      cohOn.map R s (g ⁻¹ᵁ V) n (cohOn.pushforwardEquiv R hg G V n x) := by
  rw [cohOn.pushforwardEquiv_apply, cohOn.pushforwardEquiv_apply, cohOn.pull_map, cohOn.map_pull,
    Category.comp_id, Category.id_comp]

theorem cohOn.zeroEquiv_pushforwardEquiv (V : X.Opens)
    (x : cohOn ((Scheme.Modules.pushforward g).obj G) V 0) :
    sectionsOn.toΓ G (g ⁻¹ᵁ V) (cohOn.zeroEquiv R G _ (cohOn.pushforwardEquiv R hg G V 0 x)) =
      sectionsOn.toΓ _ V (cohOn.zeroEquiv R _ V x) := by
  rw [cohOn.pushforwardEquiv_apply, cohOn.zeroEquiv_pull, sectionsOn.res_refl]
  rfl

def coh.pushforwardEquiv (n : ℕ) :
    coh ((Scheme.Modules.pushforward g).obj G) n ≃ₗ[R] coh G n :=
  cohOn.pushforwardEquiv R hg G ⊤ n


variable {G} in
theorem coh.pushforwardEquiv_map {G' : Y.Modules} [G'.IsQuasicoherent] (s : G ⟶ G')
    (n : ℕ) (x : coh ((Scheme.Modules.pushforward g).obj G) n) :
    coh.pushforwardEquiv R hg G' n (cohOn.map R ((Scheme.Modules.pushforward g).map s) ⊤ n x) =
      cohOn.map R s ⊤ n (coh.pushforwardEquiv R hg G n x) :=
  cohOn.pushforwardEquiv_map R hg s ⊤ n x

end Push

section Restrict

variable [IsOpenImmersion g] (F : X.Modules)

def cohOn.restrictEquiv {V : X.Opens} {W : Y.Opens} (h : g ''ᵁ W = V) (n : ℕ) :
    cohOn F V n ≃ₗ[R] cohOn (F.restrict g) W n :=
  LinearEquiv.ofBijective _ (cohOn.pull_restrict_bijective (F := F) (σ := RingHom.id R) (n := n) hg
    ((g.preimage_image_eq W).ge.trans (g.preimage_mono h.le)) h.ge)

end Restrict

end Linear

theorem hdim_pushforward (k : Type v) [Field k] [Algebra k Γ(X, ⊤)] [Algebra k Γ(Y, ⊤)]
    (hg : ∀ r, g.appTop (algebraMap k Γ(X, ⊤) r) = algebraMap k Γ(Y, ⊤) r) [IsAffineHom g]
    (G : Y.Modules) [G.IsQuasicoherent] (n : ℕ) :
    hdim k ((Scheme.Modules.pushforward g).obj G) n = hdim k G n :=
  (coh.pushforwardEquiv k hg G n).finrank_eq

theorem appTop_algebraΓOfHom {R : Type u} [CommRing R] (g : Y ⟶ X) (p : X ⟶ Spec (.of R))
    {q : Y ⟶ Spec (.of R)} (w : g ≫ p = q) (r : R) :
    letI := algebraΓOfHom p
    letI := algebraΓOfHom q
    g.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(Y, ⊤) r := by
  subst w
  simp only [algebraΓOfHom_algebraMap, Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply]

end Morphism

end GlobalTheory
