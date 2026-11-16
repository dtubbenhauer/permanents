import BlockPermanents.Bridges

/-! # Polarization on the span of elementary tensors

Two real parts of complex sesquilinear diagonals agreeing on products from two
complex subspaces agree on their full tensor-product span. -/
namespace BlockPermanents.Polarization
open scoped BigOperators
noncomputable section
variable {E A B : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]

abbrev Kernel (X : Type*) [AddCommGroup X] [Module ℂ X] :=
  X →ₛₗ[starRingEnd ℂ] X →ₗ[ℂ] ℂ

def mkKernel (f : E → E → ℂ)
    (la : ∀ x y z, f (x+y) z = f x z + f y z)
    (ls : ∀ a x z, f (a • x) z = star a * f x z)
    (ra : ∀ x y z, f x (y+z) = f x y + f x z)
    (rs : ∀ a x z, f x (a • z) = a * f x z) : Kernel E where
  toFun x := {toFun := f x, map_add' := ra x, map_smul' := fun a z => rs a x z}
  map_add' x y := LinearMap.ext (la x y)
  map_smul' a x := LinearMap.ext (ls a x)

def sym (K : Kernel E) : Kernel E := mkKernel (fun x y => K x y + star (K y x))
  (by intros; simp [add_add_add_comm])
  (by intros; simp [mul_add,mul_comm])
  (by intros; simp [add_add_add_comm])
  (by intros; simp [mul_add,mul_comm])

private theorem polar (f : E → E → ℂ)
    (la : ∀ x y z, f (x+y) z = f x z + f y z)
    (ls : ∀ x z, f (Complex.I • x) z = -Complex.I * f x z)
    (ra : ∀ x y z, f x (y+z) = f x y + f x z)
    (rs : ∀ x z, f x (Complex.I • z) = Complex.I * f x z)
    (U : Submodule ℂ E) (diag : ∀ x ∈ U, f x x = 0)
    {x y} (hx : x ∈ U) (hy : y ∈ U) : f x y = 0 := by
  have h := diag _ (U.add_mem hx hy)
  have g := diag _ (U.add_mem hx (U.smul_mem Complex.I hy))
  simp only [la,ra,ls,rs,diag x hx,diag y hy,mul_zero,zero_add,add_zero] at h g
  have i : Complex.I * (f x y - f y x) = 0 := by linear_combination g
  have j := (mul_eq_zero.mp i).resolve_left Complex.I_ne_zero
  linear_combination (h+j)/2

variable {I J : Type*}
abbrev Vector (T : Type*) := T → ℂ

theorem product_ext (U : Submodule ℂ (Vector I)) (V : Submodule ℂ (Vector J))
    (K L : Kernel (Vector (I × J)))
    (eq : ∀ x ∈ U, ∀ y ∈ V, (K (Bend.product x y) (Bend.product x y)).re =
      (L (Bend.product x y) (Bend.product x y)).re)
    {z : Vector (I × J)}
    (hz : z ∈ Submodule.span ℂ {u | ∃ x ∈ U, ∃ y ∈ V, Bend.product x y = u}) :
    (K z z).re = (L z z).re := by
  let T := sym (K-L)
  have lp (x x' : Vector I) (y : Vector J) : Bend.product (x+x') y =
      Bend.product x y + Bend.product x' y := by ext p; exact add_mul _ _ _
  have rp (x : Vector I) (y y' : Vector J) : Bend.product x (y+y') =
      Bend.product x y + Bend.product x y' := by ext p; exact mul_add _ _ _
  have ls (a : ℂ) (x : Vector I) (y : Vector J) : Bend.product (a • x) y =
      a • Bend.product x y := by ext p; exact mul_assoc _ _ _
  have rs (a : ℂ) (x : Vector I) (y : Vector J) : Bend.product x (a • y) =
      a • Bend.product x y := by ext p; exact mul_left_comm _ _ _
  have diagonal (x) (hx : x ∈ U) (y) (hy : y ∈ V) :
      T (Bend.product x y) (Bend.product x y) = 0 := by
    have h := eq x hx y hy
    apply Complex.ext <;>
      simp [T,sym,mkKernel,Complex.add_re,Complex.sub_re,Complex.add_im,h]
  have first (x) (hx : x ∈ U) (x') (hx' : x' ∈ U) (y) (hy : y ∈ V) :
      T (Bend.product x y) (Bend.product x' y) = 0 := by
    apply polar (fun a b => T (Bend.product a y) (Bend.product b y)) _ _ _ _ U
      (fun a ha => diagonal a ha y hy) hx hx'
    all_goals intros; simp [lp,ls]
  have cross (x) (hx : x ∈ U) (x') (hx' : x' ∈ U) (y) (hy : y ∈ V)
      (y') (hy' : y' ∈ V) : T (Bend.product x y) (Bend.product x' y') = 0 := by
    apply polar (fun a b => T (Bend.product x a) (Bend.product x' b)) _ _ _ _ V
      (fun a ha => first x hx x' hx' a ha) hy hy'
    all_goals intros; simp [rp,rs]
  have hxy {a b} (ha : a ∈ Submodule.span ℂ {u | ∃ x ∈ U, ∃ y ∈ V, Bend.product x y = u})
      (hb : b ∈ Submodule.span ℂ {u | ∃ x ∈ U, ∃ y ∈ V, Bend.product x y = u}) : T a b = 0 := by
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨x,hx,y,hy,rfl⟩ := ha
      induction hb using Submodule.span_induction with
      | mem b hb =>
        obtain ⟨x',hx',y',hy',rfl⟩ := hb
        exact cross x hx x' hx' y hy y' hy'
      | zero => simp
      | add _ _ _ _ h g => simp [h,g]
      | smul _ _ _ h => simp [h]
    | zero => simp
    | add _ _ _ _ h g => simp [h,g]
    | smul _ _ _ h => simp [h]
  have vanish := hxy hz hz
  have v := congrArg Complex.re vanish
  simp [T,sym,mkKernel,Complex.add_re,Complex.sub_re] at v
  linarith

/-- Coordinate inner product of the outputs of two linear maps. -/
def pair {D : Type*} [Fintype D] (a b : E →ₗ[ℂ] Vector D) : Kernel E :=
  mkKernel (fun x y => Closures.bracket (a x) (b y))
    (by intros; simp [Closures.bracket,add_mul,Finset.sum_add_distrib])
    (by intros; simp [Closures.bracket,← Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm])
    (by intros; simp [Closures.bracket,mul_add,Finset.sum_add_distrib])
    (by intros; simp [Closures.bracket,← Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm])

theorem pair_energy {D : Type*} [Fintype D] (a : E →ₗ[ℂ] Vector D) (z : E) :
    (pair a a z z).re = Bend.energy (a z) := by
  simp [pair,mkKernel,Closures.bracket,Bend.energy,Complex.normSq_apply]

end
end BlockPermanents.Polarization
