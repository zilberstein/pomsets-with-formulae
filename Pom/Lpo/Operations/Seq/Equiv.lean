import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Equiv.Set

namespace Equiv

open Classical

def singleton {α : Type} (x y : α) : ({x} : Set α) ≃ ({y} : Set α) :=
  (Equiv.Set.singleton.{0} x).trans (Equiv.Set.singleton y).symm

noncomputable def union {α : Type} {X X' Y Y' : Set α} (e₁ : X ≃ Y) (e₂ : X' ≃ Y')
    (h₁ : Disjoint X X') (h₂ : Disjoint Y Y') :
    ↑(X ∪ X') ≃ ↑(Y ∪ Y') :=
  (Equiv.Set.union h₁).trans
    ((e₁.sumCongr e₂).trans (Equiv.Set.union h₂).symm)

lemma union_symm {α : Type} {X X' Y Y' : Set α} {e₁ : X ≃ Y} {e₂ : X' ≃ Y'}
    {h₁ : Disjoint X X'} {h₂ : Disjoint Y Y'} :
    (union e₁ e₂ h₁ h₂).symm = union e₁.symm e₂.symm h₂ h₁ := by
  unfold union; ext1 x
  simp only [Equiv.symm_trans_apply, Equiv.sumCongr_symm, Equiv.symm_symm,
    Equiv.sumCongr_apply, Equiv.trans_apply]

lemma union_apply_left {α : Type} {X X' Y Y' : Set α} {e₁ : X ≃ Y} {e₂ : X' ≃ Y'}
    {h₁ : Disjoint X X'} {h₂ : Disjoint Y Y'} {x : α} (hx : x ∈ X) :
    (union e₁ e₂ h₁ h₂ ⟨x, Set.subset_union_left hx⟩).val = (e₁ ⟨x, hx⟩).val := by
  simp only [union, Equiv.trans_apply, Equiv.sumCongr_apply]
  conv => arg 1; arg 1; arg 2; arg 3; exact Equiv.Set.union_apply_left _ hx
  simp only [Sum.map_inl, Equiv.Set.union_symm_apply_left, Set.subset_union_left, Set.coe_inclusion]

lemma union_apply_right {α : Type} {X X' Y Y' : Set α} {e₁ : X ≃ Y} {e₂ : X' ≃ Y'}
    {h₁ : Disjoint X X'} {h₂ : Disjoint Y Y'} {x : α} (hx : x ∈ X') :
    (union e₁ e₂ h₁ h₂ ⟨x, Set.subset_union_right hx⟩).val = (e₂ ⟨x, hx⟩).val := by
  simp only [union, Equiv.trans_apply, Equiv.sumCongr_apply]
  conv => arg 1; arg 1; arg 2; arg 3; exact Equiv.Set.union_apply_right _ hx
  simp only [Sum.map_inr, Equiv.Set.union_symm_apply_right, Set.subset_union_right,
    Set.coe_inclusion]

lemma union_symm_apply_left {α : Type} {X X' Y Y' : Set α} {e₁ : X ≃ Y} {e₂ : X' ≃ Y'}
    {h₁ : Disjoint X X'} {h₂ : Disjoint Y Y'} {y : α} (hy : y ∈ Y) :
    ((union e₁ e₂ h₁ h₂).symm ⟨y, Set.subset_union_left hy⟩).val = (e₁.symm ⟨y, hy⟩).val := by
  rw [union_symm, union_apply_left]

lemma union_symm_apply_right {α : Type} {X X' Y Y' : Set α} {e₁ : X ≃ Y} {e₂ : X' ≃ Y'}
    {h₁ : Disjoint X X'} {h₂ : Disjoint Y Y'} {y : α} (hy : y ∈ Y') :
    ((union e₁ e₂ h₁ h₂).symm ⟨y, Set.subset_union_right hy⟩).val = (e₂.symm ⟨y, hy⟩).val := by
  rw [union_symm, union_apply_right]

lemma mem_union_left {α : Type} {X X' Y Y' : Set α} {e₁ : X ≃ Y} {e₂ : X' ≃ Y'}
    {h₁ : Disjoint X X'} {h₂ : Disjoint Y Y'} {x}
    (hx : (union e₁ e₂ h₁ h₂ x).val ∈ Y) : x.val ∈ X := by
  have := @union_symm_apply_left _ _ _ _ _ e₁ e₂ h₁ h₂ _ hx
  simp only [Subtype.coe_eta, Equiv.symm_apply_apply] at this; rw [this]; exact Subtype.coe_prop _

lemma mem_union_right {α : Type} {X X' Y Y' : Set α} {e₁ : X ≃ Y} {e₂ : X' ≃ Y'}
    {h₁ : Disjoint X X'} {h₂ : Disjoint Y Y'} {x}
    (hx : (union e₁ e₂ h₁ h₂ x).val ∈ Y') : x.val ∈ X' := by
  have := @union_symm_apply_right _ _ _ _ _ e₁ e₂ h₁ h₂ _ hx
  simp only [Subtype.coe_eta, Equiv.symm_apply_apply] at this; rw [this]; exact Subtype.coe_prop _

lemma mem_union_symm_left {α : Type} {X X' Y Y' : Set α} {e₁ : X ≃ Y} {e₂ : X' ≃ Y'}
    {h₁ : Disjoint X X'} {h₂ : Disjoint Y Y'} {y}
    (hy : ((union e₁ e₂ h₁ h₂).symm y).val ∈ X) : y.val ∈ Y := by
  have := @union_apply_left _ _ _ _ _ e₁ e₂ h₁ h₂ _ hy
  simp only [Subtype.coe_eta, Equiv.apply_symm_apply] at this; rw [this]; exact Subtype.coe_prop _

lemma mem_union_symm_right {α : Type} {X X' Y Y' : Set α} {e₁ : X ≃ Y} {e₂ : X' ≃ Y'}
    {h₁ : Disjoint X X'} {h₂ : Disjoint Y Y'} {y}
    (hy : ((union e₁ e₂ h₁ h₂).symm y).val ∈ X') : y.val ∈ Y' := by
  have := @union_apply_right _ _ _ _ _ e₁ e₂ h₁ h₂ _ hy
  simp only [Subtype.coe_eta, Equiv.apply_symm_apply] at this; rw [this]; exact Subtype.coe_prop _

noncomputable def sigma_iUnion {α β : Type} {f : α → Set β}
    (h : ∀ x y, x ≠ y → Disjoint (f x) (f y)) :
    Sigma (fun x ↦ ↑(f x)) ≃ ↑(Set.iUnion f) := {
  toFun x := ⟨x.snd.val, Set.mem_iUnion.mpr ⟨x.fst, x.snd.property⟩⟩
  invFun x := by
    have := Set.mem_iUnion.mp x.property
    exact Sigma.mk this.choose ⟨x.val, this.choose_spec⟩
  left_inv x := by
    ext <;> simp only
    by_contra hc
    let p i := x.snd.val ∈ f i
    exact Set.disjoint_left.mp (h _ _ hc) (Exists.choose_spec (p := p) _) x.snd.property
  right_inv x := by simp only [Subtype.coe_eta]
}

noncomputable def iUnion {ι κ α : Type} {f : ι → Set α} {g : κ → Set α}
    (h₁ : ∀ x y, x ≠ y → Disjoint (f x) (f y))
    (h₂ : ∀ x y, x ≠ y → Disjoint (g x) (g y))
    (e : ι ≃ κ) (e' : (i : ι) → f i ≃ g (e i)) :
    ↑(Set.iUnion f) ≃ ↑(Set.iUnion g) :=
  (Equiv.sigma_iUnion h₁).symm.trans
    ((Equiv.sigmaCongr e e').trans (Equiv.sigma_iUnion h₂))

lemma iUnion_apply {ι κ α : Type} {f : ι → Set α} {g : κ → Set α}
    {h₁ : ∀ x y, x ≠ y → Disjoint (f x) (f y)}
    {h₂ : ∀ x y, x ≠ y → Disjoint (g x) (g y)}
    {e : ι ≃ κ} {e' : (i : ι) → f i ≃ g (e i)}
    {x : α} {i : ι} (hx : x ∈ f i) :
    (iUnion h₁ h₂ e e' ⟨x, Set.subset_iUnion _ _ hx⟩).val = (e' i ⟨x, hx⟩).val := by
  simp only [iUnion, sigma_iUnion, Equiv.sigmaCongr, Equiv.trans_apply, Equiv.coe_fn_symm_mk,
    Equiv.sigmaCongrRight_apply, Equiv.sigmaCongrLeft_apply, Equiv.coe_fn_mk]
  have h := Set.mem_iUnion.mp (Set.subset_iUnion _ _ hx)
  have : h.choose = i := by
    refine not_not.mp ((h₁ _ _).mt ?_)
    exact Set.not_disjoint_iff.mpr ⟨x, h.choose_spec, hx⟩
  subst this; rfl

def swap_fun {ι κ α : Type} {f : ι → Set α} {g : κ → Set α}
    (e : ι ≃ κ) (e' : (i : ι) → f i ≃ g (e i)) :
    (k : κ) → g k ≃ f (e.symm k) :=
  fun k ↦
    (Equiv.setCongr (by simp only [Equiv.apply_symm_apply])).trans (e' (e.symm k)).symm

lemma iUnion_symm {ι κ α : Type} {f : ι → Set α} {g : κ → Set α}
    {h₁ : ∀ x y, x ≠ y → Disjoint (f x) (f y)}
    {h₂ : ∀ x y, x ≠ y → Disjoint (g x) (g y)}
    {e : ι ≃ κ} {e' : (i : ι) → f i ≃ g (e i)} :
    (iUnion h₁ h₂ e e').symm =
    iUnion h₂ h₁ e.symm (swap_fun e e') := by
  ext1 x; unfold swap_fun
  simp only [iUnion, sigma_iUnion, Equiv.sigmaCongr, Equiv.sigmaCongrRight, Equiv.sigmaCongrLeft,
    Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk,
    Equiv.trans_apply, Equiv.setCongr_apply, Equiv.setCongr_symm_apply, Subtype.mk.injEq]
  refine congrArg _ (congrArg _ ?_)
  ext; grind only

lemma iUnion_symm_apply {ι κ α : Type} {f : ι → Set α} {g : κ → Set α}
    {h₁ : ∀ x y, x ≠ y → Disjoint (f x) (f y)}
    {h₂ : ∀ x y, x ≠ y → Disjoint (g x) (g y)}
    {e : ι ≃ κ} {e' : (i : ι) → f i ≃ g (e i)}
    {y : α} {k : κ} (hy : y ∈ g k) :
    ((iUnion h₁ h₂ e e').symm ⟨y, Set.subset_iUnion _ _ hy⟩).val =
    ((e' (e.symm k)).symm ⟨y, by simpa only [Equiv.apply_symm_apply]⟩).val := by
  rw [iUnion_symm]; refine (iUnion_apply hy).trans ?_
  simp only [swap_fun, Equiv.trans_apply, Equiv.setCongr_apply]

lemma iUnion_symm_apply' {ι κ α : Type} {f : ι → Set α} {g : κ → Set α}
    {h₁ : ∀ x y, x ≠ y → Disjoint (f x) (f y)}
    {h₂ : ∀ x y, x ≠ y → Disjoint (g x) (g y)}
    {e : ι ≃ κ} {e' : (i : ι) → f i ≃ g (e i)}
    {y : α} {i : ι} (hy : y ∈ g (e i)) :
    ((iUnion h₁ h₂ e e').symm ⟨y, Set.subset_iUnion _ _ hy⟩).val =
    ((e' i).symm ⟨y, by simpa only [Equiv.apply_symm_apply]⟩).val := by
  convert iUnion_symm_apply hy <;> symm <;> exact e.symm_apply_apply _

lemma mem_iUnion {ι κ α : Type} {f : ι → Set α} {g : κ → Set α}
    {h₁ : ∀ x y, x ≠ y → Disjoint (f x) (f y)}
    {h₂ : ∀ x y, x ≠ y → Disjoint (g x) (g y)}
    {e : ι ≃ κ} {e' : (i : ι) → f i ≃ g (e i)}
    {x : ↑(⋃ i, f i)} {k : κ} (h : (iUnion h₁ h₂ e e' x).val ∈ g k) :
    x.val ∈ f (e.symm k) := by
  have := @iUnion_symm_apply _ _ _ _ _ h₁ h₂ e e' _ _ h
  simp only [Subtype.coe_eta, Equiv.symm_apply_apply] at this
  rw [this]; exact Subtype.coe_prop _

lemma mem_iUnion_symm {ι κ α : Type} {f : ι → Set α} {g : κ → Set α}
    {h₁ : ∀ x y, x ≠ y → Disjoint (f x) (f y)}
    {h₂ : ∀ x y, x ≠ y → Disjoint (g x) (g y)}
    {e : ι ≃ κ} {e' : (i : ι) → f i ≃ g (e i)}
    {y : ↑(⋃ k, g k)} {i : ι} (h : ((iUnion h₁ h₂ e e').symm y).val ∈ f i) :
    y.val ∈ g (e i) := by
  have := @iUnion_apply _ _ _ _ _ h₁ h₂ e e' _ _ h
  simp only [Subtype.coe_eta, Equiv.apply_symm_apply] at this
  rw [this]; exact Subtype.coe_prop _

end Equiv
