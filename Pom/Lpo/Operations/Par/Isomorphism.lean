import Pom.Lpo.Isomorphism
import Pom.Lpo.Operations.Par
import Pom.Lpo.Operations.Seq.Equiv

namespace Lpo

namespace Equiv

noncomputable def par {x y : Node} {X X' Y Y' : Set Node} (e₁ : X ≃ Y) (e₂ : X' ≃ Y')
    (hx : x ∉ X) (hx' : x ∉ X') (hd : Disjoint X X')
    (hy : y ∉ Y) (hy' : y ∉ Y') (hd' : Disjoint Y Y') :
    ↑(Set.insert x (X ∪ X')) ≃ ↑(Set.insert y (Y ∪ Y')) :=
  (Equiv.singleton x y).union (e₁.union e₂ hd hd')
    (by refine Set.disjoint_left.mpr ?_; rintro x rfl (h | h) <;> contradiction)
    (by refine Set.disjoint_left.mpr ?_; rintro x rfl (h | h) <;> contradiction)

lemma root_eq_par_symm {x y : Node} {X X' Y Y' : Set Node} {e₁ : X ≃ Y} {e₂ : X' ≃ Y'}
    {hx : x ∉ X} {hx' : x ∉ X'} {hd : Disjoint X X'}
    {hy : y ∉ Y} {hy' : y ∉ Y'} {hd' : Disjoint Y Y'}
    {z : Node} {hz : z ∈ Set.insert y (Y ∪ Y')}
    (heq : x = ((Equiv.par e₁ e₂ hx hx' hd hy hy' hd').symm ⟨z, hz⟩)) :
    y = z := by
  suffices h : Subtype.mk y (Set.mem_insert _ _) = ⟨z, hz⟩ from congrArg Subtype.val h
  refine (Equiv.par e₁ e₂ hx hx' hd hy hy' hd').symm.injective ?_
  ext; refine Eq.trans ?_ heq
  conv => lhs; exact Equiv.union_symm_apply_left (Set.mem_singleton _)
  rfl

end Equiv

section ParPermute

lemma par_form₁ {φ : Form Node} {x y : Node} (hφ : Form.literal x ≤ φ ∧ φ.DependsOn {x}) :
    Form.literal y ≤ φ.permute (Equiv.singleton x y) ∧
    (φ.permute (Equiv.singleton x y)).DependsOn {y} := by
  constructor
  · intro v hy; apply hφ.1; exact ⟨⟨y, Set.mem_singleton y⟩, rfl, hy⟩
  · intro v v' hd
    apply hφ.2
    refine Set.disjoint_left.mpr ?_
    intro z hz hz'
    simp only [Set.mem_singleton_iff] at hz'
    subst z
    apply Set.disjoint_left.mp hd ?_ (Set.mem_singleton y)
    have himg : x ∈ Form.image (symmDiff v v') (Equiv.singleton x y).symm := by
      rw [← Form.image_symmDiff]
      exact hz
    obtain ⟨w, _, hmem⟩ := himg
    simpa only [Set.mem_singleton_iff.mp w.property] using hmem

lemma par_form₂ {φ : Form Node} {x y : Node} (hφ : (Form.literal x).not ≤ φ ∧ φ.DependsOn {x}) :
    (Form.literal y).not ≤ φ.permute (Equiv.singleton x y) ∧
    (φ.permute (Equiv.singleton x y)).DependsOn {y} := by
  constructor
  · intro v hy; apply hφ.1; intro hx
    obtain ⟨w, _, hmem⟩ := hx
    exact hy (Set.mem_singleton_iff.mp w.property ▸ hmem)
  · intro v v' hd
    apply hφ.2
    refine Set.disjoint_left.mpr ?_
    intro z hz hz'
    simp only [Set.mem_singleton_iff] at hz'
    subst z
    apply Set.disjoint_left.mp hd ?_ (Set.mem_singleton y)
    have himg : x ∈ Form.image (symmDiff v v') (Equiv.singleton x y).symm := by
      rw [← Form.image_symmDiff]
      exact hz
    obtain ⟨w, _, hmem⟩ := himg
    simpa only [Set.mem_singleton_iff.mp w.property] using hmem

variable {l : Type} [Bot l] {x : Node} {ℓ : l} {α β : Lpo l}
    {φ₁ φ₂ : Form Node}
    {hx : x ∉ α.nodes} {hx' : x ∉ β.nodes}
    {hd : Disjoint α.nodes β.nodes}
    {hroot : ℓ ≠ ⊥}
    {hφ₁ : Form.literal x ≤ φ₁ ∧ φ₁.DependsOn {x}}
    {hφ₂ : (Form.literal x).not ≤ φ₂ ∧ φ₂.DependsOn {x}}
    {X Y : Set Node} {y : Node}
    (hy : y ∉ X) (hy' : y ∉ Y) (hd' : Disjoint X Y)
    (e₁ : α.nodes ≃ X) (e₂ : β.nodes ≃ Y)

lemma par_permute_rel :
    ((par_gen hx hx' hd hroot hφ₁ hφ₂).permute (Equiv.par e₁ e₂ hx hx' hd hy hy' hd')).rel =
    (par_gen (α := α.permute e₁) (β := β.permute e₂)
      hy hy' hd' hroot (par_form₁ hφ₁) (par_form₂ hφ₂)).rel := by
  ext u v; constructor
  · rintro ⟨hu, _, ⟨heq, hv⟩ | hrel | hrel⟩
    · left; constructor
      · exact Equiv.root_eq_par_symm heq
      · exact Equiv.mem_union_symm_right hv
    · right; left; have ⟨hu, hv⟩ := α.property.rel_dom hrel
      have hu' : _ ∈ α.nodes ∪ β.nodes := Or.inl hu
      have hv' : _ ∈ α.nodes ∪ β.nodes := Or.inl hv
      conv at hu =>
        rhs; exact Equiv.union_symm_apply_right <| Equiv.mem_union_symm_right hu'
      conv at hv =>
        rhs; exact Equiv.union_symm_apply_right <| Equiv.mem_union_symm_right hv'
      conv at hrel =>
        arg 2; exact Equiv.union_symm_apply_right <| Equiv.mem_union_symm_right hu'
      conv at hrel =>
        arg 3; exact Equiv.union_symm_apply_right <| Equiv.mem_union_symm_right hv'
      have hu' := Equiv.mem_union_symm_left hu; have hv' := Equiv.mem_union_symm_left hv
      conv at hrel => arg 2; exact Equiv.union_symm_apply_left hu'
      conv at hrel => arg 3; exact Equiv.union_symm_apply_left hv'
      exact ⟨hu', hv', hrel⟩
    · right; right; have ⟨hu, hv⟩ := β.property.rel_dom hrel
      have hu' : _ ∈ α.nodes ∪ β.nodes := Or.inr hu
      have hv' : _ ∈ α.nodes ∪ β.nodes := Or.inr hv
      conv at hu =>
        rhs; exact Equiv.union_symm_apply_right <| Equiv.mem_union_symm_right hu'
      conv at hv =>
        rhs; exact Equiv.union_symm_apply_right <| Equiv.mem_union_symm_right hv'
      conv at hrel =>
        arg 2; exact Equiv.union_symm_apply_right <| Equiv.mem_union_symm_right hu'
      conv at hrel =>
        arg 3; exact Equiv.union_symm_apply_right <| Equiv.mem_union_symm_right hv'
      have hu' := Equiv.mem_union_symm_right hu; have hv' := Equiv.mem_union_symm_right hv
      conv at hrel => arg 2; exact Equiv.union_symm_apply_right hu'
      conv at hrel => arg 3; exact Equiv.union_symm_apply_right hv'
      exact ⟨hu', hv', hrel⟩
  · rintro (⟨rfl, hv⟩ | ⟨hu, hv, hrel⟩ | ⟨hu, hv, hrel⟩)
    · refine ⟨Set.mem_insert _ _, ?_, ?_⟩
      · right; exact hv
      · left; constructor
        · conv => rhs; exact Equiv.union_symm_apply_left (Set.mem_singleton _)
          rfl
        · conv => rhs; exact Equiv.union_symm_apply_right hv
          exact Subtype.coe_prop _
    · refine ⟨Or.inr <| Or.inl hu, Or.inr <| Or.inl hv, ?_⟩
      right; left
      have hu' : u ∈ X ∪ Y := Or.inl hu
      have hv' : v ∈ X ∪ Y := Or.inl hv
      conv =>
        arg 2; exact (Equiv.union_symm_apply_right hu').trans <| Equiv.union_symm_apply_left hu
      conv =>
        arg 3; exact (Equiv.union_symm_apply_right hv').trans <| Equiv.union_symm_apply_left hv
      exact hrel
    · refine ⟨Or.inr <| Or.inr hu, Or.inr <| Or.inr hv, ?_⟩
      right; right
      have hu' : u ∈ X ∪ Y := Or.inr hu
      have hv' : v ∈ X ∪ Y := Or.inr hv
      conv =>
        arg 2; exact (Equiv.union_symm_apply_right hu').trans <| Equiv.union_symm_apply_right hu
      conv =>
        arg 3; exact (Equiv.union_symm_apply_right hv').trans <| Equiv.union_symm_apply_right hv
      exact hrel

lemma par_permute_lab :
    ((par_gen hx hx' hd hroot hφ₁ hφ₂).permute (Equiv.par e₁ e₂ hx hx' hd hy hy' hd')).lab =
    (par_gen (α := α.permute e₁) (β := β.permute e₂)
      hy hy' hd' hroot (par_form₁ hφ₁) (par_form₂ hφ₂)).lab := by
  ext z; by_cases hz : z ∈ Set.insert y (X ∪ Y)
  · conv => lhs; exact dif_pos hz
    classical
    refine dite_congr ?_ (fun _ ↦ rfl) (fun hne ↦ ?_)
    · ext; constructor
      · exact Equiv.root_eq_par_symm
      · rintro rfl
        conv => rhs; exact Equiv.union_symm_apply_left (Set.mem_singleton _)
        rfl
    · have hz := Set.mem_of_mem_insert_of_ne hz (Ne.symm hne)
      refine if_congr ?_ ?_ ?_
      · conv => lhs; rhs; exact Equiv.union_symm_apply_right hz
        constructor
        · exact Equiv.mem_union_symm_left
        · intro hz; conv => rhs; exact Equiv.union_symm_apply_left hz
          exact Subtype.coe_prop _
      · conv => lhs; arg 2; exact Equiv.union_symm_apply_right hz
        rcases hz with hz | hz
        · conv => lhs; arg 2; exact Equiv.union_symm_apply_left hz
          symm; exact dif_pos hz
        · conv => rhs; exact dif_neg (Set.disjoint_right.mp hd' hz)
          refine α.property.lab_dom _ (Set.disjoint_right.mp hd ?_)
          conv => rhs; exact Equiv.union_symm_apply_right hz
          exact Subtype.coe_prop _
      · conv => lhs; arg 2; exact Equiv.union_symm_apply_right hz
        rcases hz with hz | hz
        · conv => rhs; exact dif_neg (Set.disjoint_left.mp hd' hz)
          refine β.property.lab_dom _ (Set.disjoint_left.mp hd ?_)
          conv => rhs; exact Equiv.union_symm_apply_left hz
          exact Subtype.coe_prop _
        · conv => lhs; arg 2; exact Equiv.union_symm_apply_right hz
          symm; exact dif_pos hz
  · conv => lhs; exact dif_neg hz
    symm; exact (par_gen _ _ _ _ _ _).property.lab_dom _ hz

lemma and_congr_with_h {P P' Q Q' : Prop}
    (h : P ↔ P') (h' : P → P' → (Q ↔ Q')) : P ∧ Q ↔ P' ∧ Q' := by
  have := iff_iff_eq.mp h; subst this
  exact and_congr_right (fun p ↦ h' p p)

lemma par_permute_form :
    ((par_gen hx hx' hd hroot hφ₁ hφ₂).permute (Equiv.par e₁ e₂ hx hx' hd hy hy' hd')).form =
    (par_gen (α := α.permute e₁) (β := β.permute e₂)
      hy hy' hd' hroot (par_form₁ hφ₁) (par_form₂ hφ₂)).form := by
  ext z v; by_cases hz : z ∈ Set.insert y (X ∪ Y)
  · refine (exists_prop_of_true hz).trans ?_
    refine or_congr ?_ (or_congr ?_ ?_)
    · constructor
      · exact Equiv.root_eq_par_symm
      · rintro rfl; conv => rhs; exact Equiv.union_symm_apply_left (Set.mem_singleton y)
        rfl
    · refine and_congr_with_h ?_ ?_
      · constructor
        · intro h; have := Equiv.mem_union_symm_right <| Set.mem_union_left _ h
          conv at h => rhs; exact Equiv.union_symm_apply_right this
          exact Equiv.mem_union_symm_left h
        · intro h;
          conv => rhs; exact Equiv.union_symm_apply_right (Set.mem_union_left _ h)
          conv => rhs; exact Equiv.union_symm_apply_left h
          exact Subtype.coe_prop _
      · intro h h'; refine and_congr ?_ ?_
        · refine Iff.trans ?_ (exists_prop_of_true h').symm
          conv => lhs; arg 2; exact Equiv.union_symm_apply_right (Set.mem_union_left _ h')
          conv => lhs; arg 2; exact Equiv.union_symm_apply_left h'
          refine iff_iff_eq.mpr <| (α.property.form _ (Subtype.coe_prop _)).1 _ _ ?_
          refine Set.disjoint_left.mpr ?_; intro w hsd hrel
          have hw := (α.property.rel_dom hrel).1; clear hrel
          rcases Set.mem_symmDiff.mp hsd with ⟨⟨⟨u, hu⟩, rfl, hv⟩, h'⟩ | ⟨⟨⟨u, hu⟩, rfl, hv⟩, h'⟩
          · simp only [Form.image, Subtype.exists, exists_and_right, Set.mem_setOf_eq, not_exists,
              not_and, forall_exists_index] at h'
            have := Equiv.mem_union_symm_right <| Set.mem_union_left _ hw
            conv at hw => rhs; exact Equiv.union_symm_apply_right this
            have hu := Equiv.mem_union_symm_left hw
            refine h' _ hu ?_ hv
            symm; conv => lhs; exact Equiv.union_symm_apply_right this
            exact Equiv.union_symm_apply_left hu
          · simp only [Form.image, Subtype.exists, exists_and_right, Set.mem_setOf_eq, not_exists,
              not_and, forall_exists_index] at h'
            refine h' u (Or.inr (Or.inl hu)) ?_ hv
            conv => lhs; exact Equiv.union_symm_apply_right <| Set.mem_union_left _ hu
            exact Equiv.union_symm_apply_left hu
        · refine iff_iff_eq.mpr <| hφ₁.2 _ _ ?_
          refine Set.disjoint_left.mpr ?_; rintro x hsd rfl
          rcases Set.mem_symmDiff.mp hsd with ⟨⟨⟨u, hu⟩, heq, hv⟩, h'⟩ | ⟨⟨⟨u, rfl⟩, heq, hv⟩, h'⟩
          · simp only [Form.image, Subtype.exists, exists_and_right, Set.mem_setOf_eq, not_exists,
              not_and, forall_exists_index] at h'
            obtain rfl := Equiv.root_eq_par_symm heq.symm
            exact h' _ (Set.mem_singleton _) rfl hv
          · simp only [Form.image, Subtype.exists, exists_and_right, Set.mem_setOf_eq, not_exists,
              not_and, forall_exists_index] at h'
            refine h' _ (Set.mem_insert _ _) ?_ hv
            conv => rhs; exact heq.symm
            exact Equiv.union_symm_apply_left (Set.mem_singleton _)
    · refine and_congr_with_h ?_ ?_
      · constructor
        · intro h; have := Equiv.mem_union_symm_right <| Set.mem_union_right _ h
          conv at h => rhs; exact Equiv.union_symm_apply_right this
          exact Equiv.mem_union_symm_right h
        · intro h;
          conv => rhs; exact Equiv.union_symm_apply_right (Set.mem_union_right _ h)
          conv => rhs; exact Equiv.union_symm_apply_right h
          exact Subtype.coe_prop _
      · intro h h'; refine and_congr ?_ ?_
        · refine Iff.trans ?_ (exists_prop_of_true h').symm
          conv => lhs; arg 2; exact Equiv.union_symm_apply_right (Set.mem_union_right _ h')
          conv => lhs; arg 2; exact Equiv.union_symm_apply_right h'
          refine iff_iff_eq.mpr <| (β.property.form _ (Subtype.coe_prop _)).1 _ _ ?_
          refine Set.disjoint_left.mpr ?_; intro w hsd hrel
          have hw := (β.property.rel_dom hrel).1; clear hrel
          rcases Set.mem_symmDiff.mp hsd with ⟨⟨⟨u, hu⟩, rfl, hv⟩, h'⟩ | ⟨⟨⟨u, hu⟩, rfl, hv⟩, h'⟩
          · simp only [Form.image, Subtype.exists, exists_and_right, Set.mem_setOf_eq, not_exists,
              not_and, forall_exists_index] at h'
            have := Equiv.mem_union_symm_right <| Set.mem_union_right _ hw
            conv at hw => rhs; exact Equiv.union_symm_apply_right this
            have hu := Equiv.mem_union_symm_right hw
            refine h' _ hu ?_ hv
            symm; conv => lhs; exact Equiv.union_symm_apply_right this
            exact Equiv.union_symm_apply_right hu
          · simp only [Form.image, Subtype.exists, exists_and_right, Set.mem_setOf_eq, not_exists,
              not_and, forall_exists_index] at h'
            refine h' u (Or.inr (Or.inr hu)) ?_ hv
            conv => lhs; exact Equiv.union_symm_apply_right <| Set.mem_union_right _ hu
            exact Equiv.union_symm_apply_right hu
        · refine iff_iff_eq.mpr <| hφ₂.2 _ _ ?_
          refine Set.disjoint_left.mpr ?_; rintro x hsd rfl
          rcases Set.mem_symmDiff.mp hsd with ⟨⟨⟨u, hu⟩, heq, hv⟩, h'⟩ | ⟨⟨⟨u, rfl⟩, heq, hv⟩, h'⟩
          · simp only [Form.image, Subtype.exists, exists_and_right, Set.mem_setOf_eq, not_exists,
              not_and, forall_exists_index] at h'
            obtain rfl := Equiv.root_eq_par_symm heq.symm
            exact h' _ (Set.mem_singleton _) rfl hv
          · simp only [Form.image, Subtype.exists, exists_and_right, Set.mem_setOf_eq, not_exists,
              not_and, forall_exists_index] at h'
            refine h' _ (Set.mem_insert _ _) ?_ hv
            conv => rhs; exact heq.symm
            exact Equiv.union_symm_apply_left (Set.mem_singleton _)
  · constructor
    · intro ⟨hc, _⟩; contradiction
    · rintro (rfl | ⟨hc, _⟩ | ⟨hc, _⟩) <;> exfalso <;> apply hz
      · exact Set.mem_insert _ _
      · right; left; exact hc
      · right; right; exact hc

lemma par_permute :
    (par_gen hx hx' hd hroot hφ₁ hφ₂).permute (Equiv.par e₁ e₂ hx hx' hd hy hy' hd') =
    par_gen (α := α.permute e₁) (β := β.permute e₂)
      hy hy' hd' hroot (par_form₁ hφ₁) (par_form₂ hφ₂) := by
  ext1
  · rfl
  · exact par_permute_rel _ _ _ _ _
  · exact par_permute_lab _ _ _ _ _
  · exact par_permute_form _ _ _ _ _

end ParPermute

lemma par_isomorphic {l : Type} [Bot l] {x y : Node} {ℓ : l} {α α' β β' : Lpo l}
    {hx : x ∉ α.nodes} {hx' : x ∉ β.nodes}
    {hy : y ∉ α'.nodes} {hy' : y ∉ β'.nodes}
    {hd : Disjoint α.nodes β.nodes}
    {hd' : Disjoint α'.nodes β'.nodes}
    {hroot : ℓ ≠ ⊥}
    (hα : α ≈ α') (hβ : β ≈ β') :
    par hx hx' hd hroot ≈ par hy hy' hd' hroot := by
  have ⟨e₁, hα⟩ := hα
  have ⟨e₂, hβ⟩ := hβ
  refine ⟨Equiv.par e₁ e₂ hx hx' hd hy hy' hd', ?_⟩
  conv => lhs; exact par_permute hy hy' hd' e₁ e₂
  congr

end Lpo
