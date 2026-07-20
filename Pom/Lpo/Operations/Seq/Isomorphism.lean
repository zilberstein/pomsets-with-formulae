import Pom.Lpo.Operations.Seq

namespace Lpofin

variable {l : Type} [PartialOrder l] [OrderBot l]

lemma branches_permute {α α' : Lpofin l} {e : α.nodes ≃ α'.nodes}
    (h : α.permute e = α') :
    ∀ φ ∈ α.branches, φ.permute e ∈ α'.branches := by
  intro φ hφ
  obtain ⟨s, ⟨hne, hsub, ⟨v, hsat⟩, hstk, hmax⟩, rfl⟩ := (Set.Finite.mem_toFinset _).mp hφ
  let t := s.attach.image
    (fun x : ↑s ↦ (e ⟨x.val, extens_subset_nodes _ (hsub x.property)⟩).val)
  refine (Set.Finite.mem_toFinset _).mpr ⟨t, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> subst t
  · refine Finset.Nonempty.image (Finset.univ_nonempty_iff.mpr ?_) _
    exact hne.coe_sort
  · conv => rhs; rw [← h]
    intro x hx; obtain ⟨⟨y, hy⟩, _, rfl⟩ := Finset.mem_image.mp hx
    simp only [extens, Finset.mem_filter]; constructor
    · refine (Set.Finite.mem_toFinset _).mpr ?_; exact Subtype.coe_prop _
    · intro hc
      have := hsub hy
      simp only [extens, Finset.mem_filter] at this; have ⟨hy', h'⟩ := this; apply h'
      have hy' := (Set.Finite.mem_toFinset _).mp hy'; intro v hform
      have ⟨⟨z, hz, hbot⟩, _, hform'⟩ :=
        hc (Form.image v e) ((Lpo.permute_form_sat_iff hy').mp hform)
      refine ⟨⟨(e.symm ⟨_, hz⟩).val, Subtype.coe_prop _, ?_⟩, ?_⟩
      · refine Eq.trans ?_ hbot; exact (if_pos hz).symm
      · refine (Lpo.permute_form_sat_iff (Subtype.coe_prop _) (e := e)).mpr ?_
        conv => arg 2; arg 1; exact e.apply_symm_apply _
        exact ⟨hz, hform'⟩
  · use Form.image v e; intro ⟨x, hx⟩; obtain ⟨⟨y, hy⟩, _, rfl⟩ := Finset.mem_image.mp hx
    conv => simp only; arg 1; exact h.symm
    refine (Lpo.permute_form_sat_iff _).mp (hsat ⟨_, hy⟩)
  · intro v hv ⟨⟨z, hz, hbot⟩, hform⟩
    refine hstk (Form.image v e.symm) ?_ ?_
    · intro ⟨x, hx⟩; refine ((Lpo.permute_form_sat_iff ?_ (e := e)).mpr ?_)
      · exact extens_subset_nodes _ (hsub hx)
      · conv => arg 3; arg 2; exact e.symm_symm.symm
        conv => arg 3; exact Form.image_inv v e.symm
        refine Lpo.form_inter_nodes_sat_iff.mp ?_
        conv at hv => arg 1; exact h.symm
        refine hv ⟨(e ⟨x, _⟩).val, ?_⟩
        exact Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩
    · refine ⟨⟨(e.symm ⟨z, hz⟩).val, Subtype.coe_prop _, ?_⟩, ?_⟩
      · rw [← h] at hbot; simp only [Lpo.lab, permute, Lpo.permute, dite_eq_right_iff] at hbot
        exact hbot hz
      · simp only
        refine (Lpo.permute_form_sat_iff (Subtype.coe_prop _) (e := e)).mpr ?_
        conv => arg 3; exact Form.image_inv v e.symm
        refine Lpo.form_inter_nodes_sat_iff.mp ?_
        conv => arg 2; simp only [Subtype.coe_eta]; arg 1; exact e.apply_symm_apply _
        conv at hform => simp only; arg 1; exact h.symm
        exact hform
  · intro t ⟨hst, hnts⟩ hex ⟨v, hform⟩
    refine hmax (t.attach.image fun y ↦ (e.symm ⟨y.val, ?_⟩).val) ?_ ?_ ?_
    · exact extens_subset_nodes _ (hex y.property)
    · constructor
      · intro x hx; refine Finset.mem_image.mpr ⟨⟨e ⟨x, ?_⟩, ?_⟩, Finset.mem_attach _ _, ?_⟩
        · exact extens_subset_nodes _ (hsub hx)
        · exact hst (Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩)
        · simp only [Subtype.coe_eta, Equiv.symm_apply_apply]
      · intro hc; apply hnts; intro x hx
        refine Finset.mem_image.mpr ⟨⟨(e.symm ⟨x, ?_⟩).val, ?_⟩, Finset.mem_attach _ _, ?_⟩
        · exact extens_subset_nodes _ (hex hx)
        · exact hc (Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩)
        · simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
    · intro x hx; simp only [extens, Finset.mem_image, Finset.mem_attach, true_and, Finset.mem_filter] at *
      obtain ⟨y, rfl⟩ := hx; constructor
      · exact (Set.Finite.mem_toFinset _).mpr (Subtype.coe_prop _)
      · intro hc; have := hex y.property
        simp only [extens, nodes_finset, Finset.mem_filter, Set.Finite.mem_toFinset] at this
        apply this.2; intro v hform
        rw [← h] at hform; simp only [Lpofin.permute, form, Lpo.permute, Lpo.form] at hform
        have ⟨hy, hform⟩ := hform
        have ⟨⟨z, hz, hbot⟩, hform⟩ := hc _ hform
        refine ⟨⟨(e ⟨_, hz⟩).val, Subtype.coe_prop _, ?_⟩, ?_⟩
        · conv => arg 1; arg 1; arg 1; exact h.symm
          simp only [Lpofin.permute, Lpo.permute, Lpo.lab]
          refine (dif_pos (Subtype.coe_prop _)).trans ?_
          conv => lhs; arg 2; simp only [Subtype.coe_eta]; arg 1; exact e.symm_apply_apply _
          exact hbot
        · simp only [← h]
          refine Lpo.form_inter_nodes_sat_iff.mpr ?_
          conv => arg 3; exact (Form.image_inv _ e.symm).symm
          conv => arg 3; arg 2; exact e.symm_symm
          exact (Lpo.permute_form_sat_iff _).mp hform
    · refine ⟨Form.image v e.symm, ?_⟩; intro x hx
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
      refine (Lpo.permute_form_sat_iff (Subtype.coe_prop _) (e := e)).mpr ?_
      conv => arg 2; simp only [Subtype.coe_eta]; arg 1; exact e.apply_symm_apply _
      conv => arg 3; exact Form.image_inv _ _
      refine Lpo.form_inter_nodes_sat_iff.mp ?_
      have := hform _ y.property; rw [← h] at this; exact this
  · conv => lhs; arg 1; rw [← h]
    simp only [conj]; unfold Form.permute; ext v; constructor
    · intro hform x
      have :=
        hform
          ⟨(e ⟨x.val, extens_subset_nodes _ (hsub x.property)⟩).val,
            Finset.mem_image.mpr ⟨x, Finset.mem_attach _ _, rfl⟩⟩
      simp only [form, Lpo.form, permute, Lpo.permute, Form.permute, Subtype.coe_eta,
        Subtype.coe_prop, exists_const] at this
      conv at this => arg 2; arg 1; exact Equiv.symm_apply_apply _ _
      exact this
    · intro hform x
      have ⟨y, _, heq⟩ := Finset.mem_image.mp x.property; rw [← heq]
      have := hform y
      simp only [form, Lpo.form, permute, Lpo.permute, Form.permute, Subtype.coe_eta,
        Subtype.coe_prop, exists_const]
      conv => arg 2; arg 1; exact Equiv.symm_apply_apply _ _
      exact this

def branches_equiv {α α' : Lpofin l} {e : α.nodes ≃ α'.nodes}
    (h : α.permute e = α') :
    α.branches ≃ α'.branches := {
  toFun φ := ⟨φ.val.permute e, branches_permute h _ φ.property⟩
  invFun φ := ⟨φ.val.permute e.symm, by {
    refine branches_permute ?_ _ φ.property
    refine Subtype.ext ?_; symm; refine (Lpo.permute_symm ?_)
    conv => rhs; arg 1; exact h.symm
    rfl
  }⟩
  left_inv := by
    intro ⟨φ, hφ⟩
    unfold Form.permute; ext1; ext1 v; simp only [Equiv.symm_symm, Form.image]
    obtain ⟨s, ⟨_, hsub, _⟩, rfl⟩:= (Set.Finite.mem_toFinset _).mp hφ
    have h (x : ↑s) := (α.val.property.form _ (extens_subset_nodes _ (hsub x.property))).1
    refine Form.DependsOn.sAnd h _ _ ?_
    refine Set.disjoint_left.mpr ?_; intro x hx hx'
    have ⟨y, hrel⟩ := Set.mem_iUnion.mp hx'
    rcases Set.mem_symmDiff.mp hx with ⟨⟨z, rfl, w, heq, hw⟩, hv⟩ | ⟨hv, h⟩
    · apply hv; rw [← Subtype.val_injective heq]; simpa only [Equiv.symm_apply_apply]
    · have hx := (α.val.property.rel_dom hrel).1
      refine h ⟨e ⟨x, hx⟩, ?_, ⟨x, hx⟩, rfl, hv⟩
      simp only [Equiv.symm_apply_apply]
  right_inv := by
    intro ⟨φ, hφ⟩
    unfold Form.permute; ext1; ext1 v; simp only [Form.image, Equiv.symm_symm, Subtype.exists,
      exists_and_right, Set.mem_setOf_eq, ↓existsAndEq, Subtype.coe_eta, Equiv.apply_symm_apply,
      Subtype.coe_prop, exists_const, true_and, exists_prop]
    obtain ⟨s, ⟨_, hsub, _⟩, rfl⟩:= (Set.Finite.mem_toFinset _).mp hφ
    have h (x : ↑s) := (α'.val.property.form _ (extens_subset_nodes _ (hsub x.property))).1
    refine Form.DependsOn.sAnd h _ _ ?_
    refine Set.disjoint_left.mpr ?_; intro x hx hx'
    have ⟨y, hrel⟩ := Set.mem_iUnion.mp hx'
    rcases Set.mem_symmDiff.mp hx with ⟨⟨_, h⟩, h'⟩ | ⟨hv, h⟩
    · exact h' h
    · refine h ⟨⟨?_, True.intro⟩, hv⟩; exact (α'.val.property.rel_dom hrel).1
}

lemma seq_isomorphic {α α' β β' : Lpofin l} {f : CopyFn α β} {g : CopyFn α' β'}
    (hα : α ≈ α') (hβ : β ≈ β') : seq α β f ≈ seq α' β' g := by
  have ⟨e, he⟩ := hα
  have eb := branches_equiv (Subtype.ext he)
  have (φ : ↑α.branches) :
      ∃ e : ((f φ).nodes ≃ (g (eb φ)).nodes), (f φ).permute e = (g (eb φ)) := by
    have ⟨ef, hf⟩ := (f.property φ).1
    have ⟨eg, hg⟩ := (g.property (eb φ)).1
    have ⟨eβ, h⟩ := hβ
    refine ⟨ef.trans (eβ.trans eg.symm), ?_⟩
    unfold Lpofin.permute; refine Subtype.ext ?_; simp only
    refine Lpo.permute_trans.symm.trans ?_
    refine Lpo.permute_trans.symm.trans ?_
    symm; refine Lpo.permute_symm (hg.trans (h.symm.trans ?_))
    refine Lpo.permute_congr _ _ hf.symm ?_
    intro x; rfl
  choose eφ h using this
  let e' := Equiv.iUnion
    (fun φ ↦ (f.property φ).2.2)
    (fun φ ↦ (g.property φ).2.2)
    eb eφ
  refine ⟨Equiv.union e e' ?_ ?_ , ?_⟩
  · refine Set.disjoint_left.mpr ?_; intro x hx hx'
    have ⟨φ, hx'⟩ := Set.mem_iUnion.mp hx'
    exact Set.disjoint_left.mp (f.property φ).2.1 hx hx'
  · refine Set.disjoint_left.mpr ?_; intro x hx hx'
    have ⟨φ, hx'⟩ := Set.mem_iUnion.mp hx'
    exact Set.disjoint_left.mp (g.property φ).2.1 hx hx'
  · ext1
    · rfl
    · ext x y
      by_cases hx : x ∈ (α'.seq β' g).nodes
      · by_cases hy : y ∈ (α'.seq β' g).nodes
        · simp only [seq, seq_base, Lpo.permute, Lpo.nodes, Lpo.rel]
          unfold Rel.permute
          refine Iff.trans ⟨fun h ↦ h.2.2, fun h ↦ ⟨hx, hy, h⟩⟩ ?_
          refine or_congr ?_ ?_
          · unfold Lpofin.rel; rw [← he]
            simp only [Lpo.permute, Lpo.rel, Rel.permute]
            constructor
            · intro hrel; have ⟨hx', hy'⟩ := (α.val.property.rel_dom hrel)
              have hx := Equiv.mem_union_symm_left hx'
              have hy := Equiv.mem_union_symm_left hy'
              refine ⟨hx, hy, ?_⟩
              rw [Equiv.union_symm_apply_left hx, Equiv.union_symm_apply_left hy] at hrel
              exact hrel
            · intro ⟨hx', hy', hrel⟩
              refine (congrArg₂ α.rel ?_ ?_).mpr hrel
              · exact Equiv.union_symm_apply_left hx'
              · exact Equiv.union_symm_apply_left hy'
          · refine eb.exists_congr ?_; intro φ
            rw [← h φ]
            simp only [Lpofin.permute, Lpo.permute, rel, Lpo.rel, nodes, Lpo.nodes, Rel.permute]
            refine or_congr ?_ ?_
            · constructor
              · intro hrel
                have ⟨hx', hy'⟩ := (f φ).val.property.rel_dom hrel
                have hx'' := Equiv.mem_union_symm_right (Set.mem_iUnion.mpr ⟨_, hx'⟩)
                have hy'' := Equiv.mem_union_symm_right (Set.mem_iUnion.mpr ⟨_, hy'⟩)
                conv at hx' => arg 2; exact Equiv.union_symm_apply_right hx''
                conv at hy' => arg 2; exact Equiv.union_symm_apply_right hy''
                unfold e' at hx'
                have hx := Equiv.mem_iUnion_symm (e := eb) hx'
                have hy := Equiv.mem_iUnion_symm (e := eb) hy'
                refine ⟨hx, hy, (congrArg₂ _ ?_ ?_).mp hrel⟩; all_goals {
                  refine (Equiv.union_symm_apply_right ?_).trans ?_
                  · assumption
                  · exact Equiv.iUnion_symm_apply' _
                }
              · intro ⟨hx', hy', hrel⟩
                refine (congrArg₂ _ ?_ ?_).mpr hrel; all_goals {
                  refine (Equiv.union_symm_apply_right ?_).trans ?_
                  · refine Set.mem_iUnion.mpr ⟨eb φ, ?_⟩; assumption
                  · exact Equiv.iUnion_symm_apply' _
                }
            · refine and_congr ?_ ?_
              · sorry
              · sorry
        · constructor
          · intro ⟨_, hy', _⟩; exfalso; exact hy hy'
          · intro hrel; exfalso; exact hy ((seq _ _ _).val.property.rel_dom hrel).2
      · constructor
        · intro ⟨hx', _⟩; exfalso; exact hx hx'
        · intro hrel; exfalso; exact hx ((seq _ _ _).val.property.rel_dom hrel).1
    · sorry
    · sorry



    --   constructor
    --   · rintro ⟨hx, hy, hrel | ⟨φ, hrel | ⟨hform, hj⟩⟩⟩
    --     · left; unfold Lpofin.rel; rw [← he]; simp only [Lpo.permute, Lpo.rel, Rel.permute]
    --       have ⟨hx', hy'⟩ := (α.val.property.rel_dom hrel)
    --       have hx := Equiv.mem_union_symm_left hx'
    --       have hy := Equiv.mem_union_symm_left hy'
    --       refine ⟨hx, hy, ?_⟩
    --       rw [Equiv.union_symm_apply_left hx, Equiv.union_symm_apply_left hy] at hrel
    --       exact hrel
    --     · right; use eb φ; left
    --       have ⟨hx', hy'⟩ := (f φ).val.property.rel_dom hrel
    --       rw [← h φ]; simp only [Lpofin.permute, rel, Lpo.permute, Lpo.rel, Rel.permute]
    --       sorry
    --     · sorry
    --   · intro h; sorry
    -- · simp only [seq, seq_base, Lpo.permute, Lpo.lab, Lpo.nodes]
    --   ext x; by_cases hx : x ∈ α'.nodes ∪ ⋃ φ, (g φ).nodes
    --   · conv => lhs; exact dif_pos hx
    --     by_cases hx' : ∃ φ, x ∈ (g φ).nodes
    --     · conv => rhs; exact dif_pos hx'
    --       have ⟨φ, hx'⟩ := hx'
    --       refine (dif_pos ?_).trans ?_
    --       · use eb.symm φ; sorry
    --       · conv => rhs; arg 1; arg 2; exact (eb.apply_symm_apply _).symm
    --         conv => rhs; arg 1; exact (h _).symm
    --         simp only [permute, lab, Lpo.permute, Lpo.lab]
    --         sorry
    --   · conv => lhs; exact dif_neg hx
    --     symm; refine (dif_neg ?_).trans ?_
    --     · intro ⟨φ, hφ⟩; apply hx; right; exact Set.mem_iUnion.mpr ⟨_, hφ⟩
    --     · refine α'.val.property.lab_dom _ ?_
    --       intro hx'; apply hx; left; exact hx'
    -- · simp only [seq, seq_base, Lpo.permute, Lpo.form, Lpo.nodes]
    --   ext x v; constructor
    --   · intro ⟨hx, hform⟩
    --     rcases hx with hx | hx
    --     · rw [if_pos hx, Lpofin.form, ← he]
    --       use hx

    --       --conv => congrFun (if_pos hx) _


end Lpofin
