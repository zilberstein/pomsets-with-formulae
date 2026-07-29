import Pom.Lpo.Operations.Seq

namespace Lpofin

variable {act test : Type} [PartialOrder act] [PartialOrder test]

lemma branches_permute {α α' : Lpofin (Label act test)} {e : α.nodes ≃ α'.nodes}
    (h : α.permute e = α') :
    ∀ φ ∈ α.branches, (h ▸ φ.permute e) ∈ α'.branches := by
  rintro φ ⟨himp, hstk, hmax⟩
  refine ⟨?_, ?_, ?_⟩ <;> sorry
  -- · rintro x ⟨x, rfl⟩; conv => lhs; rw [← h]
  --   have ⟨b, hlab⟩ := (Label.isTest_iff _).mp <| hs x.property
  --   refine (Label.isTest_iff _).mpr ⟨b, ?_⟩
  --   simp only [lab, Lpo.lab, permute, Lpo.permute, Subtype.coe_prop, ↓reduceDIte, Subtype.coe_eta]
  --   conv => lhs; arg 2; arg 1; exact e.symm_apply_apply _
  --   exact hlab
  -- · ext v; constructor
  --   · intro hform x; have := hform (eb.symm x)
  --     simp only [g, node_lit] at *; by_cases h : f (eb.symm x) = true
  --     · simp only [h, ↓reduceIte] at *
  --       have ⟨z, heq, hmem⟩ := this
  --       sorry
  --     · sorry
  --   · sorry
  -- · refine ⟨?_, ?_⟩
  --   · intro v hform y; sorry
  --   · sorry
  -- · sorry

def branches_equiv {α α' : Lpofin (Label act test)} {e : α.nodes ≃ α'.nodes}
    (h : α.permute e = α') :
    α.branches ≃ α'.branches := {
  toFun φ := ⟨h ▸ φ.val.permute e, branches_permute h _ φ.property⟩
  invFun φ := sorry
  --   ⟨φ.val.permute e.symm, by {
  --   refine branches_permute ?_ _ φ.property
  --   refine Subtype.ext ?_; symm; refine (Lpo.permute_symm ?_)
  --   conv => rhs; arg 1; exact h.symm
  --   rfl
  -- }⟩
  left_inv := by sorry
    -- rintro ⟨_, ⟨t, ht, f, rfl, _⟩⟩
    -- have h (x : ↑t) := (α.val.property.form _ (tests_sub_nodes <| ht x.property)).1
    -- ext1; ext1 v; simp only [eq_iff_iff]
    -- have hdep : (mk_form f).DependsOn α.nodes := by
    --   refine (mk_form_depends_on f).monotone _ ?_
    --   intro x hx; exact tests_sub_nodes <| ht hx
    -- rw [Form.permute_trans _ _ _ hdep, e.self_trans_symm, Form.permute_refl _ hdep]
  right_inv := by sorry
    -- rintro ⟨_, ⟨t, ht, f, rfl, _⟩⟩
    -- have h (x : ↑t) := (α'.val.property.form _ (tests_sub_nodes <| ht x.property)).1
    -- ext1; ext1 v; simp only [eq_iff_iff]
    -- have hdep : (mk_form f).DependsOn α'.nodes := by
    --   refine (mk_form_depends_on f).monotone _ ?_
    --   intro x hx; exact tests_sub_nodes <| ht hx
    -- rw [Form.permute_trans _ _ _ hdep, e.symm_trans_self, Form.permute_refl _ hdep]
    }

lemma form_imp_permute {l : Type} [Bot l]
    {a : Lpofin l} {Y : Set Node} {e : a.nodes ≃ Y} {φ : Form Node} {x : Node}
    (hx : x ∈ a.nodes) (hφ : φ.DependsOn a.nodes) :
    φ ≤ a.form x ↔ φ.permute e ≤ (a.permute e).form (e ⟨x, hx⟩).val := by
  classical
  constructor
  · intro himp v h
    apply Lpo.form_inter_nodes_sat_iff.mpr;
    conv in v ∩ _ => exact (Form.image_inv _ e.symm).symm
    rw [e.symm_symm]; exact (Lpo.permute_form_sat_iff _).mp (himp _ h)
  · intro himp v h
    apply (Lpo.permute_form_sat_iff hx (e := e)).mpr
    refine himp _ ?_; unfold Form.permute; conv => arg 1; exact Form.image_inv v e
    refine (hφ _ _ ?_).mp h; apply Set.disjoint_left.mpr fun y hy hy' ↦ ?_
    rcases Set.mem_symmDiff.mp hy with ⟨hv, hv'⟩ | ⟨hv, hv'⟩
    · exact hv' ⟨hv, hy'⟩
    · exact hv' hv.1

lemma seq_iso_rel {α α' β β' : Lpofin (Label act test)} {f : CopyFn α β} {g : CopyFn α' β'}
    {e : α.val.nodes ≃ α'.val.nodes} (he : α.val.permute e = α'.val)
    {eφ : (φ : ↥α.branches) →
      ((f φ).nodes ≃ (g (branches_equiv (Subtype.ext he) φ)).nodes)}
    (h : ∀ φ, (f φ).permute (eφ φ) = g (branches_equiv (Subtype.ext he) φ))
    (hd1 : Disjoint α.nodes (⋃ φ, (f φ).nodes))
    (hd2 : Disjoint α'.nodes (⋃ φ, (g φ).nodes)) :
    ((α.seq β f).val.permute (Equiv.union e
      (Equiv.iUnion (fun φ ↦ (f.property φ).2.2) (fun φ ↦ (g.property φ).2.2)
        (branches_equiv (Subtype.ext he)) eφ) hd1 hd2)).rel = (α'.seq β' g).val.rel := by
  let eb := branches_equiv (Subtype.ext he)
  let e' := Equiv.iUnion (fun φ ↦ (f.property φ).2.2) (fun φ ↦ (g.property φ).2.2) eb eφ
  change ((α.seq β f).val.permute (Equiv.union e e' hd1 hd2)).rel = (α'.seq β' g).val.rel
  · ext x y
    by_cases hx : x ∈ (α'.seq β' g).nodes
    · by_cases hy : y ∈ (α'.seq β' g).nodes
      · simp only [seq, seq_base, Lpo.permute, Lpo.nodes, Lpo.rel]
        unfold Rel.permute
        refine Iff.trans ⟨fun h ↦ h.2.2, fun h ↦ ⟨hx, hy, h⟩⟩ ?_
        refine or_congr ?_ ?_
        · unfold Lpofin.rel; conv_rhs => rw [← he]
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
            · rcases hx with hx | hx
              · conv => lhs; rhs; arg 2; exact Equiv.union_symm_apply_left hx
                refine (form_imp_permute (e := e) ?_ ?_).trans ?_
                · exact Subtype.coe_prop _
                · refine φ.val.dependsOn.monotone _ ?_
                  exact φ.val.tests_valid.trans tests_sub_nodes
                · sorry
                  -- refine forall_congr' fun v ↦ imp_congr ?_ ?_
                  -- · exact Iff.refl _
                  -- · conv => lhs; arg 2; arg 1; exact e.apply_symm_apply _
                  --   unfold form; conv => rhs; arg 1; exact he.symm
                  --   exact Iff.refl _
              · conv => lhs; rhs; arg 2; exact Equiv.union_symm_apply_right hx
                obtain ⟨_, ⟨ψ, rfl⟩, hx⟩ := hx
                conv => lhs; rhs; arg 2; exact Equiv.iUnion_symm_apply hx (e := eb)
                constructor
                · intro himp v h; exfalso
                  sorry
                  -- have := (α.val.property.form_dom _).mp ⟨_, himp _ h⟩
                  -- refine Set.disjoint_right.mp (f.property (eb.symm ψ)).2.1 ?_ this
                  -- exact Subtype.coe_prop _
                · intro himp v h; exfalso
                  refine Set.disjoint_right.mp (g.property ψ).2.1 hx ?_
                  refine (α'.val.property.form_dom _).mp ⟨Form.image v e, himp _ ?_⟩
                  simp only [branches_equiv, Equiv.coe_fn_mk, Form.permute, eb]
                  sorry
                  -- conv => arg 2; exact Form.image_inv v e
                  -- refine (branch_depends_on φ.property _ _ ?_).mp h
                  -- apply Set.disjoint_left.mpr fun y hy hy' ↦ ?_
                  -- rcases Set.mem_symmDiff.mp hy with ⟨hv, hv'⟩ | ⟨hv, hv'⟩
                  -- · exact hv' ⟨hv, hy'⟩
                  -- · exact hv' hv.1
            · constructor
              · intro h;
                have := Set.subset_iUnion (fun φ ↦ (f φ).nodes) φ h
                rw [Equiv.union_symm] at this
                have := Equiv.mem_union_right this
                conv at h => arg 2; exact Equiv.union_symm_apply_right this
                exact Equiv.mem_iUnion_symm h (e := eb)
              · intro hy
                have := Set.subset_iUnion (fun ψ ↦ (g ψ).nodes) (eb φ) hy
                conv => rhs; exact Equiv.union_symm_apply_right this
                conv => rhs; exact Equiv.iUnion_symm_apply' hy (e := eb)
                exact Subtype.coe_prop _
      · constructor
        · intro ⟨_, hy', _⟩; exfalso; exact hy hy'
        · intro hrel; exfalso; exact hy ((seq _ _ _).val.property.rel_dom hrel).2
    · constructor
      · intro ⟨hx', _⟩; exfalso; exact hx hx'
      · intro hrel; exfalso; exact hx ((seq _ _ _).val.property.rel_dom hrel).1

lemma seq_iso_lab {α α' β β' : Lpofin (Label act test)} {f : CopyFn α β} {g : CopyFn α' β'}
    {e : α.val.nodes ≃ α'.val.nodes} (he : α.val.permute e = α'.val)
    {eφ : (φ : ↥α.branches) →
      ((f φ).nodes ≃ (g (branches_equiv (Subtype.ext he) φ)).nodes)}
    (h : ∀ φ, (f φ).permute (eφ φ) = g (branches_equiv (Subtype.ext he) φ))
    (hd1 : Disjoint α.nodes (⋃ φ, (f φ).nodes))
    (hd2 : Disjoint α'.nodes (⋃ φ, (g φ).nodes)) :
    ((α.seq β f).val.permute (Equiv.union e
      (Equiv.iUnion (fun φ ↦ (f.property φ).2.2) (fun φ ↦ (g.property φ).2.2)
        (branches_equiv (Subtype.ext he)) eφ) hd1 hd2)).lab = (α'.seq β' g).val.lab := by
  let eb := branches_equiv (Subtype.ext he)
  let e' := Equiv.iUnion (fun φ ↦ (f.property φ).2.2) (fun φ ↦ (g.property φ).2.2) eb eφ
  change ((α.seq β f).val.permute (Equiv.union e e' hd1 hd2)).lab = (α'.seq β' g).val.lab
  · ext x; by_cases hx : x ∈ (α'.seq β' g).nodes
    · conv => lhs; exact dif_pos hx
      classical refine dite_congr ?_ ?_ ?_
      · apply propext
        constructor
        · rintro ⟨φ, hφ⟩
          exact Set.mem_iUnion.mp
            (Equiv.mem_union_symm_right (Set.mem_iUnion.mpr ⟨φ, hφ⟩))
        · rintro ⟨ψ, hψ⟩
          have hu : x ∈ ⋃ φ, (g φ).nodes := Set.mem_iUnion.mpr ⟨ψ, hψ⟩
          have heq := Equiv.union_symm_apply_right (e₁ := e) (e₂ := e')
            (h₁ := hd1) (h₂ := hd2) hu
          refine ⟨eb.symm ψ, ?_⟩
          have hψ' : (e' (e'.symm ⟨x, hu⟩)).val ∈ (g ψ).nodes := by
            simpa only [Equiv.apply_symm_apply] using hψ
          have hi : (e'.symm ⟨x, hu⟩).val ∈ (f (eb.symm ψ)).nodes :=
            Equiv.mem_iUnion (e := eb) hψ'
          exact heq ▸ hi
      · intro hf
        let ψ := hf.choose
        have hxg : x ∈ (g ψ).nodes := hf.choose_spec
        have hu : x ∈ ⋃ φ, (g φ).nodes := Set.mem_iUnion.mpr ⟨ψ, hxg⟩
        have hunion := Equiv.union_symm_apply_right (e₁ := e) (e₂ := e')
          (h₁ := hd1) (h₂ := hd2) hu
        have hiapply := Equiv.iUnion_symm_apply'
          (f := fun φ ↦ (f φ).nodes) (g := fun φ ↦ (g φ).nodes)
          (h₁ := fun φ ψ hn ↦ (f.property φ).2.2 ψ hn)
          (h₂ := fun φ ψ hn ↦ (g.property φ).2.2 ψ hn)
          (e := eb) (e' := eφ) (i := eb.symm ψ)
          (by simpa only [eb.apply_symm_apply] using hxg)
        have hz : ((Equiv.union e e' hd1 hd2).symm ⟨x, hx⟩).val ∈
            (f (eb.symm ψ)).nodes := by
          rw [hunion]
          exact hiapply ▸ Subtype.coe_prop _
        let hfpre : ∃ φ, ((Equiv.union e e' hd1 hd2).symm ⟨x, hx⟩).val ∈
            (f φ).nodes := ⟨eb.symm ψ, hz⟩
        change (f hfpre.choose).lab
            ((Equiv.union e e' hd1 hd2).symm ⟨x, hx⟩).val = (g hf.choose).lab x
        have hindex : hfpre.choose = eb.symm ψ := by
          by_contra hc
          exact Set.disjoint_left.mp ((f.property hfpre.choose).2.2 _ hc)
            hfpre.choose_spec hz
        rw [hindex, hunion]
        unfold e' at *
        conv => lhs; arg 2; exact hiapply
        have hebind : branches_equiv (Subtype.ext he) (eb.symm ψ) = ψ := by
          change eb (eb.symm ψ) = ψ
          exact eb.apply_symm_apply ψ
        have hh := h (eb.symm ψ)
        have hp := congrArg (fun a : Lpofin _ ↦ a.lab x) hh
        have hxgb : x ∈ (g (branches_equiv (Subtype.ext he) (eb.symm ψ))).nodes :=
          hebind.symm ▸ hxg
        simp only [Lpofin.permute, Lpofin.lab, Lpo.permute, Lpo.lab,
          dif_pos hxgb] at hp
        exact hp.trans (congrArg (fun a : Lpofin _ ↦ a.lab x) (congrArg g hebind))
      · intro hn
        have hxa' : x ∈ α'.nodes := by
          change x ∈ α'.nodes ∪ ⋃ φ, (g φ).nodes at hx
          rcases hx with hx | hx
          · exact hx
          · exact (hn (Set.mem_iUnion.mp hx)).elim
        have heq := Equiv.union_symm_apply_left (e₁ := e) (e₂ := e')
          (h₁ := hd1) (h₂ := hd2) hxa'
        have hp := congrArg (fun a : Lpo _ ↦ a.lab x) he
        simp only [Lpo.permute, Lpo.lab] at hp
        have hp' : α.lab (e.symm ⟨x, hxa'⟩).val = α'.lab x :=
          (dif_pos hxa').symm.trans hp
        exact heq ▸ hp'
    · conv => lhs; exact dif_neg hx
      symm; exact (α'.seq β' g).val.property.lab_dom _ hx

lemma form_permute_union_left {X X' Y Y' : Set Node}
    (e₁ : X ≃ Y) (e₂ : X' ≃ Y') (hd1 : Disjoint X X') (hd2 : Disjoint Y Y')
    {φ : Form Node} (hφ : φ.DependsOn X) :
    φ.permute (Equiv.union e₁ e₂ hd1 hd2) = φ.permute e₁ := by
  symm
  refine Form.permute_monotone ?_ hφ
  refine ⟨Set.subset_union_left, ?_⟩
  intro x
  exact (Equiv.union_apply_left x.property).symm

lemma form_permute_union_right {X X' Y Y' : Set Node}
    (e₁ : X ≃ Y) (e₂ : X' ≃ Y') (hd1 : Disjoint X X') (hd2 : Disjoint Y Y')
    {φ : Form Node} (hφ : φ.DependsOn X') :
    φ.permute (Equiv.union e₁ e₂ hd1 hd2) = φ.permute e₂ := by
  symm
  refine Form.permute_monotone ?_ hφ
  refine ⟨Set.subset_union_right, ?_⟩
  intro x
  exact (Equiv.union_apply_right x.property).symm

lemma form_permute_iUnion {ι κ : Type} {X : ι → Set Node} {Y : κ → Set Node}
    (hdX : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hdY : ∀ i j, i ≠ j → Disjoint (Y i) (Y j))
    (ei : ι ≃ κ) (en : ∀ i, X i ≃ Y (ei i)) (i : ι)
    {φ : Form Node} (hφ : φ.DependsOn (X i)) :
    φ.permute (Equiv.iUnion hdX hdY ei en) = φ.permute (en i) := by
  symm
  refine Form.permute_monotone ?_ hφ
  refine ⟨Set.subset_iUnion X i, ?_⟩
  intro x
  exact (Equiv.iUnion_apply x.property).symm

lemma seq_iso_form_base {α α' β β' : Lpofin (Label act test)} {f : CopyFn α β} {g : CopyFn α' β'}
    {e : α.val.nodes ≃ α'.val.nodes} (he : α.val.permute e = α'.val)
    {eφ : (φ : ↥α.branches) →
      ((f φ).nodes ≃ (g (branches_equiv (Subtype.ext he) φ)).nodes)}
    (hd1 : Disjoint α.nodes (⋃ φ, (f φ).nodes))
    (hd2 : Disjoint α'.nodes (⋃ φ, (g φ).nodes))
    (x : Node) (hx : x ∈ α'.nodes) :
    ((α.seq β f).val.permute (Equiv.union e
      (Equiv.iUnion (fun φ ↦ (f.property φ).2.2) (fun φ ↦ (g.property φ).2.2)
        (branches_equiv (Subtype.ext he)) eφ) hd1 hd2)).form x =
      (α'.seq β' g).val.form x := by
  let eb := branches_equiv (Subtype.ext he)
  let e' := Equiv.iUnion (fun φ ↦ (f.property φ).2.2)
    (fun φ ↦ (g.property φ).2.2) eb eφ
  change ((α.seq β f).val.permute (Equiv.union e e' hd1 hd2)).form x =
    (α'.seq β' g).val.form x
  funext v
  simp only [Lpofin.form, Lpo.permute, Lpo.form, seq, seq_base]
  have hpre : ((Equiv.union e e' hd1 hd2).symm
      ⟨x, Set.subset_union_left hx⟩).val ∈ α.nodes := by
    have heq := Equiv.union_symm_apply_left (e₁ := e) (e₂ := e')
      (h₁ := hd1) (h₂ := hd2) hx
    rw [heq]
    exact Subtype.coe_prop _
  rw [eq_iff_iff]
  sorry
  -- simp only [hx, if_pos]
  -- constructor
  -- · rintro ⟨_, hv⟩
  --   split at hv
  --   · have heq := Equiv.union_symm_apply_left (e₁ := e) (e₂ := e')
  --       (h₁ := hd1) (h₂ := hd2) hx
  --     have hdep := α.val.property.form _ (e.symm ⟨x, hx⟩).property |>.1
  --     have hdep' := Form.DependsOn.monotone _
  --       (fun y hy ↦ α.val.property.rel_dom hy |>.1) hdep
  --     have hformeq := congrArg α.val.val.form heq
  --     have hpermeq := congrArg
  --       (fun φ : Form Node ↦ φ.permute (Equiv.union e e' hd1 hd2) v) hformeq
  --     have hv := hpermeq.mp hv
  --     have hp := congrArg (fun a : Lpo _ ↦ a.form x v) he
  --     simp only [Lpo.permute, Lpo.form] at hp
  --     exact hp.mp ⟨hx, congrFun (form_permute_union_left e e' hd1 hd2 hdep') v |>.mp hv⟩
  --   · contradiction
  -- · intro hv
  --   refine ⟨Set.subset_union_left hx, ?_⟩
  --   split
  --   · have heq := Equiv.union_symm_apply_left (e₁ := e) (e₂ := e')
  --       (h₁ := hd1) (h₂ := hd2) hx
  --     have hp := congrArg (fun a : Lpo _ ↦ a.form x v) he
  --     simp only [Lpo.permute, Lpo.form] at hp
  --     have hdep := α.val.property.form _ (e.symm ⟨x, hx⟩).property |>.1
  --     have hdep' := Form.DependsOn.monotone _
  --       (fun y hy ↦ α.val.property.rel_dom hy |>.1) hdep
  --     have hformeq := congrArg α.val.val.form heq
  --     have hpermeq := congrArg
  --       (fun φ : Form Node ↦ φ.permute (Equiv.union e e' hd1 hd2) v) hformeq
  --     apply hpermeq.symm.mp
  --     apply congrFun (form_permute_union_left e e' hd1 hd2 hdep') v |>.mpr
  --     simp only [eq_iff_iff] at hp
  --     exact (hp.mpr hv).choose_spec
  --   · contradiction

lemma seq_iso_form_copy {α α' β β' : Lpofin (Label act test)} {f : CopyFn α β} {g : CopyFn α' β'}
    {e : α.val.nodes ≃ α'.val.nodes} (he : α.val.permute e = α'.val)
    {eφ : (φ : ↥α.branches) →
      ((f φ).nodes ≃ (g (branches_equiv (Subtype.ext he) φ)).nodes)}
    (h : ∀ φ, (f φ).permute (eφ φ) = g (branches_equiv (Subtype.ext he) φ))
    (hd1 : Disjoint α.nodes (⋃ φ, (f φ).nodes))
    (hd2 : Disjoint α'.nodes (⋃ φ, (g φ).nodes))
    (x : Node) (hx : x ∈ ⋃ φ, (g φ).nodes) :
    ((α.seq β f).val.permute (Equiv.union e
      (Equiv.iUnion (fun φ ↦ (f.property φ).2.2) (fun φ ↦ (g.property φ).2.2)
        (branches_equiv (Subtype.ext he)) eφ) hd1 hd2)).form x =
      (α'.seq β' g).val.form x := by
  let eb := branches_equiv (Subtype.ext he)
  let e' := Equiv.iUnion (fun φ ↦ (f.property φ).2.2)
    (fun φ ↦ (g.property φ).2.2) eb eφ
  change ((α.seq β f).val.permute (Equiv.union e e' hd1 hd2)).form x =
    (α'.seq β' g).val.form x
  obtain ⟨ψ, hxψ⟩ := Set.mem_iUnion.mp hx
  let φ := eb.symm ψ
  have hψ : eb φ = ψ := eb.apply_symm_apply ψ
  have hxψ' : x ∈ (g (eb φ)).nodes := hψ.symm ▸ hxψ
  have hxU : x ∈ ⋃ ψ, (g ψ).nodes := Set.mem_iUnion.mpr ⟨ψ, hxψ⟩
  have hu := Equiv.union_symm_apply_right (e₁ := e) (e₂ := e')
    (h₁ := hd1) (h₂ := hd2) hxU
  have hi := Equiv.iUnion_symm_apply'
    (f := fun φ ↦ (f φ).nodes) (g := fun ψ ↦ (g ψ).nodes)
    (h₁ := fun φ ψ hn ↦ (f.property φ).2.2 ψ hn)
    (h₂ := fun φ ψ hn ↦ (g.property φ).2.2 ψ hn)
    (e := eb) (e' := eφ) hxψ'
  have hpoint : ((Equiv.union e e' hd1 hd2).symm
      ⟨x, Set.subset_union_right hxU⟩).val =
      ((eφ φ).symm ⟨x, hxψ'⟩).val := hu.trans hi
  have hxφ : (e'.symm ⟨x, hxU⟩).val ∈ (f φ).nodes := by
    rw [hi]
    exact Subtype.coe_prop _
  have hxpre : ((Equiv.union e e' hd1 hd2).symm
      ⟨x, Set.subset_union_right hxU⟩).val ∈ (f φ).nodes := by
    rw [hu]
    exact hxφ
  have hnα : ((Equiv.union e e' hd1 hd2).symm
      ⟨x, Set.subset_union_right hxU⟩).val ∉ α.nodes :=
    Set.disjoint_right.mp (f.property φ).2.1 hxpre
  have hnxα : x ∉ α'.nodes := Set.disjoint_right.mp (g.property ψ).2.1 hxψ
  have hxseq : x ∈ α'.nodes ∪ ⋃ ψ, (g ψ).nodes := Set.subset_union_right hxU
  funext v
  simp only [Lpofin.form, Lpo.permute, Lpo.form, seq, seq_base]
  rw [eq_iff_iff]
  constructor
  · rintro ⟨_, hleft⟩
    sorry
    -- split at hleft
    -- · contradiction
    -- split
    -- · contradiction
    -- rcases hleft with ⟨η, hη, hφ⟩
    -- have hηnode := ((f η).val.property.form_dom _).mp ⟨_, hη⟩
    -- have hηeq : η = φ := by
    --   by_contra hne
    --   exact Set.disjoint_left.mp ((f.property η).2.2 φ hne) hηnode hxpre
    -- subst hηeq
    -- refine ⟨eb φ, ?_, ?_⟩
    -- · have hform := congrArg (fun a : Lpofin _ ↦ a.form x v) (h φ)
    --   simp only [Lpofin.permute, Lpofin.form, Lpo.permute, Lpo.form] at hform
    --   apply hform.mp
    --   refine ⟨hxψ', ?_⟩
    --   have hdep := (f φ).val.property.form _ ((eφ φ).symm ⟨x, hxψ'⟩).property
    --   apply congrFun (form_permute_iUnion
    --     (fun i j hn ↦ (f.property i).2.2 j hn)
    --     (fun i j hn ↦ (g.property i).2.2 j hn) eb eφ φ
    --     (Form.DependsOn.monotone _ (fun y hy ↦ (f φ).val.property.rel_dom hy |>.1) hdep.1)) v |>.mp
    --   apply congrFun (form_permute_union_right e e' hd1 hd2
    --     (Form.DependsOn.monotone _ (Set.subset_iUnion (fun η ↦ (f η).nodes) φ)
    --       (Form.DependsOn.monotone _ (fun y hy ↦ (f φ).val.property.rel_dom hy |>.1)
    --         hdep.1))) v |>.mp
    --   exact (congrFun (congrArg (f φ).val.val.form hpoint)
    --     (Form.image v (Equiv.union e e' hd1 hd2).symm)).mp hη
    -- · exact congrFun (form_permute_union_left e e' hd1 hd2
    --     (branch_depends_on φ.property)) v |>.mp hφ
  · intro hright
    sorry
    -- split at hright
    -- · contradiction
    -- rcases hright with ⟨η, hη, hbranch⟩
    -- refine ⟨Set.subset_union_right hxU, ?_⟩
    -- split
    -- · contradiction
    -- have hηnode := ((g η).val.property.form_dom _).mp ⟨_, hη⟩
    -- have hηeq : η = ψ := by
    --   by_contra hne
    --   exact Set.disjoint_left.mp ((g.property η).2.2 ψ hne) hηnode hxψ
    -- subst hηeq
    -- rw [← hψ] at hη hbranch
    -- refine ⟨φ, ?_, ?_⟩
    -- · have hdep := (f φ).val.property.form _ ((eφ φ).symm ⟨x, hxψ'⟩).property
    --   apply (congrFun (congrArg (f φ).val.val.form hpoint)
    --     (Form.image v (Equiv.union e e' hd1 hd2).symm)).mpr
    --   apply congrFun (form_permute_union_right e e' hd1 hd2
    --     (Form.DependsOn.monotone _ (Set.subset_iUnion (fun η ↦ (f η).nodes) φ)
    --       (Form.DependsOn.monotone _ (fun y hy ↦ (f φ).val.property.rel_dom hy |>.1)
    --         hdep.1))) v |>.mpr
    --   apply congrFun (form_permute_iUnion
    --     (fun i j hn ↦ (f.property i).2.2 j hn)
    --     (fun i j hn ↦ (g.property i).2.2 j hn) eb eφ φ
    --     (Form.DependsOn.monotone _ (fun y hy ↦ (f φ).val.property.rel_dom hy |>.1)
    --       hdep.1)) v |>.mpr
    --   have hform := congrArg (fun a : Lpofin _ ↦ a.form x v) (h φ)
    --   simp only [Lpofin.permute, Lpofin.form, Lpo.permute, Lpo.form] at hform
    --   exact (hform.mpr hη).choose_spec
    -- · apply congrFun (form_permute_union_left e e' hd1 hd2
    --     (branch_depends_on φ.property)) v |>.mpr
    --   exact hbranch

lemma seq_iso_form {α α' β β' : Lpofin (Label act test)} {f : CopyFn α β} {g : CopyFn α' β'}
    {e : α.val.nodes ≃ α'.val.nodes} (he : α.val.permute e = α'.val)
    {eφ : (φ : ↥α.branches) →
      ((f φ).nodes ≃ (g (branches_equiv (Subtype.ext he) φ)).nodes)}
    (h : ∀ φ, (f φ).permute (eφ φ) = g (branches_equiv (Subtype.ext he) φ))
    (hd1 : Disjoint α.nodes (⋃ φ, (f φ).nodes))
    (hd2 : Disjoint α'.nodes (⋃ φ, (g φ).nodes)) :
    ((α.seq β f).val.permute (Equiv.union e
      (Equiv.iUnion (fun φ ↦ (f.property φ).2.2) (fun φ ↦ (g.property φ).2.2)
        (branches_equiv (Subtype.ext he)) eφ) hd1 hd2)).form = (α'.seq β' g).val.form := by
  let eb := branches_equiv (Subtype.ext he)
  let e' := Equiv.iUnion (fun φ ↦ (f.property φ).2.2) (fun φ ↦ (g.property φ).2.2) eb eφ
  change ((α.seq β f).val.permute (Equiv.union e e' hd1 hd2)).form = (α'.seq β' g).val.form
  funext x
  by_cases hx : x ∈ (α'.seq β' g).nodes
  · change x ∈ α'.nodes ∪ ⋃ φ, (g φ).nodes at hx
    rcases hx with hx | hx
    · exact seq_iso_form_base he hd1 hd2 x hx
    · exact seq_iso_form_copy he h hd1 hd2 x hx
  · funext v
    rw [eq_iff_iff]
    constructor
    · rintro ⟨hx', _⟩; exact (hx hx').elim
    · intro hf
      exact (hx (((α'.seq β' g).val.property.form_dom x).mp ⟨v, hf⟩)).elim

lemma seq_isomorphic {α α' β β' : Lpofin (Label act test)} {f : CopyFn α β} {g : CopyFn α' β'}
    (hα : α ≈ α') (hβ : β ≈ β') : seq α β f ≈ seq α' β' g := by
  have ⟨e, he⟩ := hα
  let eb := branches_equiv (Subtype.ext he)
  have key (φ : ↑α.branches) :
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
  choose eφ h using key
  have hd1 : Disjoint α.nodes (⋃ φ, (f φ).nodes) := by
    refine Set.disjoint_left.mpr ?_; intro x hx hx'
    have ⟨φ, hx'⟩ := Set.mem_iUnion.mp hx'
    exact Set.disjoint_left.mp (f.property φ).2.1 hx hx'
  have hd2 : Disjoint α'.nodes (⋃ φ, (g φ).nodes) := by
    refine Set.disjoint_left.mpr ?_; intro x hx hx'
    have ⟨φ, hx'⟩ := Set.mem_iUnion.mp hx'
    exact Set.disjoint_left.mp (g.property φ).2.1 hx hx'
  let e' := Equiv.iUnion (fun φ ↦ (f.property φ).2.2) (fun φ ↦ (g.property φ).2.2) eb eφ
  refine ⟨Equiv.union e e' hd1 hd2, ?_⟩
  ext1
  · rfl
  · exact seq_iso_rel he h hd1 hd2
  · exact seq_iso_lab he h hd1 hd2
  · exact seq_iso_form he h hd1 hd2

end Lpofin
