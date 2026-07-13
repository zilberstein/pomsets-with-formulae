import Mathlib.Order.WithBot

import DomainTheory.DCPO

inductive Label (act : Type) (test : Type)
  | bot : Label act test
  | fork : Label act test
  | act : act → Label act test
  | test : test → Label act test

namespace Label

variable {act test : Type}

def isAct (ℓ : Label act test) : Prop :=
  match ℓ with
  | Label.act _ => True
  | _ => False

lemma isAct_iff (ℓ : Label act test) : ℓ.isAct ↔ ∃ a, ℓ = Label.act a := by
  constructor
  · intro h; cases ℓ <;> (try contradiction); exact ⟨_, rfl⟩
  · rintro ⟨_, rfl⟩; trivial

def isTest (ℓ : Label act test) : Prop :=
  match ℓ with
  | Label.test _ => True
  | _ => False

lemma isTest_iff (ℓ : Label act test) : ℓ.isTest ↔ ∃ b, ℓ = Label.test b := by
  constructor
  · intro h; cases ℓ <;> (try contradiction); exact ⟨_, rfl⟩
  · rintro ⟨_, rfl⟩; trivial

end Label

instance {act test : Type} : Bot (Label act test) where
  bot := Label.bot

instance {act test : Type} [LE act] [LE test] : LE (Label act test) where
  le l1 l2 :=
    match l1 with
    | Label.bot => True
    | Label.fork => l2 = Label.fork
    | Label.act a =>
      match l2 with
      | Label.act a' => a ≤ a'
      | _ => False
    | Label.test b =>
      match l2 with
      | Label.test b' => b ≤ b'
      | _ => False

lemma lab_is_act_le {act test : Type} {a : act} {l : Label act test}
    [Preorder act] [Preorder test]
    (hle : Label.act a ≤ l) :
    ∃ a', l = Label.act a' ∧ a ≤ a' := by
  cases l <;> (try contradiction); exact ⟨_, rfl, hle⟩

lemma lab_is_test_le {act test : Type} {b : test} {l : Label act test}
    [Preorder act] [Preorder test]
    (hle : Label.test b ≤ l) :
    ∃ b', l = Label.test b' ∧ b ≤ b' := by
  cases l <;> (try contradiction); exact ⟨_, rfl, hle⟩

lemma lab_is_fork_le {act test : Type} {l : Label act test}
    [LE act] [LE test]
    (hle : Label.fork ≤ l) :
    l = Label.fork := by
  cases l <;> (try contradiction); rfl

instance {act test : Type} [LE act] [LE test] : OrderBot (Label act test) where
  bot_le _ := True.intro

instance {act test : Type} [Preorder act] [Preorder test] : Preorder (Label act test) where
  le_refl := by intro l; cases l <;> simp only [LE.le, Std.le_refl]
  le_trans := by {
    intro l₁ l₂ l₃ h12 h23; simp only [LE.le]
    match l₁ with
    | Label.bot => simp
    | Label.fork =>
        simp only [LE.le] at h12; simp only [LE.le, h12] at h23
        exact h23
    | Label.act a =>
        rcases lab_is_act_le h12 with ⟨a₂, hl₂, ha₂⟩; subst hl₂
        rcases lab_is_act_le h23 with ⟨a₃, hl₃, ha₃⟩; subst hl₃
        exact le_trans ha₂ ha₃
    | Label.test b =>
        rcases lab_is_test_le h12 with ⟨b₂, hl₂, hb₂⟩; subst hl₂
        rcases lab_is_test_le h23 with ⟨b₃, hl₃, hb₃⟩; subst hl₃
        exact le_trans hb₂ hb₃
  }

instance {act test : Type} [PartialOrder act] [PartialOrder test] :
    PartialOrder (Label act test) where
  le_antisymm l₁ l₂ h12 h21 := by {
    cases l₁ <;> cases l₂ <;>
      simp only [LE.le, reduceCtorEq, Label.act.injEq, Label.test.injEq] at *
    · exact le_antisymm h12 h21
    · exact le_antisymm h12 h21
  }

lemma label_dset {act test : Type} [Preorder act] [Preorder test] (d : DSet (Label act test)) :
    (d = DSet.singleton ⊥) ∨
    (Label.fork ∈ d ∧ ∀ ℓ ∈ d, ℓ = ⊥ ∨ ℓ = Label.fork) ∨
    ((∃ a, Label.act a ∈ d) ∧ ∀ ℓ ∈ d, ℓ = ⊥ ∨ ℓ.isAct) ∨
    ((∃ b, Label.test b ∈ d) ∧ ∀ ℓ ∈ d, ℓ = ⊥ ∨ ℓ.isTest) := by
  by_cases hd : d = DSet.singleton ⊥
  · left; exact hd
  · right
    have ⟨ℓ, hℓ, hbot⟩ : ∃ ℓ ∈ d, ℓ ≠ ⊥ := by
      by_contra h; simp only [ne_eq, not_exists, not_and, not_not] at h
      apply hd; refine Subtype.ext ?_; ext ℓ; constructor
      · intro hℓ; rw [h _ hℓ]; rfl
      · rintro rfl; have ⟨ℓ, hℓ⟩ := d.nonempty
        rw [h _ hℓ] at hℓ; exact hℓ
    cases ℓ with
    | bot => contradiction
    | fork =>
      left; refine ⟨hℓ, ?_⟩; intro ℓ' hℓ'
      have ⟨z, _, hz, hle⟩ := d.directed _ hℓ _ hℓ'
      rcases lab_is_fork_le hz with rfl
      cases ℓ' <;> try contradiction
      · left; rfl
      · right; rfl
    | act a =>
      right; left; refine ⟨⟨a, hℓ⟩, ?_⟩; intro ℓ' hℓ'
      have ⟨z, _, hz, hle⟩ := d.directed _ hℓ _ hℓ'
      rcases lab_is_act_le hz with ⟨_, rfl, hle⟩
      cases ℓ' <;> try contradiction
      · left; rfl
      · right; trivial
    | test b =>
      right; right; refine ⟨⟨b, hℓ⟩, ?_⟩; intro ℓ' hℓ'
      have ⟨z, _, hz, hle⟩ := d.directed _ hℓ _ hℓ'
      rcases lab_is_test_le hz with ⟨_, rfl, hle⟩
      cases ℓ' <;> try contradiction
      · left; rfl
      · right; trivial

def to_act_dset {act test : Type} [Preorder act] [Preorder test] (d : DSet (Label act test))
    (h : ∃ a, Label.act a ∈ d) :
    DSet act := {
  val := { a | Label.act a ∈ d }
  property := by
    refine ⟨?_, h⟩; intro a₁ ha₁ a₂ ha₂
    have ⟨ℓ, hℓ, hle₁, hle₂⟩ := d.directed _ ha₁ _ ha₂
    obtain ⟨a, rfl, _⟩ := lab_is_act_le hle₁
    exact ⟨a, hℓ, hle₁, hle₂⟩
}

def to_test_dset {act test : Type} [Preorder act] [Preorder test] (d : DSet (Label act test))
    (h : ∃ b, Label.test b ∈ d) :
    DSet test := {
  val := { b | Label.test b ∈ d }
  property := by
    refine ⟨?_, h⟩; intro b₁ hb₁ b₂ hb₂
    have ⟨ℓ, hℓ, hle₁, hle₂⟩ := d.directed _ hb₁ _ hb₂
    obtain ⟨a, rfl, _⟩ := lab_is_test_le hle₁
    exact ⟨a, hℓ, hle₁, hle₂⟩
}

lemma exists_lub {act test : Type} [DCPO act] [DCPO test] (d : DSet (Label act test)) :
    ∃ ℓ, IsLUB d.val ℓ := by
  rcases label_dset d with rfl | ⟨hfork, h⟩ | ⟨hact, h⟩ | ⟨htest, h⟩
  · refine ⟨⊥, ?_, ?_⟩
    · rintro ℓ rfl; trivial
    · intro _ _; exact bot_le
  · refine ⟨Label.fork, ?_, ?_⟩
    · intro ℓ hℓ; rcases h _ hℓ with rfl | rfl <;> trivial
    · intro ℓ hℓ; exact hℓ hfork
  · refine ⟨Label.act (to_act_dset d hact).dSup, ?_, ?_⟩
    · intro ℓ hℓ; rcases h _ hℓ with rfl | h
      · exact bot_le
      · obtain ⟨_, rfl⟩ := ℓ.isAct_iff.mp h; exact DSet.le_dSup hℓ
    · intro ℓ hℓ; have ⟨_, hact⟩ := hact
      obtain ⟨a, rfl, hle⟩ := lab_is_act_le (hℓ hact)
      exact DSet.dSup_le fun _ ha ↦ hℓ ha
  · refine ⟨Label.test (to_test_dset d htest).dSup, ?_, ?_⟩
    · intro ℓ hℓ; rcases h _ hℓ with rfl | h
      · exact bot_le
      · obtain ⟨_, rfl⟩ := ℓ.isTest_iff.mp h; exact DSet.le_dSup hℓ
    · intro ℓ hℓ; have ⟨_, htest⟩ := htest
      obtain ⟨b, rfl, hle⟩ := lab_is_test_le (hℓ htest)
      exact DSet.dSup_le fun _ hb ↦ hℓ hb

noncomputable instance {act test : Type} [DCPO act] [DCPO test] : DCPO (Label act test) where
  dSup d := (exists_lub d).choose
  lubOfDirected d := (exists_lub d).choose_spec
