theory dev_1_3
imports Main

begin

typedecl entity
typedecl event

consts
  Consumer :: "entity ⇒ bool"
  TrophicLevel :: "entity ⇒ bool"
  Feed :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  At :: "event ⇒ entity ⇒ bool"
  Omnivore :: "entity ⇒ bool"
  Plant :: "entity ⇒ bool"
  Producer :: "entity ⇒ bool"

(* Explanation 1: Many consumers feed at more than one trophic level. *)
axiomatization where
  explanation_1: "∃x y e. Consumer x ∧ TrophicLevel y ⟶ Feed e ∧ Agent e x ∧ At e y"

(* Explanation 2: All omnivores are consumers. *)
axiomatization where
  explanation_2: "∀x. Omnivore x ⟶ Consumer x"

(* Explanation 3: Plants are producers. *)
axiomatization where
  explanation_3: "∀x. Plant x ⟶ Producer x"

theorem hypothesis:
  assumes asm: "Omnivore x ∧ TrophicLevel y"
  (* Hypothesis: Omnivores can feed at more than one trophic level. *)
  shows "∀x y e. Omnivore x ∧ TrophicLevel y ⟶ Feed e ∧ Agent e x ∧ At e y"
  sledgehammer
  oops

end
