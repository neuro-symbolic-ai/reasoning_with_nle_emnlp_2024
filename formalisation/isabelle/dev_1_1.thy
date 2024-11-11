theory dev_1_1
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
  Plant :: "entity ⇒ bool"
  Producer :: "entity ⇒ bool"
  Omnivore :: "entity ⇒ bool"
  Be :: "event ⇒ bool"
  TypeOf :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: Many consumers feed at more than one trophic level. *)
axiomatization where
  explanation_1: "∃x y e. Consumer x ∧ TrophicLevel y ∧ Feed e ∧ Agent e x ∧ At e y"

(* Explanation 2: All plants are producers, and all producers are consumers, and all consumers can be omnivores. *)
axiomatization where
  explanation_2: "∀x. Plant x ⟶ Producer x ∧ (∀y. Producer y ⟶ Consumer y) ∧ (∀z. Consumer z ⟶ (∃e. Omnivore z ∧ Be e ∧ Agent e z))"

(* Explanation 3: Omnivores are a specific type of consumer that can feed at more than one trophic level. *)
axiomatization where
  explanation_3: "∀x. Omnivore x ⟶ (∃y e z. Consumer y ∧ TypeOf x y ∧ Feed e ∧ Agent e x ∧ At e z ∧ TrophicLevel z)"

theorem hypothesis:
  assumes asm: "Omnivore x"
  (* Hypothesis: Omnivores can feed at more than one trophic level. *)
  shows "∃y e. Omnivore x ∧ TrophicLevel y ∧ Feed e ∧ Agent e x ∧ At e y"
  using assms explanation_3 by blast
  

end
