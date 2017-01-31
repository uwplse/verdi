* make all proofs robust against changes in hypothesis names and
  ordering. the effort to do so will be more than made up for as you
  change your theorem statements.
* don't say `P -> A /\ B` but instead say `(P -> A) /\ (P -> B)`, even
  if `P` is long (in which case maybe you should give it a name/notation). this
  makes automatic backwards reasoning easier.
* don't say `P <-> Q` but instead say `(P -> Q) /\ (Q -> P)` even if `P`
  and `Q` are long (give them names/notations). this is also for
  backwards reasoning.
* when deciding hypothesis order `P -> Q -> R`, place most restrictive
  hypothesis first. this helps because it reduces the chance that
  eauto will infer the wrong thing satisfying `P` but not `Q`.
* obvious truism: constantly throw exploratory proofs away. it's
  not enough to play the video game until QED, produce a maintainable
  proof that liberally uses lemmas and tactics.
* whenever possible, define complete "eliminator" lemmas for the facts
  you need to reason about. for example, `foo x = true -> P x /\ Q x`
  where `P` and `Q` is "all the information" contained in `foo x =
  true`. Do this instead of (or in addition to) proving `foo x = true
  -> P x` and `foo x = true -> Q x` because the complete eliminator
  avoids the need to manage the context in the common case: since the
  eliminator is complete, it is always safe to apply it.
* eliminator lemmas don't work well with backwards reasoning. so it is
  common to reason forward with them. thus, for each commonly used
  eliminator lemma `foo_elim : foo x = true -> P x /\ Q x` , define a
  corresponding `do_foo_elim` tactic of the form
```coq
match goal with
  | [ H : foo _ = true |- _ ] => apply foo_elim in H; break_and
end.
```
* if necessary/convenient, use a general `elim` tactic that calls all
  your elimination tactics.
* TEST THINGS. Verifying software is hard and verifying incorrect
  software is impossible, so any time spent finding bugs before starting to
  prove stuff will pay dividends down the road.
* each lemma should unfold only one thing. think of this like the
  standard software engineering practice of hiding implementation
  details. this leads to somewhat longer proof developments, but they
  are much more robust to definition change.
* avoid simpl-ing non-trivial definitions. a common anti-pattern:
  `simpl in *; repeat break_match; ...` this can be very convenient
  for exploratory proofs, but is generally unmaintainable and has
  horrible performance. instead, prove all the definitional equalities
  you need propositionally as lemmas. another option is to prove a
  high-level "definition" lemma, which is usually a big or of ands
  that does all the case analysis for you at once. this is much more
  efficient and maintainable.
