# Homological algebra in Lean

In this repository, I slowly work towards some form of homological algebra in
the Lean theorem prover. For now, I'm busy proving basic facts about abelian
categories.

## Table of contents

* Preadditive categories and biproducts (this will hopefully be made obsolete
soon by enriched categories in mathlib)
* The definitition of an abelian category
  * We use a relatively low-tech definition while still requiring preadditivity
* Basic facts about abelian categories
  * Image factorization
  * mono + epi = iso
  * The pullback of an epimorphism is an epimorphism
* The definition and basic facts about exactness
* Pseudoelements
  * The definition and the usual characterizations of exactness etc.
* A buggy and inefficient tactic that chases pseudoelements
* Proofs of the four lemma, the kernels' lemma and the snake lemma (the general
  one) valid in any abelian category
* A proof that the category of modules is abelian
  * and also that categorical exactness means precisely `f.range = g.ker`
  * A proof of the four lemma for modules that works by specializing the four lemma
  for abelian categories to the category of modules

There used to be some other things in here which I have since deleted. Some of
these have since found their way into mathlib.
