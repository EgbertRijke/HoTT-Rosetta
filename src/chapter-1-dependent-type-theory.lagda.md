# Chapter 1 Dependent Type Theory

```agda
module chapter-1-dependent-type-theory where
```

Dependent type theory is a system of inference rules that can be combined to make *derivations*.
In these derivations, the goal is often to construct an element of a certain type.
Such an element can be a function if the type of the constructed element is a function type; a proof of a property if the type of the constructed element is a proposition; but it can also be an identification if the type of the constructed element is an identity type, and so on.
In some respect, a type is just a collection of mathematical objects and constructing elements of a type is the everyday mathematical task or challenge.
The system of inference rules that we call type theory offers a principled way of engaging in mathematical activity.

```agda
open import section-1-1-judgments-and-contexts-in-type-theory
open import section-1-2-type-families
open import section-1-3-inference-rules
open import section-1-4-derivations
```
