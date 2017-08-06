## higher-order-unification

A simple, concise implementation of Huet's algorithm. Written because
it's difficult to translate the simple prose explanations of
algorithms often adopted by the unification community to a working
piece of code. The code is documented fully in `explanation.md`.

An example of how higher-order unification might be used may be found
in `src/Client.hs` which provides a simple type-inference/checking
algorithm for a dependently typed language with `Type : Type`.
