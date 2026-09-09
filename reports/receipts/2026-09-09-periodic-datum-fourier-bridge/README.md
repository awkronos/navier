# Periodic datum Fourier bridge receipt

At source SHA-256
`568a8f0a05d3725a2fbb42e3ad7142ce84f46b294177f98b3d520c2fa516db84`,
the source compiles and its audited public endpoints use only `propext`,
`Classical.choice`, and `Quot.sound`.

`nativeCoefficient` is the componentwise Fourier coefficient of the official
real velocity datum, defined by the literal nested integral over `[0,1]^3`
with kernel `exp (-2π i k · x)`.  The proof turns the official generator
periodicity into invariance under all integer translations, obtains arbitrary
mixed coefficient decay by repeated integration by parts, and proves the
weighted `ℓ¹` contract consumed by the existing lattice convolution layer.

This closes the static weighted-summability part of the native datum bridge.
It does not prove coefficient reality or spectral divergence-free constraints,
construct a weighted Banach carrier, reconstruct the physical field, or prove
the arbitrary-data evolution and global bound required by alternative B.
