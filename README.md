# Isogeny meet-in-the-middle

This is a Rust program which tries to find an isogeny of degree $2^{e_a}$ between two elliptic curves. It takes as input the short weierstrass coefficients of the starting curve, the j-invariant of the target curve and $e_a$. It only considers the isogeny up to isomorphism, if you have a specific target curve of the isomorphism class in mind you will need to account for that.

It works with j-invariants in $\mathbb{F}_{p^2}$ where $p$ is a prime of the form $2^{e_a}3^{e_b}-1$. `generate_problem.py` shows how to supply input to the program. If you want to change the prime number you will need to edit the start of `src/main.rs`, use the output of `generate_problem.py` to get the correct values. This is a small experiment of mine and is not designed to be user friendly, but if you have a good idea of how to supply run-time prime numbers without affecting performance I would be happy to hear it.

Command you can use to test the current configuration:
`cargo run --release 0 0 1 0 2650467163916332087580100642 18201068689908591548055750637 37`

(this is my first Rust project the code might be a bit rough)