# A Tutorial on QIQT-H

*How holographic finite-information constraints can — in principle — address the measurement problem of quantum mechanics, without adding collapses, worlds as separate substances, or hidden trajectories.*

> **Important status note.** QIQT-H, as presented here, is a research-program framework, not an established theory like standard quantum mechanics or quantum field theory. The goal of this tutorial is not to claim that QIQT-H is already correct. The goal is to explain the pieces: what the mathematical ingredients mean, why they are being used, and how they are supposed to fit together.

---

# 0. What this is and how to read it

The central idea of QIQT-H is:

> Quantum theory gives amplitudes for many possible histories. But in a universe with gravity, a finite causal region cannot contain arbitrarily much distinguishable information. The holographic entropy bound says that the amount of information associated with a region is controlled not by its volume, but by the area of its boundary. QIQT-H tries to turn that into a constraint on which quantum histories can count as physically admissible records.

That is the short version.

The long version requires ingredients from several areas:

- standard quantum measurement theory,
- decoherence,
- black-hole entropy and holography,
- von Neumann algebras,
- modular theory,
- crossed products,
- generalized entropy,
- decoherent histories,
- and some foundations issues such as Bell’s theorem.

Some of these words sound intimidating. The point of this tutorial is to unpack them from the ground up.

You should know:

- ordinary undergraduate quantum mechanics,
- Hilbert spaces and matrices,
- density matrices,
- entropy in statistical mechanics,
- basic special relativity,
- the rough idea of QFT.

You do **not** need to know:

- functional analysis,
- operator algebras,
- Tomita-Takesaki theory,
- algebraic QFT,
- Connes-Takesaki theory.

We will build those ideas slowly, starting from matrices.

---

# 1. The measurement problem in one page

In ordinary quantum mechanics, the state evolves by Schrödinger’s equation:

$$
i\hbar \frac{d}{dt}|\psi(t)\rangle = H|\psi(t)\rangle.
$$

This evolution is:

- deterministic,
- linear,
- unitary.

But measurements seem to produce definite outcomes.

Suppose a spin starts in

$$
|\psi\rangle = \alpha |\uparrow\rangle + \beta |\downarrow\rangle.
$$

A measuring device begins in a ready state $|M_0\rangle$ (pointer at zero, nothing recorded yet). We assume a *good* measurement coupling: if the spin is definitely $|\uparrow\rangle$, the device evolves to a macroscopically distinct pointer state $|M_\uparrow\rangle$ — "pointer reads up" — and similarly $|\downarrow\rangle|M_0\rangle \longrightarrow |\downarrow\rangle|M_\downarrow\rangle$ with $|M_\downarrow\rangle$ being "pointer reads down." The two pointer states are orthogonal,

$$
\langle M_\uparrow | M_\downarrow \rangle = 0,
$$

because they differ in a macroscopic degree of freedom (the pointer is literally in a different position). For an unknown input spin, linearity of Schrödinger evolution forces

$$
(\alpha|\uparrow\rangle+\beta|\downarrow\rangle)|M_0\rangle
\longrightarrow
\alpha|\uparrow\rangle|M_\uparrow\rangle
+
\beta|\downarrow\rangle|M_\downarrow\rangle.
$$

But in the lab, we see one pointer position, not a ghostly superposition of two pointer readings.

So we have a tension:

1. Schrödinger evolution says superpositions persist.
2. Experience says outcomes are definite.

Standard interpretations solve this in different ways:

| Interpretation | Move |
|---|---|
| Copenhagen | Add collapse as a rule for measurements |
| Many-worlds | Keep all branches; each observer sees one branch |
| Bohmian mechanics | Add particle positions guided by the wavefunction |
| Objective collapse | Modify Schrödinger dynamics |
| QBism / relational views | Reinterpret the state as information or relation |

QIQT-H tries a different route.

It keeps ordinary quantum amplitudes but adds a **global information constraint** motivated by gravity and holography.

Roughly:

> Not every formally available branch is allowed to correspond to an independent physical record inside a finite causal region. The admissible set of records must fit inside a holographic entropy budget.

That statement needs a lot of unpacking.

---

# 2. The basic picture: amplitudes, branches, and records

In ordinary QM, if we have alternatives $i$, the state can be written

$$
|\Psi\rangle = \sum_i c_i |i\rangle.
$$

The Born rule says

$$
P(i)=|c_i|^2.
$$

But in real measurements, $i$ is not merely a label in a tiny Hilbert space. It becomes a **record**:

- a pointer points left,
- a detector clicked,
- photons scattered into the room,
- neurons in an observer’s brain encode an outcome.

The essential object is not merely “the spin is up,” but rather:

$$
\text{spin up} + \text{apparatus says up} + \text{environment contains records of up}.
$$

A branch is approximately a large entangled component:

$$
|\Psi\rangle
\approx
\alpha |\uparrow\rangle |M_\uparrow\rangle |E_\uparrow\rangle
+
\beta |\downarrow\rangle |M_\downarrow\rangle |E_\downarrow\rangle.
$$

Why should

$$
\langle E_\uparrow | E_\downarrow\rangle \approx 0
$$

in practice? The standard Joos-Zeh answer is: because the apparatus is continually scattered by its environment. Air molecules, photons, phonons, electronics, and many other degrees of freedom interact with the pointer. If the pointer is in the up-position, an incoming environmental particle is scattered into one outgoing state; if it is in the down-position, into a different outgoing state:

$$
|M_i\rangle |e^{(k)}_{\rm in}\rangle \longrightarrow |M_i\rangle |e^{(k)}_i\rangle,
\qquad i=\uparrow,\downarrow.
$$

Here $k$ labels one scattering event. The crucial approximation is independence: different environmental particles scatter separately, and the incoming environment is approximately a product state. After $N$ such events,

$$
|E_i^{(N)}\rangle = |e_i^{(1)}\rangle |e_i^{(2)}\rangle \cdots |e_i^{(N)}\rangle,
\qquad
D_N \equiv \langle E_\downarrow^{(N)} | E_\uparrow^{(N)}\rangle = \prod_{k=1}^N \langle e_\downarrow^{(k)} | e_\uparrow^{(k)}\rangle.
$$

This is the product formula. It is not a new postulate — it follows from many independent scattering records. Each scattered photon or molecule may carry only a tiny amount of which-branch information, but the information accumulates *multiplicatively*.

Suppose each event reduces the squared overlap by a small amount, $|\langle e_\downarrow^{(k)} | e_\uparrow^{(k)}\rangle|^2 = 1 - \eta$, and events arrive at rate $\gamma$, so $N(t) \simeq \gamma t$. Then

$$
|D_N|^2 = (1-\eta)^N \approx e^{-N\eta} \approx e^{-\Lambda t},
\qquad \Lambda = \gamma\eta,
\qquad t_D = \Lambda^{-1}.
$$

This $t_D$ is the **decoherence time**. For a macroscopic pointer in an ordinary environment it is usually fantastically short — the original Joos-Zeh 1985 collisional-decoherence calculation gives $t_D \sim 10^{-30}\,\mathrm{s}$ for a dust grain in air. Decoherence is fast.

The effect is seen by tracing out the environment. Using an orthonormal basis $\{|r\rangle\}$ for $E$,

$$
\begin{aligned}
\rho_S
&= \mathrm{Tr}_E |\Psi\rangle\langle\Psi| = \sum_r \langle r | \Psi\rangle\langle\Psi | r\rangle \\
&= |\alpha|^2 |\uparrow M_\uparrow\rangle\langle\uparrow M_\uparrow|
+ |\beta|^2 |\downarrow M_\downarrow\rangle\langle\downarrow M_\downarrow| \\
&\quad + \alpha\beta^* \langle E_\downarrow | E_\uparrow\rangle |\uparrow M_\uparrow\rangle\langle\downarrow M_\downarrow| + \text{h.c.}
\end{aligned}
$$

The diagonal terms are the apparent alternatives. The off-diagonal terms are the interference terms. Decoherence is the rapid suppression of those off-diagonal terms by the factor $\langle E_\downarrow | E_\uparrow\rangle$.

This statement is basis-dependent. Decoherence suppresses interference in the basis that the environment *monitors*. For a measuring device this is a basis of robust **pointer states**: macroscopically distinct positions, currents, tracks, or records. Zurek calls this environmental selection of stable states **einselection**, and we return to it in §6.

But nothing has collapsed. The full state of spin, apparatus, and environment is still a pure entangled state. Decoherence explains why branches stop interfering for local observers — but it does **not** choose one outcome. It gives an apparent classical branching structure. The measurement problem remains:

> Why do I experience one branch rather than a superposition of branches?

QIQT-H says: the answer may involve not a dynamical collapse, but a constraint on possible records.

---

# 3. The holographic clue: finite information in gravity

In non-gravitational quantum mechanics, it is tempting to say that a finite volume can contain arbitrarily much information. Just use shorter and shorter wavelengths.

But gravity changes that.

If you pack too much energy into a region, the region collapses into a black hole.

Here is the standard textbook calculation of the black-hole entropy. It is not the full Hawking 1975 derivation — that requires quantum field theory in curved spacetime — but it uses Hawking's main result, the temperature of the horizon, plus ordinary thermodynamics, and arrives at the right answer.

For a Schwarzschild black hole of mass $M$, the Hawking temperature is

$$
T_H = \frac{\hbar c^3}{8\pi G M k_B}.
$$

This temperature is set by the surface gravity of the horizon: larger black holes are colder.

Use the first law of thermodynamics, $dE = T_H \, dS$, with the black-hole energy $E = M c^2$, so $dE = c^2 \, dM$. Then

$$
dS = \frac{c^2 \, dM}{T_H} = c^2 \, dM \cdot \frac{8\pi G M k_B}{\hbar c^3} = \frac{8\pi G k_B}{\hbar c} \, M \, dM.
$$

Integrating from $0$ to $M$,

$$
S(M) = \frac{4\pi G M^2 k_B}{\hbar c}.
$$

Now rewrite in terms of the horizon area. The Schwarzschild radius is $r_s = 2GM/c^2$, so the horizon area is

$$
A = 4\pi r_s^2 = \frac{16\pi G^2 M^2}{c^4}.
$$

Define the Planck area

$$
\ell_P^2 = \frac{G\hbar}{c^3}.
$$

Then

$$
\frac{k_B A}{4 \ell_P^2}
= \frac{k_B}{4} \cdot \frac{16\pi G^2 M^2}{c^4} \cdot \frac{c^3}{G\hbar}
= \frac{4\pi G M^2 k_B}{\hbar c}.
$$

This matches the entropy from the first law, so

$$
S_{\rm BH} = \frac{k_B A}{4 \ell_P^2} = \frac{k_B c^3 A}{4 G \hbar}.
$$

This is the Bekenstein-Hawking entropy.

There is also Bekenstein's intuitive "drop a bit" heuristic, which gives the scaling without invoking the first law. A bit of information localized in a region of size $R$ needs a wavelength of order $R$, so its minimum energy is $E_{\rm bit} \sim \hbar c / R$. Drop one such bit into a Schwarzschild black hole of horizon radius $R$. The mass increase is

$$
dM = E_{\rm bit} / c^2 \sim \hbar / (R c).
$$

The change in horizon area is

$$
dA = \frac{dA}{dM} \, dM = \frac{32\pi G^2 M}{c^4} \cdot \frac{\hbar}{R c}.
$$

Using $R = r_s = 2GM/c^2$,

$$
dA \sim 16\pi \, \frac{G\hbar}{c^3} = 16\pi \, \ell_P^2.
$$

Up to numerical factors: **one bit of information costs about one Planck area of horizon**. The entropy is the number of bits the horizon can store, so $S \sim A/\ell_P^2$.

In the natural units used in the rest of the tutorial, $c = k_B = 1$, the Planck area is $\ell_P^2 = G\hbar$ and the Bekenstein-Hawking entropy reads

$$
S_{\rm BH} = \frac{A}{4G\hbar}.
$$

The striking thing is that entropy scales like **area**, not volume.

That motivates the holographic principle:

> The maximum number of independent degrees of freedom in a gravitational region scales like the area of its boundary.

If entropy counts distinguishable states, then a region with boundary area $A$ can contain at most roughly

$$
N \sim e^{A/4G\hbar}
$$

orthogonal distinguishable states.

QIQT-H takes this seriously.

If a measurement creates records, and records are physical information, then the total physically meaningful record content in a causal region should be bounded by generalized entropy.

This is the “H” in QIQT-H: holographic.

---

# 4. Entropy basics: Shannon, von Neumann, Rényi-0, and support

Before we talk about holographic information constraints, we need to review several kinds of entropy.

Why several? Because "how much information is in a distribution?" is not one question — it is many. *On average, how surprising is a draw?* *How many outcomes are possible at all?* *How peaked is the worst-case outcome?* *Can we ignore vanishingly tiny tails?* Each of these legitimate questions gets its own entropy. In QIQT-H different parts of the framework care about different ones: the holographic bound is most naturally a bound on the **number of distinguishable record alternatives**, not on average surprise — so we will eventually need a *support-counting* entropy rather than Shannon. To see why, we need the full menu.

## 4.1 Shannon entropy

For a classical probability distribution $p_i$, the Shannon entropy is

$$
H(p) = -\sum_i p_i \log p_i.
$$

It measures the expected surprise of a draw from the distribution — equivalently, the average number of bits needed to encode an outcome. It is the right entropy when you care about *typical* behaviour: thermodynamics, source coding, channel capacity. Its weakness for our purposes is that it almost ignores rare outcomes — a tiny tail probability barely affects $H$, even though the corresponding outcome is *still physically possible*.

Example:

- Fair coin: $p=(1/2,1/2)$

$$
H = -2\cdot \frac12 \log \frac12 = \log 2.
$$

- Biased coin: $p=(0.99,0.01)$

$$
H \approx 0.056 \text{ nats},
$$

much smaller.

Shannon entropy cares about probabilities.

> **Aside: units (bits, nats, hartleys).** The entropy $H = -\sum_i p_i \log p_i$ depends on the base of the logarithm. Using $\log_2$ gives **bits** (binary digits); using $\ln$ gives **nats**; using $\log_{10}$ gives **hartleys** (decimal digits). The conversion is $1\,\text{nat} = 1/\ln 2 \approx 1.443\,\text{bits}$. In QIQT-H the choice of units does not change the physics; we use natural logarithms throughout.

## 4.2 Von Neumann entropy

Shannon entropy takes a probability distribution as input. In quantum mechanics the fundamental object is not a probability distribution but a *density matrix* $\rho$ — possibly carrying coherences between basis states. We need a quantum analogue.

For a density matrix $\rho$, the quantum entropy is

$$
S(\rho) = -\mathrm{Tr}(\rho \log \rho).
$$

If $\rho$ has eigenvalues $p_i$, then

$$
S(\rho) = -\sum_i p_i \log p_i.
$$

So von Neumann entropy is just Shannon entropy applied to the eigenvalues of $\rho$. Its physical content is sharper than Shannon's: $S(\rho)$ measures the *mixedness* of a quantum state, and for a bipartite pure state it equals the **entanglement entropy** of either subsystem. This is the entropy that appears in QFT entanglement bounds, in Page's curve, and in the Bekenstein-Hawking formula. Like Shannon, however, it weights outcomes by probability and is insensitive to small-amplitude branches.

Example:

$$
\rho =
\begin{pmatrix}
1/2 & 0 \\
0 & 1/2
\end{pmatrix}
$$

has

$$
S(\rho)=\log 2.
$$

A pure state

$$
\rho=|\psi\rangle\langle\psi|
$$

has eigenvalues $1,0,0,\dots$, so

$$
S(\rho)=0.
$$

## 4.3 Rényi entropies

The **Rényi entropies** are a family $H_\alpha$, indexed by a parameter $\alpha \ge 0$, whose $\alpha \to 1$ limit is the Shannon entropy. Changing $\alpha$ changes which probabilities dominate the answer: small $\alpha$ treats all nonzero possibilities more equally, while large $\alpha$ emphasizes the largest probabilities. Explicitly, for $\alpha \ge 0$ with $\alpha \ne 1$,

$$
H_\alpha(p)=\frac{1}{1-\alpha}\log\left(\sum_i p_i^\alpha\right),
$$

with the boundary cases understood as limits. Two values matter for QIQT-H:

- $\alpha \to 0$: take the one-sided limit $\alpha \to 0^+$ inside the sum. For $p_i > 0$, $p_i^\alpha \to 1$; for $p_i = 0$, $0^\alpha = 0$ for every $\alpha > 0$, so the limit is $0$. Hence each nonzero outcome contributes a $1$ and $H_0 = \log|\mathrm{supp}(p)|$ — *counts possibilities*.
- $\alpha \to 1$: recovers Shannon entropy — *typical behaviour*.

(Other choices exist — $\alpha = 2$ gives the collision entropy $H_2 = -\log\sum_i p_i^2$, and $\alpha \to \infty$ gives the min-entropy $H_\infty = -\log\max_i p_i$ — but QIQT-H does not use them.)

The holographic capacity is about *distinguishable possibilities*, not average surprise, so the central QIQT-H quantity will be built from $\alpha = 0$. Shannon ($\alpha = 1$) reappears on the *other* side of the bound, inside the generalized entropy.

## 4.4 Rényi-0 entropy: counting possible outcomes

The expression $p_i^0$ is fine for $p_i > 0$ but ambiguous when $p_i = 0$, since $0^0$ is undefined. If we naively extended $x^0 = 1$ to the zero bins as well, we would get $H_0 = \log N$ where $N$ is the number of *formal* bins listed — including ones that cannot occur. That number depends on how we wrote down the distribution, not on its physical content. Useless.

Strictly, $H_0$ is defined by the outer limit

$$
H_0(p) = \lim_{\alpha \to 0^+} \frac{1}{1-\alpha}\log\sum_i p_i^\alpha.
$$

For a finite outcome set the sum has finitely many terms, so we may take the limit term by term. For $p_i > 0$, $p_i^\alpha \to 1$; for $p_i = 0$, $0^\alpha = 0$ for every $\alpha > 0$. Hence

$$
\sum_i p_i^\alpha \;\longrightarrow\; |\mathrm{supp}(p)|,
$$

and since $\log$ is continuous and $1/(1-\alpha) \to 1$,

$$
H_0(p) = \log|\mathrm{supp}(p)| = \log(\#\text{ of nonzero-probability outcomes}).
$$

This is called the **support entropy**.

This is the same kind of limit convention used to define Shannon entropy, where one writes $0\log 0 := \lim_{p \to 0^+} p\log p = 0$. Boundary cases are *not* arbitrary algebraic conventions — they are forced by continuity.

The crucial feature: **$H_0$ depends only on which outcomes are possible, not on how likely they are**. Once a probability is nonzero, $H_0$ does not care whether it is $0.99$ or $10^{-30}$. That is exactly the feature QIQT-H wants when it asks "how many physically distinguishable records does this state admit?"

Example:

$$
p=(0.99,0.01)
$$

has Shannon entropy small, but Rényi-0 entropy

$$
H_0 = \log 2.
$$

Why? Because two outcomes are possible.

If

$$
p=(0.999999,0.000001),
$$

then Shannon entropy is even smaller, but Rényi-0 is still $\log 2$.

So Rényi-0 asks:

> How many alternatives have nonzero support?

It does not ask how likely they are.

This matters for QIQT-H because a holographic bound is plausibly a bound on distinguishable alternatives, not merely on average surprise.

## 4.5 Hill numbers

Entropy is a logarithmic count. A **Hill number** removes the logarithm.

For a Rényi entropy in nats,

$$
H_q^{\rm nat} = \frac{1}{1-q}\ln\left(\sum_i p_i^q\right),
$$

the corresponding Hill number is

$$
N_q = \exp(H_q^{\rm nat}) = \left(\sum_i p_i^q\right)^{1/(1-q)}.
$$

This is the **effective number of outcomes** — measured in the same units as "number of species" or "number of records."

The Shannon case ($q = 1$) is

$$
N_1 = \exp\left(-\sum_i p_i \ln p_i\right).
$$

In NLP and machine learning this is called the **perplexity**. It says how many equally likely words would produce the same uncertainty as the actual distribution.

The three important cases for us are:

$$
N_0 = |\mathrm{supp}(p)|, \qquad N_1 = \text{perplexity}, \qquad N_\infty = \frac{1}{\max_i p_i}.
$$

Example:

$$
p = (1/2, 1/2) \quad\Longrightarrow\quad N_0 = N_1 = N_\infty = 2.
$$

Example:

$$
p = (0.999, 0.001) \quad\Longrightarrow\quad N_0 = 2,
$$

because both outcomes are possible. But its Shannon effective number is

$$
N_1 \approx 1.008,
$$

close to $1$, because in a typical draw the second outcome is essentially never seen.

This is the natural way to state the holographic bound: it is an inequality on a *count* of records, not on the logarithm of a count.

## 4.6 Smooth support

A problem: in quantum mechanics, tiny amplitudes are everywhere. If every nonzero amplitude counts, then almost everything has enormous or infinite support.

So one uses a **smooth support**.

Instead of counting all outcomes with $p_i>0$, we allow ourselves to ignore a tiny total probability $\varepsilon$.

Define the $\varepsilon$-smooth support size as:

> the smallest number of outcomes whose total probability is at least $1-\varepsilon$.

Example:

$$
p=(0.98,0.01,0.01).
$$

If $\varepsilon=0.03$, then one outcome already captures $0.98$, so

$$
N_0^\varepsilon=1.
$$

If $\varepsilon=0.005$, then we need all three outcomes, so

$$
N_0^\varepsilon=3.
$$

This is useful when tiny tails are physically irrelevant.

QIQT-H often uses a support-like entropy because it wants to count possible records, while smoothing avoids being dominated by absurdly tiny amplitudes.

To summarise the menu: **Shannon and von Neumann** measure average surprise / mixedness — natural for thermodynamics and entanglement, but blind to small-amplitude possibilities. **Rényi-α** lets us slide between possibility-counting ($\alpha \to 0$) and worst-case ($\alpha \to \infty$). **Rényi-0**, sharpened by **smooth support**, is the right tool when we want to ask "how many physically realisable records does this state describe?" That is the entropy the holographic bound naturally constrains.

---

# 5. Zurek’s physical entropy

Wojciech Zurek suggested that physical entropy should include two pieces:

$$
S_{\rm phys} = K(\text{description}) + S_{\rm Boltzmann}.
$$

Here:

- $K(\text{description})$ is the algorithmic complexity of the macroscopic description,
- $S_{\rm Boltzmann}=k_B\log W$ is the entropy of the microstates compatible with that description.

Let’s make this concrete.

## 5.1 Gas in a piston

Suppose you have a gas in a box. A macrostate might be described by:

$$
\text{``Energy''} E, \text{ ``volume''} V, \text{ ``particle number''} N.
$$

That description is short. Its algorithmic complexity is small.

But many microscopic configurations have the same $E,V,N$. The number of compatible microstates is $W$, so

$$
S_{\rm Boltzmann}=k_B\log W.
$$

Now consider a bizarre macro-description:

> “The gas molecules occupy exactly this intricate fractal-shaped subset of phase space.”

That description may have high algorithmic complexity. Even if the residual number of compatible microstates is smaller, the description itself carries information.

So Zurek’s idea is:

> Entropy is not only ignorance within a macrostate. It also includes the information cost of specifying the macrostate.

In QIQT-H, this matters because “records” are not free. A record must be physically describable, storable, and distinguishable.

---

# 6. Decoherence: why classical branches appear

The standard measurement problem involves superpositions of macroscopically distinct states. Decoherence explains why these superpositions become unobservable in practice.

## 6.1 A two-state system coupled to an environment

Let the system have states $|0\rangle, |1\rangle$. Suppose the environment starts in $|E_0\rangle$.

Interaction produces:

$$
(\alpha|0\rangle+\beta|1\rangle)|E_0\rangle
\longrightarrow
\alpha|0\rangle|E_0^{(0)}\rangle
+
\beta|1\rangle|E_0^{(1)}\rangle.
$$

The total density matrix is

$$
\rho_{\rm total}
=
|\Psi\rangle\langle\Psi|.
$$

The reduced density matrix of the system is obtained by tracing over the environment:

$$
\rho_S = \mathrm{Tr}_E(\rho_{\rm total}).
$$

Compute it:

$$
\rho_S
=
|\alpha|^2 |0\rangle\langle 0|
+
|\beta|^2 |1\rangle\langle 1|
+
\alpha\beta^* \langle E_0^{(1)}|E_0^{(0)}\rangle |0\rangle\langle 1|
+
\alpha^*\beta \langle E_0^{(0)}|E_0^{(1)}\rangle |1\rangle\langle 0|.
$$

If

$$
\langle E_0^{(1)}|E_0^{(0)}\rangle \approx 0,
$$

then the off-diagonal terms vanish:

$$
\rho_S \approx
|\alpha|^2 |0\rangle\langle 0|
+
|\beta|^2 |1\rangle\langle 1|.
$$

This looks like a classical mixture.

But remember: the total state is still pure. Decoherence did not collapse the wavefunction. It only made branches stop interfering locally.

## 6.2 Einselection: environment-induced superselection

The environment does not decohere every basis equally. It picks out a preferred basis, called the **pointer basis**.

This is called **einselection**, short for environment-induced superselection.

The rule is simple: the environment monitors the system observable that appears in the interaction Hamiltonian.

### Toy model: monitoring $\sigma_z$

Let

$$
H_{\rm int} = g\,\sigma_z \otimes B_E, \qquad \sigma_z |s\rangle = s\,|s\rangle,
$$

where $g$ is a real coupling constant (units of energy) that sets the strength of the system-environment interaction, $B_E$ is some environment operator, and $|s\rangle$ is either $|0\rangle$ or $|1\rangle$, with $s = \pm 1$.

Evolve an initial product state $|s\rangle|e\rangle$. Since $|s\rangle$ is an eigenstate of $\sigma_z$,

$$
e^{-i H_{\rm int} t / \hbar} |s\rangle|e\rangle
= |s\rangle \otimes e^{-i g s t B_E / \hbar} |e\rangle
\equiv |s\rangle |E_s(t)\rangle.
$$

The system state has not changed. There is no mixing between $|0\rangle$ and $|1\rangle$. Only the environment changes, and it changes in a way that depends on $s$.

That is what "stable under the interaction" means here.

A superposition evolves differently:

$$
(\alpha|0\rangle + \beta|1\rangle)|e\rangle
\longrightarrow
\alpha|0\rangle|E_0(t)\rangle + \beta|1\rangle|E_1(t)\rangle.
$$

The system and environment are now entangled. Once $\langle E_0(t) | E_1(t)\rangle \to 0$ — by the product-of-overlaps mechanism of §2 — the reduced system state is decohered in the $\sigma_z$ basis. So the pointer basis is the $\sigma_z$ eigenbasis.

**Concrete realization: dephasing by bath spins.** Let the environment be a single bath spin and let $B_E = \sigma_z^{(1)}$, so

$$
H_{\rm int} = g\,\sigma_z \otimes \sigma_z^{(1)}.
$$

This is the simplest spin-environment model. Prepare the bath in $|+\rangle_1 = (|0\rangle_1 + |1\rangle_1)/\sqrt{2}$ — a state carrying no initial information about $s$. A short calculation gives

$$
|E_0(t)\rangle = \tfrac{1}{\sqrt{2}}\!\left(e^{-igt/\hbar}|0\rangle_1 + e^{+igt/\hbar}|1\rangle_1\right), \quad
|E_1(t)\rangle = \tfrac{1}{\sqrt{2}}\!\left(e^{+igt/\hbar}|0\rangle_1 + e^{-igt/\hbar}|1\rangle_1\right),
$$

with overlap

$$
\langle E_0(t) | E_1(t)\rangle = \cos\!\left(\frac{2gt}{\hbar}\right).
$$

A single bath spin makes the overlap *oscillate*, never permanently vanishing. Now take $N$ independent bath spins with couplings $g_k$, each in $|+\rangle$. Because the bath factorises, the total overlap is the product of one-spin overlaps:

$$
\langle E_0(t) | E_1(t)\rangle = \prod_{k=1}^N \cos\!\left(\frac{2 g_k t}{\hbar}\right).
$$

For generic incommensurate $g_k$ and large $N$ this drops to essentially zero almost immediately and stays there — the dephasing version of the product formula from §2. Decoherence in the $\sigma_z$ basis is just many bath spins independently dephasing the system superposition.

The standard criterion says the same thing in one line. **Pointer states are eigenstates of any system observable $A$ that commutes with the system part of the interaction**:

$$
[A, H_{\rm int}^{(S)}] = 0.
$$

If this holds, eigenstates of $A$ evolve without intra-basis mixing. The environment may record *which* eigenstate is present, but it does not rotate one pointer state into another.

For the model above, $H_{\rm int}^{(S)} = \sigma_z$, so the pointer states are $\sigma_z$ eigenstates. If instead

$$
H_{\rm int} = g\,\sigma_x \otimes B_E,
$$

then the commuting observable is $\sigma_x$, and the pointer basis is the $\sigma_x$ eigenbasis.

In real measurements, the pointer basis is almost always **position-like**: macroscopic pointer positions, detector currents, cloud-chamber tracks, spots on a screen. The reason is that most physical interactions are local in position — scattering, electromagnetic coupling, mass-density coupling all depend on *where* things are. So position commutes (approximately) with the interaction Hamiltonian, and position eigenstates are the natural pointer states.

Pointer states are not magical. They are the states that the system-environment interaction monitors.

## 6.3 Quantum Darwinism

Quantum Darwinism asks:

> Why do many observers agree on the same classical facts?

Zurek’s answer: because information about pointer states is redundantly copied into many fragments of the environment.

Example: a dust grain in sunlight.

A photon scatters off the dust particle. The outgoing photon carries information about the particle’s position. Many photons scatter, and each carries partial information.

So the environment becomes a communication channel:

$$
\text{dust position}
\longrightarrow
\text{many scattered photons}.
$$

Different observers can intercept different photons and infer the same position without disturbing the dust grain.

This is redundancy.

Schematically:

$$
|x\rangle |E_0\rangle
\longrightarrow
|x\rangle |E_x^{(1)}\rangle |E_x^{(2)}\rangle \cdots |E_x^{(N)}\rangle.
$$

Each fragment $E^{(k)}$ contains information about $x$.

## 6.4 Spectrum broadcast structure

A strong form of Quantum Darwinism is called **spectrum broadcast structure**.

A state has this structure if it looks like

$$
\rho_{S E_1 \cdots E_N}
=
\sum_i p_i |i\rangle\langle i|_S
\otimes \rho_i^{E_1}
\otimes \rho_i^{E_2}
\otimes \cdots
\otimes \rho_i^{E_N},
$$

with the environment fragment states distinguishable:

$$
\rho_i^{E_k}\rho_j^{E_k}=0
\quad
\text{for } i\neq j.
$$

This means:

- the system is classically in one of the pointer states $i$,
- each environment fragment contains a readable record of $i$,
- different observers can independently learn $i$.

This is the mathematical form of objective classical facts emerging from quantum mechanics.

---

# 7. Decoherent histories

The decoherent histories framework is a way to talk about whole sequences of events without assuming measurements at each time.

## 7.1 What is a history?

A history is a sequence of alternatives at different times.

Example:

At time $t_1$, the particle is in region $A$ or $B$.

At time $t_2$, it is in region $C$ or $D$.

A possible history is:

$$
A \text{ at } t_1,\quad C \text{ at } t_2.
$$

In quantum mechanics, alternatives are represented by projection operators.

Let

$$
P_A(t_1),\quad P_C(t_2)
$$

be Heisenberg-picture projectors. Then the class operator for the history $h=(A,C)$ is

$$
C_h = P_C(t_2)P_A(t_1).
$$

For longer histories,

$$
C_h=P_{i_n}(t_n)\cdots P_{i_2}(t_2)P_{i_1}(t_1).
$$

## 7.2 The decoherence functional

Given initial state $\rho$, define

$$
D(h,h')=\mathrm{Tr}(C_h \rho C_{h'}^\dagger).
$$

This is called the decoherence functional.

The diagonal elements

$$
D(h,h)
$$

are candidate probabilities.

But probabilities only make sense if histories do not interfere. That requires off-diagonal terms to vanish approximately:

$$
D(h,h')\approx 0
\quad
\text{for } h\neq h'.
$$

This condition is called decoherence of histories.

## 7.3 Medium decoherence

A set of histories is medium decoherent if

$$
D(h,h')\approx 0
\quad
\text{for } h\neq h'.
$$

Then the probabilities

$$
p(h)=D(h,h)
$$

obey ordinary probability rules.

For example, if history $h$ is the union of two alternatives $h_1,h_2$, then

$$
p(h)=p(h_1)+p(h_2)
$$

provided interference vanishes.

## 7.4 Two-slit example

In the two-slit experiment, histories are:

- particle went through slit 1 and arrived at screen point $x$,
- particle went through slit 2 and arrived at screen point $x$.

If no environment records which slit, the two histories interfere:

$$
D(1,x;2,x)\neq 0.
$$

You cannot assign classical probabilities to “went through slit 1” and “went through slit 2.”

If a detector records the slit, the environment states become orthogonal:

$$
|E_1\rangle,\quad |E_2\rangle,
\qquad
\langle E_1|E_2\rangle\approx 0.
$$

Then

$$
D(1,x;2,x)\approx 0.
$$

Now the histories decohere, and you can assign probabilities.

## 7.5 Why QIQT-H likes histories

Measurements are not instantaneous magic. They are physical processes extended in time.

QIQT-H uses decoherent histories because its fundamental constraint is not simply on states at an instant. It is on possible **recorded histories** inside a causal region.

A record is evidence that a history occurred.

---

# 8. The QIQT-H central postulate, schematically

Now we can state the central idea in a clean but schematic form.

Consider a causal region $D$, such as the region accessible to an observer between two times. Let $\partial D$ be its boundary.

QIQT-H says:

> The physically admissible decoherent histories in $D$ are constrained by a holographic information budget.

A schematic version is

$$
I_{\rm branch}^{\varepsilon}(D)
\;\leq\;
S_{\rm gen}(\partial D).
$$

Here:

- $I_{\rm branch}^{\varepsilon}(D)$ is a smoothed support-like entropy counting distinguishable records across decoherent branches in the region,
- $S_{\rm gen}(\partial D)$ is the generalized entropy associated with the boundary.

The generalized entropy is

$$
S_{\rm gen}
=
\frac{A}{4G\hbar}
+
S_{\rm matter}^{\rm ren}.
$$

We will explain this later.

For now, the interpretation is:

> The number of physically distinguishable recorded alternatives cannot exceed the holographic entropy budget.

Equivalently, if a formal quantum state contains more branch-record alternatives than can fit in the region, not all of those alternatives are jointly admissible as physical records.

## 8.1 Branch-summed rather than branch-by-branch

This is crucial.

The constraint is not:

> Each branch individually must fit.

That would be weak.

Instead, it is:

> The total set of distinguishable branch records available in the region must fit.

This is called a **branch-summed constraint**.

Suppose a measurement produces $N$ distinguishable possible records. A support entropy would be

$$
I_{\rm branch}\sim \log N.
$$

The holographic bound says

$$
\log N \leq S_{\rm gen}.
$$

With smoothing,

$$
\log N^\varepsilon_{\rm eff}\leq S_{\rm gen}.
$$

So very tiny-amplitude alternatives may be ignored up to tolerance $\varepsilon$, but robust recorded alternatives count.

## 8.2 Probabilities

Given a decoherent family of histories $\{h\}$, ordinary quantum mechanics assigns weights

$$
w(h)=D(h,h).
$$

QIQT-H keeps these weights but restricts to admissible histories.

For an admissible family $\mathcal{H}_{\rm adm}$,

$$
P(h)
=
\frac{w(h)}{\sum_{h'\in \mathcal{H}_{\rm adm}} w(h')}.
$$

If the admissible set contains essentially all Born-weight-relevant histories, this reduces to ordinary quantum mechanics.

**Caveat.** This renormalization formula is only consistent if the admissibility rule $\mathcal{H}_{\rm adm}$ is stable under coarse-graining and compatible with causal localization. A naive global-budget formulation would *fail* — it would let a distant experimenter's choice affect a local experimenter's marginal probabilities. The framework's resolution is the **modular-local reformulation** of §8.4 below: admissibility is imposed on each region separately, not as a joint cap. Under that reformulation no-signaling is automatic (§8.4 makes this precise).

Born-weight equivariance — the statement that the renormalized weights still reduce to $|c_k|^2$ under admissibility conditioning — is the framework's remaining major open problem (analogous to Bohmian $|\psi|^2$-equivariance, §22). In ordinary laboratory regimes where the bound is far from saturation, the equivariance holds trivially because the admissibility predicate is vacuous and $P_{\rm QIQT}(h) = w(h)$ exactly.

## 8.3 Why this might help the measurement problem

Decoherence explains why branches stop interfering. QIQT-H adds:

> Not every formal decohered branch can be promoted to an independent physical record if doing so would exceed the holographic information budget.

Thus, definite outcomes are tied to the finite capacity of physical record-keeping.

The hope is to get:

- no explicit collapse law,
- no many-worlds ontology with arbitrarily many equally real recorded branches,
- no Bohmian particle trajectories,
- ordinary quantum predictions in normal experiments,
- new constraints when gravitational entropy bounds matter.

**Why ordinary lab measurements don't immediately violate the bound — and what this exposes.** A natural worry: a single lab does thousands of measurements per second; surely these would quickly violate any branch-summed bound? The answer is that the area term $A/(4G\hbar)$ for a one-meter region is fantastically large — of order $10^{69}$–$10^{70}$ in natural units. Ordinary laboratory records occupy a negligible fraction of this capacity. Therefore QIQT-H, if correct, must reproduce standard quantum mechanics in ordinary non-gravitational laboratory regimes — the constraint is operationally vacuous there.

**However, this also exposes an important open issue.** If the holographic constraint is far from saturation in ordinary measurements, then the constraint alone does not by itself select a unique laboratory outcome. An ordinary Stern-Gerlach measurement would still have, in principle, an admissible multi-record decohered structure within the bound — yet experimentally one observes one outcome. QIQT-H must therefore explain definite ordinary outcomes through *some additional global admissibility of record histories*, not through simple local saturation of the holographic budget. Making that global selection rule precise is one of the framework's central open problems (see §28).

The honest picture: the Branch-Summed Bound predicts a definite quantum-to-classical *boundary scale*, above which multi-record structures are kinematically excluded. Below that scale, the bound is operationally vacuous, and the framework needs an additional global admissibility mechanism to recover ordinary single-outcome experience. The current research program proposes the bound but does not yet supply the global mechanism. The tutorial should be read with this caveat throughout.

## 8.4 The modular-local reformulation (why no-signaling works)

The "branch-summed" picture above is intuitive, but as stated it has a subtle problem. When Alice and Bob measure entangled particles at spacelike separation and their records are later compared in a *joint region* $D_{AB}$, the joint region has its own holographic budget. If the branch-summed cost in $D_{AB}$ is treated as "Alice's record bits + Bob's record bits", then Bob's choice of measurement can in principle affect how much budget is available for Alice's outcomes — and Alice would see her marginal statistics shift depending on what Bob did. That is **superluminal signaling**, which relativity forbids.

A concrete Bell-style example confirms the worry: with asymmetric record costs and a hard joint cutoff, one can compute

$$
P_{\rm QIQT}(\text{Alice}=+ \mid x, y) = \frac{2}{3 + \cos\theta_{xy}},
$$

which depends on Bob's setting $y$. So the naive formulation as stated is *inconsistent with relativity*.

The fix is structural. Instead of "count records in each region and bound the count", state the constraint as a bound on the **regional relative entropy** — a quantity already well-defined for Type III local QFT algebras via Araki / Connes machinery:

$$
\chi_R(\omega) := S_{\hat{\mathcal{A}}(R)}(\omega_R \,\|\, \Omega_R) \;\le\; C(R) = \frac{A(\partial R)}{4G\hbar}.
$$

Here $\chi_R(\omega)$ measures how complicated the regional state $\omega_R$ is compared to a reference state $\Omega_R$ (typically the vacuum), evaluated *intrinsically* on the regional algebra. It is finite, basis-independent, and well-defined even when the algebra is Type III (no density-matrix factorization needed).

For two spacelike-separated regions $D_A$ and $D_B$, admissibility is the **meet of local predicates**:

$$
\mathrm{Adm}(D_A \cup D_B) \;=\; \mathrm{Adm}(D_A) \;\text{AND}\; \mathrm{Adm}(D_B).
$$

That is: a state is admissible on the spacelike pair iff its restriction to *each* local algebra is admissible. **No joint cutoff is applied to the combined algebra $\hat{\mathcal{A}}(D_A) \vee \hat{\mathcal{A}}(D_B)$.** The vacuum may remain entangled across the spacelike boundary — the framework doesn't try to disentangle it; it simply asks that each region's *local* relative entropy be below its *local* capacity.

### Why this gives no-signaling automatically

In algebraic QFT, the algebras of spacelike-separated regions commute:

$$
[\hat{\mathcal{A}}(D_A), \hat{\mathcal{A}}(D_B)] = 0.
$$

This is **microcausality** — the bedrock principle that spacelike operations cannot interfere with each other. From microcausality plus the modular-local form of the bound, Alice's marginal probability is independent of Bob's setting in one line:

If Bob performs an instrument $\{\Psi_b^y\}$ in $D_B$ with the *summed* operation $\Psi^y = \sum_b \Psi_b^y$ (i.e., we don't record Bob's outcome), then by microcausality $\Psi^y$ acts as the identity on Alice's algebra. Therefore Alice's outcome effect $E_a^x \in \hat{\mathcal{A}}(D_A)$ gives

$$
P_{\rm QIQT}(a \mid x, y) = \omega(\Psi^{y*}(E_a^x)) = \omega(E_a^x),
$$

independent of $y$. The admissibility predicate cannot break this, because Alice's local admissibility depends only on her local state restriction, which Bob's non-selective operation does not touch.

**No-signaling is now a one-line theorem**, not an extra axiom and not an approximation. The framework was *forced* into this modular-local form by the no-signaling constraint, and the fact that the constraint forces such a clean algebraic reformulation is itself evidence that this is the right structure.

### What survives from the branch-counting picture

The branch-counting language ($I_\Sigma^\varepsilon$, $I_0$, $N \le Q_R/I_0$) doesn't disappear. When a regional state is a classical mixture of decoherent macroscopic records (which is what measurement produces, after §6's einselection and Quantum Darwinism do their work), the regional relative entropy *reduces* to a sum:

$$
\chi_R(\omega_{\rm classical\;mixture}) \;\approx\; \sum_r p_r\, c_R(r) + H_{\rm Shannon}(\{p_r\}),
$$

where $c_R(r)$ is the per-record relative entropy. So "branch-summed cost" becomes a *derived approximation* of the modular-local bound in the classical-mixture regime — useful for operational calibration ($I_0$ as an empirical parameter, predicting the Schrödinger-cat scale, designing macroscopic-superposition experiments) but no longer the *fundamental* statement of the bound.

The fundamental statement is algebraic. The branch-counting picture is the right intuitive handle in the appropriate regime.

### Why this respects the boundary entanglement

In QFT, the vacuum is wildly entangled across every spatial boundary. Two regions sharing a boundary share entangled vacuum modes; the regions are not independent universes. This is the deep reason local algebras are Type III.

The modular-local approach handles this correctly. $\chi_R$ is *defined* on the regional algebra including its boundary structure — it already accounts for the boundary entanglement that's always there. What the framework explicitly *avoids* is trying to compute a joint relative entropy across the boundary, which would re-couple the two regions and re-introduce signaling. Relative entropy is used locally only; spacelike combination is by meet.

### Summary

| Original (branch-summed) | Reformulated (modular-local) |
|---|---|
| Count records in $R$, bound the count by $Q_R/I_0$ | Bound regional relative entropy $\chi_R(\omega)$ by $C(R)$ |
| Spacelike regions combined by joint-budget cap (dangerous) | Spacelike regions combined by meet of local predicates (safe) |
| No-signaling: open problem | No-signaling: one-line theorem from microcausality |
| Fundamental object: support count | Fundamental object: algebra-state pair |
| Branch counting is the rule | Branch counting is a derived approximation in the classical-mixture regime |

The modular-local reformulation is the framework's response to the no-signaling constraint — and it produces a more elegant, more mathematically clean version of the same physical idea.

## 8.5 Four technical commitments the framework makes

The modular-local reformulation forces four concrete commitments that deserve to be stated explicitly. Each is a refinement of an earlier informal statement.

**1. The physical state space is not a Hilbert subspace, and it is *stagewise*, not global.** Under the modular-local bound, admissibility is imposed at each process stage on the regions that are *causally instantiated* at that stage:

$$
\mathcal{S}_{\rm phys}(t, h) = \{ \omega_t^h : \chi_R((\omega_t^h)_R) \le C(R) \text{ for every } R \in \mathfrak{R}_t(h) \},
$$

where $\mathfrak{R}_t(h)$ collects the bounded diamonds available to the framework on branch $h$ at stage $t$ — past records and the regions causally downstream of them. There is no single global admissibility list applied for all time; constraints come into force as their regions are physically instantiated. The Hilbert-space picture $\mathcal{H}_{\rm phys}$ is recovered only as equivalence classes of representatives inducing the same regional states. The constraint is *nonlinear* in the Hilbert vector, and there is no projector onto $\mathcal{H}_{\rm phys}$.

**2. Macroscopic definiteness is "effective" on the *normalized active set*, not literal.** The earlier "$N$ records fit iff $N \cdot I_0 \le Q_R$" argument is replaced by an effective-entropy bound on the normalized active distribution $\tilde p_k = p_k/q$ (where $q = \sum_{k \in \mathcal{A}_\epsilon} p_k$ is the active-set total weight):

$$
H_\epsilon := -\sum_k \tilde p_k \log \tilde p_k \;\le\; C(R) - I_0 + 2\eta_\epsilon, \qquad N^{(\epsilon)}_{\rm eff} := \exp H_\epsilon.
$$

Single-record-per-run is **exact only at exact saturation** $I_0 = C(R)$ and $\eta_\epsilon = 0$. At finite $\eta_\epsilon$, the conclusion weakens to $H_\epsilon \le 2\eta_\epsilon$ — a single record dominates with probability $\ge 1 - O(\eta_\epsilon)$. The framework is honest that this is a *probabilistic concentration* on a small effective set, not a sharp kinematic exclusion of all multi-record states.

**3. Instruments must be branchwise admissibility-preserving.** A measurement instrument $\{\Phi_a\}$ is physical only if *every* normalized post-outcome state $\omega_a = \omega \circ \Phi_a^* / p_a$ is admissible — not just the non-selective average. Precisely: the outcome is localized in a bounded diamond $O_a$, and $\omega_a$ must satisfy $\chi_R((\omega_a)_R) \le C(R)$ for every bounded $R \Subset J^+(O_a)$ that has been causally instantiated at the relevant stage. A measurement could in principle preserve admissibility on average while one branch violates it; the framework forbids this.

**4. Admissibility applies causally, never retroactively.** When a joint future diamond $D_{AB}$ contains both Alice's and Bob's records, $D_{AB}$ has its own capacity $C(D_{AB})$ that constrains the *future joint state* on $\hat{\mathcal{A}}(D_{AB})$ **once $D_{AB}$ is causally instantiated**. The constraint **does not** retroactively delete or reweight Alice's or Bob's past separately-admissible branches. Without this clause, the framework would smuggle in postselection signaling through future joint conditions.

These four commitments turn the framework's working informal description into a *specifically constrained* algebraic theory. They are the price of having the modular-local refactor close the no-signaling loophole properly.

### A small numerical update

The earlier estimate that QIQT-H deviations from Born probabilities at lab scale are below $\sim 10^{-24}$ used a Bekenstein cap on branch counts. The modular-local form gives the deviation directly via Markov:

$$
\delta_R \le \frac{\mathbb{E}[\chi_R]}{C(R)} \lesssim \frac{2\pi L \, E_R / (\hbar c)}{A(\partial R)/(4 \ell_P^2)}.
$$

For $L \sim 1\,\mathrm{m}$ and $E_R \sim 1\,\mathrm{kg}\,c^2$, the numerator is $\sim 2 \times 10^{43}$ nats and the denominator $\sim 10^{70}$ nats, giving the **conditional** order-of-magnitude estimate $\delta_R \lesssim 10^{-27}$. Operationally invisible — but importantly, the bound is now **region- and energy-dependent**, not a universal constant. Larger or more energetic regions have different deviations.

The estimate is *conditional* because the modular-energy bound $\Delta\langle K_R^\sigma\rangle \lesssim 2\pi L E_R/(\hbar c)$ is exact only for two special cases — Rindler wedges (Bisognano-Wichmann theorem) and balls in a CFT vacuum (conformal modular Hamiltonian). For generic ball-shaped regions in flat-spacetime QFT, the bound is obtained by enclosing-wedge monotonicity of relative entropy. The $\chi_R \le \Delta\langle K_R^\sigma\rangle$ step further assumes a non-negative entropy shift $\Delta S_R \ge 0$. So $10^{-27}$ is a textbook-style heuristic, not a generic QFT theorem. The framework's main point — that operational signaling is *vanishingly small* under these standard hypotheses — survives.

---

# 9. Why operator algebras enter at all

In ordinary undergraduate QM, we start with a Hilbert space $\mathcal{H}$. Observables are Hermitian operators on $\mathcal{H}$.

For a finite-dimensional system, all operators are matrices.

Example: for one qubit,

$$
\mathcal{H}=\mathbb{C}^2,
$$

and observables are $2\times 2$ Hermitian matrices.

The full algebra of operators is

$$
M_2(\mathbb{C}).
$$

For two qubits,

$$
\mathcal{H}=\mathbb{C}^2\otimes \mathbb{C}^2,
$$

and the full algebra is

$$
M_4(\mathbb{C}).
$$

So far, everything is simple.

But QFT and gravity force us to think more carefully.

In QFT, the degrees of freedom are spread over spacetime regions. We often care about the observables localized in a region $O$. So we associate an algebra

$$
\mathcal{A}(O)
$$

to each spacetime region $O$.

This is the algebraic viewpoint:

> Instead of starting with particles, start with observables associated to regions.

This is useful because:

- particle number can be observer-dependent in curved spacetime,
- local fields are distributions, not ordinary operators at points,
- entanglement across spatial boundaries is UV-divergent,
- gravitational subregions are subtle.

The algebras that appear are often not just finite matrices. They are von Neumann algebras.

---

# 10. Von Neumann algebras from matrices upward

## 10.1 What is an algebra of observables?

An algebra is a set of operators closed under:

- addition,
- multiplication,
- scalar multiplication,
- adjoint $A\mapsto A^\dagger$,
- limits of suitable sequences.

In finite dimensions, an algebra is just a set of matrices closed under those operations.

Example:

All $2\times 2$ matrices:

$$
M_2(\mathbb{C}).
$$

Example:

All diagonal $2\times 2$ matrices:

$$
\left\{
\begin{pmatrix}
a & 0\\
0 & b
\end{pmatrix}
: a,b\in\mathbb{C}
\right\}.
$$

This diagonal algebra is commutative. It behaves like classical observables for a two-outcome system.

## 10.2 The commutant

Given an algebra $\mathcal{A}$, its commutant $\mathcal{A}'$ is the set of all operators that commute with every operator in $\mathcal{A}$:

$$
\mathcal{A}'=\{B:[A,B]=0\text{ for all }A\in\mathcal{A}\}.
$$

Example:

If $\mathcal{A}=M_n(\mathbb{C})$ acting on $\mathbb{C}^n$, then the only matrices commuting with all matrices are multiples of the identity:

$$
\mathcal{A}'=\mathbb{C}I.
$$

Example:

If $\mathcal{A}$ is all diagonal $2\times 2$ matrices, then $\mathcal{A}'$ is also all diagonal $2\times 2$ matrices.

## 10.3 Von Neumann algebra

A von Neumann algebra is an operator algebra satisfying

$$
\mathcal{A}=\mathcal{A}''.
$$

That is, it equals its double commutant.

In finite dimensions, this condition is not mysterious. Most familiar matrix algebras of observables are von Neumann algebras.

The reason the definition matters is that in infinite dimensions, taking limits becomes subtle. The double-commutant condition captures the idea that the algebra is closed under physically relevant limiting operations.

---

# 11. Factors and the Type I/II/III classification

Von Neumann algebras are classified into Types I, II, and III.

This classification is one of the most enigmatic things for physics students, so let’s build it carefully.

## 11.1 The center

The center of an algebra $\mathcal{A}$ is

$$
Z(\mathcal{A})=\{A\in\mathcal{A}:[A,B]=0\text{ for all }B\in\mathcal{A}\}.
$$

If the center is just multiples of the identity,

$$
Z(\mathcal{A})=\mathbb{C}I,
$$

then $\mathcal{A}$ is called a **factor**.

A factor is an algebra with no classical superselection label sitting inside it.

Example:

$$
M_n(\mathbb{C})
$$

is a factor.

The diagonal algebra is not a factor because every diagonal matrix commutes with every other diagonal matrix.

The Type classification classifies factors.

---

## 11.2 Type I: ordinary quantum mechanics

Type I factors are the familiar ones:

$$
\mathcal{A}=B(\mathcal{H}),
$$

the algebra of all bounded operators on a Hilbert space.

Finite-dimensional example:

$$
M_n(\mathbb{C}).
$$

This is ordinary quantum mechanics.

Type I algebras have minimal projections.

A projection is an operator $P$ satisfying

$$
P^2=P,\qquad P^\dagger=P.
$$

It represents a yes/no question.

In $M_n(\mathbb{C})$, a one-dimensional projector

$$
P=|\psi\rangle\langle\psi|
$$

is minimal: it cannot be decomposed into smaller nonzero projections.

So Type I algebras have atoms, like individual basis states.

This is the world of undergraduate QM.

---

## 11.3 Type II: continuous dimension

Type II factors are stranger.

They have no minimal projections, but they still have a trace.

A trace is a function $\tau$ satisfying

$$
\tau(AB)=\tau(BA),
$$

like the ordinary matrix trace.

For a Type II$_1$ factor, the trace is finite and normalized:

$$
\tau(I)=1.
$$

The surprising part is that projections can have any continuous size between 0 and 1.

For ordinary matrices $M_n$, projection ranks are discrete:

$$
\mathrm{rank}(P)=0,1,2,\dots,n.
$$

The normalized trace gives

$$
\frac{\mathrm{rank}(P)}{n}
=
0,\frac{1}{n},\frac{2}{n},\dots,1.
$$

Only discrete values.

In a Type II$_1$ factor, projections can have trace

$$
\tau(P)=r
$$

for any real number $0\leq r\leq 1$.

That is why von Neumann described Type II algebras as having **continuous dimension**.

### Toy model intuition: infinite spin chain limit

Take $N$ qubits.

The algebra is

$$
M_{2^N}(\mathbb{C}).
$$

The normalized trace of a projection can be

$$
0,\frac{1}{2^N},\frac{2}{2^N},\dots,1.
$$

As $N\to\infty$, the spacing between possible trace values goes to zero.

A Type II$_1$ factor is morally like the infinite limit of such matrix algebras, where the possible projection sizes become continuous.

This is not a complete construction, but it gives the right intuition.

Type II factors are important because they are infinite-dimensional but still have a good trace. Entropy can be defined using that trace.

### Type II$_1$ vs Type II$_\infty$ — an important distinction

There are actually **two species** of Type II factors:

- **Type II$_1$**: finite normalized trace, $\tau(\mathbf{1}) = 1$. All projections have $\tau(P) \in [0, 1]$. Like the "infinite spin chain limit" picture above.

- **Type II$_\infty$**: *semifinite* trace, with $\tau(\mathbf{1}) = \infty$. Projections can have any nonnegative real trace, including infinite. Think of it as Type II$_1$ tensored with an infinite-dimensional Type I piece — $\mathcal{A}_{\rm II_\infty} \cong \mathcal{A}_{\rm II_1} \otimes B(\mathcal{H}_\infty)$.

This distinction matters later. When we form the crossed product of a Type III algebra with its modular flow (§17), the result (the "continuous core") is generically Type II$_\infty$, not Type II$_1$. The trace is still semifinite — well-defined, satisfying $\tau(AB) = \tau(BA)$ — but the identity has infinite trace. So you can compute trace-like quantities, but $S = -\tau(\rho \log \rho)$ may not be automatically finite without further regularization.

In the de Sitter static-patch construction of CLPW 2022, the observer algebra can become Type II$_1$, reflecting the finite entropy of the cosmological horizon. One has to be careful with normalization here: with the normalized Type II$_1$ trace $\tau(\mathbf{1}) = 1$, the maximally mixed (tracial) state has $S = -\tau(\mathbf{1} \log \mathbf{1}) = 0$, and smaller-support states have negative entropy. This is mathematically fine but physically nonintuitive — the physical de Sitter horizon entropy $A/(4G\hbar)$ appears as an additive *gravitational normalization constant* relative to this convention, not literally as $\log \tau(\mathbf{1})$. So the Type II$_1$ structure encodes a finite-entropy state space (which is the important physics), but the numerical horizon entropy requires restoring the gravitational normalization. This is the cleanest example of Type II$_1$ structure in semiclassical gravity in the literature.

---

## 11.4 Type III: the QFT case

Type III factors are the weird ones.

They have:

- no minimal projections,
- no finite trace,
- no ordinary density matrices for local regions,
- no clean tensor factorization into “inside” and “outside.”

These appear naturally in relativistic QFT.

If $O$ is a bounded spacetime region, the local algebra $\mathcal{A}(O)$ is usually Type III.

This is not an exotic exception. It is the generic case.

## 11.5 Why QFT gives Type III algebras

In ordinary QM, if a system splits into two parts,

$$
\mathcal{H}=\mathcal{H}_A\otimes\mathcal{H}_B,
$$

then the observables in $A$ are

$$
B(\mathcal{H}_A)\otimes I_B.
$$

That is Type I.

But in continuum QFT, the vacuum is entangled across every spatial boundary at arbitrarily short distances.

There is no exact factorization

$$
\mathcal{H}_{\rm total}
\neq
\mathcal{H}_{\rm inside}\otimes \mathcal{H}_{\rm outside}
$$

in the naive way.

A region's algebra is therefore not $B(\mathcal{H}_{\rm inside})$. It is Type III.

The divergence of entanglement entropy is one symptom of this.

**Caveat — the split property.** Sharp-boundary factorization fails, but an *approximate* factorization is often available if you leave a small buffer region between inside and outside. For nice QFTs (those satisfying the "split property" of Doplicher-Longo), the algebras for $R$ and for the complement-of-a-slight-enlargement-of-$R$ can be embedded in a Type I factor structure. So Type III is the exact mathematical fact about sharp regions, but Type I factorizations are recoverable in the limit of nonzero buffer width. The Bekenstein-Bousso bound is naturally formulated for the sharp region (Type III) case; the framework's machinery is built for that.

---

# 12. Why QFT vacuum entanglement diverges at boundaries

Let’s use a simple example: a 1+1 dimensional conformal field theory on a line.

Consider an interval of length $L$, with UV cutoff $\epsilon$. The vacuum entanglement entropy of the interval is

$$
S(L)\sim \frac{c}{3}\log\frac{L}{\epsilon},
$$

where $c$ is the central charge.

For a half-line with an IR cutoff $L$, one often gets

$$
S_{\rm half-line}\sim \frac{c}{6}\log\frac{L}{\epsilon}.
$$

As $\epsilon\to 0$,

$$
S\to \infty.
$$

Why?

Because field modes on opposite sides of the boundary are entangled at all wavelengths. Near the boundary, there are correlations at arbitrarily short distances.

A rough counting argument:

- divide space into lattice sites of spacing $\epsilon$,
- degrees of freedom just across the boundary are entangled,
- every scale contributes some amount,
- the number of scales between $\epsilon$ and $L$ is

$$
\log\frac{L}{\epsilon}.
$$

So entropy grows logarithmically in 1+1 dimensions.

In higher dimensions, the leading divergence is usually an area law:

$$
S\sim \alpha \frac{\mathrm{Area}}{\epsilon^{d-2}}+\cdots.
$$

This divergence is not merely a calculational nuisance. It reflects the Type III nature of local QFT algebras.

---

# 13. Cyclic and separating vectors

Modular theory begins with two strange words: cyclic and separating.

Let $\mathcal{A}$ be an algebra acting on a Hilbert space $\mathcal{H}$, and let $|\Omega\rangle$ be a vector.

## 13.1 Cyclic

$|\Omega\rangle$ is cyclic for $\mathcal{A}$ if applying operators in $\mathcal{A}$ to it generates a dense set of states:

$$
\{A|\Omega\rangle:A\in\mathcal{A}\}
$$

spans the Hilbert space.

Finite-dimensional translation:

> By acting on $|\Omega\rangle$ with observables in $\mathcal{A}$, you can reach any vector.

## 13.2 Separating

$|\Omega\rangle$ is separating for $\mathcal{A}$ if

$$
A|\Omega\rangle=0
\quad\Rightarrow\quad
A=0.
$$

In words:

> No nonzero operator in the algebra kills $|\Omega\rangle$.

## 13.3 Toy example with two qubits

Let

$$
\mathcal{H}=\mathbb{C}^2_L\otimes \mathbb{C}^2_R.
$$

Let the algebra be operators on the left qubit:

$$
\mathcal{A}=B(\mathbb{C}^2_L)\otimes I_R.
$$

Consider the entangled state

$$
|\Omega\rangle
=
\sqrt{p}|0\rangle_L|0\rangle_R
+
\sqrt{1-p}|1\rangle_L|1\rangle_R,
$$

with $0<p<1$.

This state has full Schmidt rank.

Acting with arbitrary left operators can generate any state of the form

$$
a|0\rangle_L|0\rangle_R
+
b|1\rangle_L|0\rangle_R
+
c|0\rangle_L|1\rangle_R
+
d|1\rangle_L|1\rangle_R?
$$

Actually, left operators cannot change the right basis labels directly, but because the state is entangled, left operators acting on the two Schmidt components generate the full two-qubit space when the Schmidt ranks match.

More explicitly, choose left operators like

$$
|0\rangle\langle0|,\quad |1\rangle\langle0|,\quad |0\rangle\langle1|,\quad |1\rangle\langle1|.
$$

Acting on $|\Omega\rangle$, these produce vectors proportional to

$$
|0\rangle_L|0\rangle_R,\quad
|1\rangle_L|0\rangle_R,\quad
|0\rangle_L|1\rangle_R,\quad
|1\rangle_L|1\rangle_R.
$$

So $|\Omega\rangle$ is cyclic.

It is also separating. If

$$
(A_L\otimes I_R)|\Omega\rangle=0,
$$

then because both Schmidt coefficients are nonzero, $A_L$ must annihilate a basis of $\mathbb{C}^2_L$, so $A_L=0$.

## 13.4 Why this matters in QFT

The Reeh-Schlieder theorem says that the QFT vacuum is cyclic and separating for local algebras associated with suitable spacetime regions.

That sounds bizarre:

> By acting only with operators in one small region, you can approximate any state.

This does not mean you can send signals faster than light. The required operators are generally extremely non-unitary and physically unrealistic. But mathematically it expresses the enormous entanglement of the vacuum.

Cyclic and separating vectors are precisely the setup needed for Tomita-Takesaki modular theory.

---

# 14. Tomita-Takesaki modular theory from matrices

Tomita-Takesaki theory sounds forbidding. Let’s start with finite matrices.

## 14.1 The finite-dimensional problem

Suppose we have an algebra of observables $\mathcal{A}$ and a state $\omega$.

In finite-dimensional QM, a state is represented by a density matrix $\rho$:

$$
\omega(A)=\mathrm{Tr}(\rho A).
$$

If $\rho$ is full rank, then it has no zero eigenvalues.

The modular theory associated with $(\mathcal{A},\omega)$ gives a canonical “flow” of the algebra:

$$
\sigma_t^\omega(A).
$$

In the simplest finite-dimensional case — when $\mathcal{A} = B(\mathcal{H})$ is the full matrix algebra and $\omega(A) = \mathrm{Tr}(\rho A)$ with $\rho$ a faithful density matrix — this flow is

$$
\sigma_t^\omega(A)
=
\rho^{it} A \rho^{-it}.
$$

That is the key formula in this special case.

**Important caveat.** This simple "conjugate by $\rho^{it}$" formula is *only* exact for the full matrix algebra $B(\mathcal{H})$. For a proper subalgebra $\mathcal{A} \subset B(\mathcal{H})$ — and crucially for Type III algebras in QFT — the modular flow is associated with the *algebra-state pair* $(\mathcal{A}, \Omega)$ and is **not** generally obtained by conjugating with a global density matrix. The intuition "$\rho^{it}$ generates the flow" survives in form (with $\rho$ replaced by the modular operator $\Delta_\Omega$), but the global-density-matrix picture breaks down.

It says, in the simplest case:

> The state $\rho$ defines an intrinsic time evolution on the algebra by conjugation with $\rho^{it}$.

Because

$$
\rho^{it}=e^{it\log\rho},
$$

the generator is

$$
K_\omega=-\log\rho,
$$

called the modular Hamiltonian.

Then

$$
\sigma_t^\omega(A)
=
e^{-itK_\omega}A e^{itK_\omega}
$$

up to sign conventions.

## 14.2 What is the modular Hamiltonian?

If

$$
\rho=\frac{e^{-\beta H}}{Z},
$$

then

$$
K_\omega=-\log\rho
=
\beta H+\log Z.
$$

The constant $\log Z$ commutes with everything, so it does not affect the flow.

Then

$$
\sigma_t^\omega(A)
=
e^{-i\beta H t} A e^{i\beta H t}.
$$

So for a thermal state, modular flow is ordinary time evolution, but with time rescaled by $\beta$.

This is a key physical idea:

> Modular flow generalizes thermal time evolution to situations where there may be no ordinary density matrix or Hamiltonian for a subregion.

## 14.3 The standard representation: why $\rho^{1/2}$ appears

In a more precise finite-dimensional version, we represent states as Hilbert-Schmidt operators.

Let

$$
\mathcal{H}_{\rm HS}
=
\{X:\mathcal{H}\to\mathcal{H}\}
$$

with inner product

$$
\langle X,Y\rangle=\mathrm{Tr}(X^\dagger Y).
$$

The algebra $\mathcal{A}=B(\mathcal{H})$ acts by left multiplication:

$$
L_A X=AX.
$$

A density matrix $\rho$ is represented by the vector

$$
|\Omega_\rho\rangle \leftrightarrow \rho^{1/2}.
$$

Then

$$
\omega(A)=\langle \Omega_\rho,L_A\Omega_\rho\rangle
=
\mathrm{Tr}(\rho^{1/2}A\rho^{1/2})
=
\mathrm{Tr}(\rho A).
$$

So the vector representing the state is $\rho^{1/2}$.

Strictly speaking, the modular operator is not just $\rho^{1/2}$. For the left algebra, it acts as

$$
\Delta = L_\rho R_{\rho^{-1}},
$$

where $R_{\rho^{-1}}$ means right multiplication by $\rho^{-1}$.

Then modular flow gives

$$
\Delta^{it} L_A \Delta^{-it}
=
L_{\rho^{it}A\rho^{-it}}.
$$

So the finite-dimensional facts are:

- the cyclic-separating vector is $\rho^{1/2}$,
- the modular operator involves $\rho$ on the left and $\rho^{-1}$ on the right,
- the induced flow on observables is $A\mapsto \rho^{it}A\rho^{-it}$.

That is the part to remember.

---

# 15. Why modular theory matters for Type III algebras

In Type I quantum mechanics, a state on a subsystem is described by a density matrix.

But for a Type III local QFT algebra, there is no ordinary density matrix for the region.

That sounds catastrophic. How can we define entropy, thermal behavior, or time evolution?

Tomita-Takesaki theory solves part of this.

Given:

- a von Neumann algebra $\mathcal{A}$,
- a cyclic and separating state $|\Omega\rangle$,

modular theory constructs:

1. a modular operator $\Delta$,
2. a modular conjugation $J$,
3. a modular flow

$$
\sigma_t(A)=\Delta^{it}A\Delta^{-it}.
$$

This works even when there is no density matrix.

So modular theory is a replacement for the missing density matrix.

In finite dimensions, modular flow is just $\rho^{it}A\rho^{-it}$. In QFT, it is a deeper structure intrinsic to the algebra-state pair.

---

# 16. Lorentz boosts, Rindler wedges, and the Unruh effect

The most important physical example of modular flow is the Rindler wedge.

## 16.1 Rindler wedge

In flat spacetime with coordinates $(t,x)$, the right Rindler wedge is

$$
x>|t|.
$$

This is the region accessible to an observer with constant acceleration to the right.

Introduce Rindler coordinates:

$$
t=\rho\sinh(a\eta),
$$

$$
x=\rho\cosh(a\eta),
$$

with $\rho>0$.

Curves of constant $\rho$ are hyperbolas:

$$
x^2-t^2=\rho^2.
$$

These are the worldlines of uniformly accelerated observers.

## 16.2 Boosts

A Lorentz boost in the $x$-direction acts like a time translation in Rindler coordinates.

So for an accelerated observer, the boost generator plays the role of Hamiltonian.

## 16.3 Unruh effect

The Minkowski vacuum looks thermal to an accelerated observer.

The Unruh temperature is

$$
T_U=\frac{\hbar a}{2\pi c k_B}.
$$

In natural units,

$$
T_U=\frac{a}{2\pi}.
$$

This means the vacuum restricted to the Rindler wedge behaves like a thermal state with respect to boost time.

## 16.4 Bisognano-Wichmann theorem

The Bisognano-Wichmann theorem says, roughly:

> For relativistic QFT in the vacuum, the modular flow of the algebra of a Rindler wedge is exactly the Lorentz boost flow.

In formula form,

$$
\sigma_s(A)=e^{i 2\pi s K_{\rm boost}} A e^{-i 2\pi s K_{\rm boost}}.
$$

This is profound because it connects:

- abstract modular theory,
- thermal behavior,
- spacetime geometry,
- acceleration horizons.

For QIQT-H, this is a major clue: modular flow is not just mathematical bookkeeping. In important cases, it is geometric time.

---

# 17. Crossed products: adding the clock explicitly

Now we reach another abstract object: the crossed product.

The crossed product is how one takes an algebra with a symmetry flow and builds a larger algebra in which the symmetry is implemented by explicit operators.

Let’s start finite.

## 17.1 Finite group toy model

Suppose we have an algebra

$$
\mathcal{A}=\mathbb{C}^2,
$$

the algebra of functions on two points. Elements are pairs

$$
(a,b).
$$

Represent them as diagonal matrices:

$$
(a,b)\leftrightarrow
\begin{pmatrix}
a&0\\
0&b
\end{pmatrix}.
$$

Let the group $G=\mathbb{Z}_2$ act by swapping the two points:

$$
\alpha(a,b)=(b,a).
$$

Now add a unitary $U$ that implements the swap:

$$
U
\begin{pmatrix}
a&0\\
0&b
\end{pmatrix}
U^\dagger
=
\begin{pmatrix}
b&0\\
0&a
\end{pmatrix}.
$$

Choose

$$
U=
\begin{pmatrix}
0&1\\
1&0
\end{pmatrix}.
$$

The algebra generated by diagonal matrices and $U$ is all of $M_2(\mathbb{C})$.

This is the crossed product

$$
\mathbb{C}^2\rtimes \mathbb{Z}_2
\cong
M_2(\mathbb{C}).
$$

So the crossed product means:

> Start with an algebra. Add operators that implement a symmetry of that algebra.

## 17.2 General definition idea

Suppose a group $G$ acts on $\mathcal{A}$ by automorphisms:

$$
\alpha_g:\mathcal{A}\to\mathcal{A}.
$$

An automorphism is a structure-preserving map:

$$
\alpha_g(AB)=\alpha_g(A)\alpha_g(B),
$$

$$
\alpha_g(A^\dagger)=\alpha_g(A)^\dagger.
$$

The crossed product

$$
\mathcal{A}\rtimes_\alpha G
$$

is generated by:

- elements $A\in\mathcal{A}$,
- unitaries $U_g$ for $g\in G$,

with the relation

$$
U_g A U_g^\dagger=\alpha_g(A).
$$

This relation is the heart of the construction.

## 17.3 The continuous case: $G=\mathbb{R}$

For modular theory, the group is usually

$$
G=\mathbb{R},
$$

because modular flow is a continuous one-parameter family:

$$
\sigma_t(A).
$$

The crossed product is

$$
\mathcal{A}\rtimes_\sigma \mathbb{R}.
$$

It is obtained by adding unitaries $U(t)$ satisfying

$$
U(t) A U(t)^\dagger = \sigma_t(A).
$$

By Stone’s theorem, a continuous unitary group has a self-adjoint generator $K$:

$$
U(t)=e^{-itK}.
$$

So the crossed product contains the unitary implementers $U(t)$ of the modular flow as bounded operators in an enlarged algebra. The generator $K$ is generally an *unbounded self-adjoint operator affiliated with* the crossed-product algebra — not literally an element of it, but uniquely determined by it via Stone's theorem. (The slogan "we add the modular Hamiltonian as an operator" is a useful shorthand, but the precise statement is the affiliation, not literal membership.)

## 17.4 Why an $L^2(\mathbb{R})$ factor appears

For a continuous parameter $t$, the natural Hilbert space of wavefunctions over that parameter is

$$
L^2(\mathbb{R}).
$$

This is the space of square-integrable functions

$$
\psi(s),
$$

where $s$ is a real variable.

Think of $s$ as a clock reading.

On $L^2(\mathbb{R})$, define:

- clock-reading operator

$$
(T\psi)(s)=s\psi(s),
$$

- clock-momentum operator

$$
(K\psi)(s)=-i\frac{d}{ds}\psi(s).
$$

They satisfy

$$
[T,K]=i.
$$

The unitary

$$
e^{-itK}
$$

shifts the clock wavefunction:

$$
(e^{-itK}\psi)(s)=\psi(s-t).
$$

So the crossed product Hilbert space often looks like

$$
\mathcal{H}_{\rm original}\otimes L^2(\mathbb{R}).
$$

**The honest statement** is that the regular representation of the crossed product introduces an $L^2(\mathbb{R})$ factor associated with the *flow parameter* — the variable that labels the modular automorphism. Mathematically, that's all the bare theorem says.

Interpreting this $L^2(\mathbb{R})$ as a *physical quantum clock* is an additional move, motivated by quantum-gravity ideas (Page-Wootters formalism, gravitationally dressed observers, observer-relative algebras). In Witten 2022 and CPW 2022 the physical clock interpretation is natural and well-motivated — it's how gravity actually enters the construction. But you should keep in mind: the clock interpretation is a *physical reading* of an extra mathematical degree of freedom; it is not part of the bare operator-algebra theorem.

Also, the action of the original algebra on $\mathcal{H} \otimes L^2(\mathbb{R})$ is more subtle than a simple tensor structure $A \otimes I$. In the standard representation,
$$
(\pi(A)\xi)(s) = \sigma_{-s}(A) \, \xi(s),
$$
so the original-algebra operators act in a way that's "twisted" by the modular flow itself. The clean tensor-product picture is a useful first approximation, not the exact structure.

## 17.5 Connection to quantum gravity clock formalisms

In canonical quantum gravity, there is often no external time. Instead, one introduces a clock degree of freedom $T$ and describes other variables relative to it.

A simple Page-Wootters-style constraint is

$$
(P_T+H_{\rm sys})|\Psi\rangle=0.
$$

Here:

- $T$ is the clock reading,
- $P_T=-i\partial_T$ is its conjugate momentum,
- $H_{\rm sys}$ is the system Hamiltonian.

Then conditional states

$$
|\psi(t)\rangle = \langle T=t|\Psi\rangle
$$

obey an ordinary Schrödinger equation.

The crossed product clock is similar in spirit: modular time becomes represented by an explicit Hilbert-space degree of freedom.

---

# 18. Takesaki’s structure theorem: Type III plus clock gives Type II

Now we can state the key structural fact.

For a Type III von Neumann algebra $\mathcal{M}$ with modular flow $\sigma_t$, the crossed product

$$
\mathcal{M}\rtimes_{\sigma}\mathbb{R}
$$

is called the **continuous core** of $\mathcal{M}$. It is always *semifinite*. For Type III$_1$ factors (the relevant case for local QFT algebras), the continuous core is **Type II$_\infty$** — semifinite trace with $\tau(\mathbf{1}) = \infty$. For Type III$_\lambda$ ($0 < \lambda < 1$) or Type III$_0$ factors, the continuous core may have a nontrivial center (i.e., not be a single factor).

So the precise statement is: *crossed product with modular flow gives a semifinite algebra (the continuous core), which is Type II$_\infty$ in the cases relevant to QFT*. The slogan "Type III + clock = Type II" is shorthand for this; the exact type and structure depend on which Type III subclass you started with.

This is part of Takesaki's theory (Connes-Takesaki decomposition).

## 18.1 Intuition

Type III algebras lack a trace. Without a trace, ordinary entropy is hard to define.

The modular flow is like an intrinsic thermal time. But in the Type III algebra, that flow is external as an automorphism.

When we form the crossed product, we add an explicit generator of that flow — a clock or energy-like variable.

Doing this enlarges the algebra enough that a trace appears.

So:

$$
\text{Type III algebra}
+
\text{modular clock}
\quad
\Longrightarrow
\quad
\text{Type II algebra with trace}.
$$

This is the slogan.

## 18.2 Why this helps entropy

Entropy usually needs a trace:

$$
S=-\mathrm{Tr}(\rho\log\rho).
$$

Type III algebras do not have a normal semifinite trace, so naïve entropy fails.

After crossing with modular flow, one gets a semifinite algebra (the continuous core) with a faithful normal semifinite trace $\tau$. This provides a trace framework in which entropy-like quantities can sometimes be defined:

$$
S=-\tau(\rho\log\rho),
$$

with appropriate renormalization choices.

**Important caveat.** Two clarifications matter here:

1. **The crossed product does NOT automatically give finite entropy.** The trace $\tau$ on a Type II$_\infty$ algebra has $\tau(\mathbf{1}) = \infty$. So generic states on the continuous core can still have divergent or undefined entropy. Defining a finite renormalized entropy requires further choices: a reference state, a regularization, or selecting states whose "density operator" relative to $\tau$ is trace-class. The continuous core is a *necessary condition* for an entropy notion, not a *sufficient* one.

2. **Relative entropy was already well-defined for Type III algebras directly,** via Araki's construction using the relative modular operator. So the modular machinery already gave us a perfectly good notion of *relative* entropy (entropy of one state with respect to another) without needing crossed products. What the crossed-product construction adds is a route to *absolute*-like renormalized entropies via the trace structure, which is more subtle.

So the slogan "Type III + clock = renormalized entropy" should be heard as: the crossed product gives us trace-based machinery and reproduces *differences* in generalized entropy (CPW's main result); absolute renormalized entropies require additional scheme choices.

## 18.3 Not magic

This does not mean Type III problems disappear.

The crossed product adds extra structure: a modular time/clock degree of freedom. The result depends on the state through its modular flow, though there are powerful theorems saying the resulting “core” is canonical up to equivalence.

The physical interpretation still requires care.

For QIQT-H, the important point is:

> A region that is Type III at the purely local-QFT level can be embedded into a Type II “core” where traces and entropies become meaningful.

---

# 19. Renormalized entropy

In QFT, naïve entanglement entropy diverges:

$$
S_{\rm ent}\to\infty
$$

as the UV cutoff is removed.

But physics often deals with divergent quantities by renormalization.

## 19.1 Energy analogy

In QFT, the vacuum energy is formally infinite:

$$
E_0=\frac12\sum_{\mathbf{k}}\hbar\omega_{\mathbf{k}}.
$$

But only energy differences or gravitationally renormalized quantities are physical.

We subtract or absorb divergences into counterterms.

Similarly, local entanglement entropy has universal boundary divergences. These are not usually directly observable by themselves.

## 19.2 Entropy differences and relative entropy

A very useful finite quantity is relative entropy.

For density matrices,

$$
S(\rho||\sigma)
=
\mathrm{Tr}(\rho\log\rho)
-
\mathrm{Tr}(\rho\log\sigma).
$$

It measures distinguishability of $\rho$ from $\sigma$.

In QFT, even when individual entanglement entropies diverge, relative entropy can be finite.

There is an important identity:

$$
S(\rho||\sigma)
=
\Delta\langle K_\sigma\rangle
-
\Delta S,
$$

where

$$
K_\sigma=-\log\sigma
$$

is the modular Hamiltonian of $\sigma$,

$$
\Delta\langle K_\sigma\rangle
=
\mathrm{Tr}(\rho K_\sigma)-\mathrm{Tr}(\sigma K_\sigma),
$$

and

$$
\Delta S=S(\rho)-S(\sigma).
$$

Even if $S(\rho)$ and $S(\sigma)$ separately diverge, the difference can be meaningful after renormalization.

## 19.3 Renormalized matter entropy

The renormalized entropy is roughly:

$$
S_{\rm matter}^{\rm ren}
=
S_{\rm matter}^{\rm cutoff}
-
S_{\rm divergent\ boundary}.
$$

QIQT-H wants this subtraction to be principled rather than arbitrary.

The modular/crossed-product machinery provides a principled framework for defining entropy *differences* — Araki relative entropy is already well-defined in Type III, and the CPW crossed-product construction reproduces generalized-entropy *differences*. Absolute-like renormalized entropies can also be defined within this framework once a reference state and normalization are chosen.

The slogan is:

> Use modular structure to define entropy relative to a reference state, subtracting the universal UV boundary entanglement in a principled way.

This is why Type III and crossed products matter for QIQT-H. The holographic bound talks about entropy, but raw QFT entropy is divergent — the modular/crossed-product machinery gives us trace-based tools (with appropriate choices) that match generalized-entropy differences in semiclassical gravity. Whether they give *canonical absolute* entropies depends on scheme choices; the framework should not claim more canonicity than the underlying mathematics actually delivers.

---

# 20. Generalized entropy

In gravitational physics, the entropy associated with a *codimension-2 surface* $\Sigma$ — for example a black-hole horizon cross-section, or a quantum extremal surface bounding a spatial region $R$ — is not just matter entropy. It is

$$
S_{\rm gen}(\Sigma; R)
=
\frac{\mathrm{Area}(\Sigma)}{4G\hbar}
+
S_{\rm matter}^{\rm ren}(R).
$$

This is called the **generalized entropy**.

A note on dimensions: the area term is the area of a codimension-2 surface (2-dimensional in 4D spacetime), not the area of a codimension-1 hypersurface boundary. For a spatial region $R$ at a moment of time, the relevant $\Sigma$ is $\partial R$ as a 2-surface. The matter entropy is the renormalized entropy of matter on one side of $\Sigma$ (say inside $R$). Throughout the rest of this tutorial, when we write $\partial R$ or similar without further qualification, we mean the codimension-2 boundary surface; this is the convention CPW use.

## 20.1 Origin: black-hole thermodynamics

Bekenstein argued that black holes should have entropy proportional to horizon area. Hawking radiation fixed the coefficient:

$$
S_{\rm BH}=\frac{A}{4G\hbar}.
$$

If matter falls into a black hole, ordinary matter entropy outside may decrease. But the black hole area increases.

The generalized second law says:

$$
S_{\rm outside}+S_{\rm BH}
$$

never decreases.

So the correct entropy in gravity is not merely matter entropy. It is matter entropy plus area entropy.

## 20.2 Why area appears

In semiclassical gravity, geometry itself carries entropy.

A horizon hides information. The area term counts gravitational degrees of freedom associated with the boundary.

Thus, for a region with boundary $\partial D$, QIQT-H uses

$$
S_{\rm gen}(\partial D)
=
\frac{\mathrm{Area}(\partial D)}{4G\hbar}
+
S_{\rm matter}^{\rm ren}.
$$

This is the entropy budget.

## 20.3 Why this is the right bound for records

If records are physical information in a gravitational region, the number of distinguishable records should not exceed the generalized entropy.

So QIQT-H’s core inequality is schematically

$$
I_{\rm records}^{\varepsilon}
\leq
S_{\rm gen}.
$$

This ties the measurement problem to black-hole thermodynamics.

---

# 21. Gauge theory analogy

QIQT-H’s branch-summed constraint is often compared to a gauge constraint. Let’s review gauge theory first.

## 21.1 Gauge redundancy in electromagnetism

In electromagnetism, the vector potential $A_\mu$ is not unique.

The transformation

$$
A_\mu \to A_\mu+\partial_\mu\lambda
$$

does not change the electromagnetic fields $E$ and $B$.

So different $A_\mu$'s can represent the same physical situation.

Gauge symmetry is redundancy in our description.

## 21.2 Gauss law as a constraint

In canonical electromagnetism, physical states must satisfy Gauss’s law:

$$
\nabla\cdot E=\rho.
$$

In quantum theory, this becomes an operator constraint:

$$
(\nabla\cdot \hat E-\hat\rho)|\Psi_{\rm phys}\rangle=0.
$$

So not every vector in the formal Hilbert space is physical.

The physical Hilbert space is the subspace satisfying the constraint.

## 21.3 BRST cohomology

In more advanced gauge theory, especially for nonabelian gauge fields, one introduces a BRST operator $Q$ satisfying

$$
Q^2=0.
$$

Physical states are BRST-closed:

$$
Q|\psi\rangle=0,
$$

and states differing by BRST-exact terms are identified:

$$
|\psi\rangle \sim |\psi\rangle+Q|\chi\rangle.
$$

This is called cohomology.

You do not need the details. The key idea is:

> Gauge theory has a large formal state space, but only a constrained quotient/subspace is physical.

## 21.4 Analogy to QIQT-H

QIQT-H similarly says:

> The formal quantum branch space is larger than the physically admissible record space.

The branch-summed constraint plays a role analogous to Gauss’s law:

$$
\mathcal{C}_{\rm QIQT-H}|\Psi_{\rm phys}\rangle=0
$$

or, more generally,

$$
I_{\rm branch}^\varepsilon(D)\leq S_{\rm gen}(\partial D).
$$

The analogy is **structural, not technical**.

**Important caveat.** Gauge constraints in the technical sense have specific properties that the QIQT-H admissibility condition does NOT have:

- Gauge constraints are *linear* operator equations: $G_a|\psi\rangle = 0$, where $G_a$ are bounded or affiliated operators acting linearly on the state.
- Gauge constraints are *local*: $G_a$ involves fields at a point or smeared over a small region.
- Gauge constraints reflect *redundancy*: gauge-equivalent states are physically identical.
- Gauge constraints *generate symmetries*: gauge transformations are flows generated by the constraints.
- BRST machinery requires *nilpotency* $Q^2 = 0$.

The QIQT-H admissibility condition $I_\Sigma^\epsilon[\omega_R] \le Q_R$ is:

- *Nonlinear* (depends nonlinearly on the state through the active-set construction)
- *History- and coarse-graining-dependent* (requires choosing $\mathcal{C}(R)$, the record subalgebra, and the smoothing parameter $\epsilon$)
- *Not from a symmetry* (no generator, not even formally)
- *Not a redundancy*: forbidden multi-record states are not gauge-equivalent to allowed states — they are simply excluded
- *Not BRST-like*: no nilpotent charge or cohomological structure

So when we say "QIQT-H's constraint is like a gauge constraint," we mean: both restrict a larger formal space to a smaller physical one, and physical Hamiltonians must preserve the constraint. **That structural pattern is the entire analogy. The mathematical machinery is completely different.**

In particular: writing $\mathcal{C}_{\rm QIQT-H}|\Psi_{\rm phys}\rangle = 0$ above is suggestive notation, not a literal operator equation. There is no Hermitian "constraint operator" $\mathcal{C}_{\rm QIQT-H}$ whose kernel defines $\mathcal{H}_{\rm phys}$. The admissibility condition is a nonlinear inequality on regional algebra-states. Its dynamical implementation — characterizing which Hermitian operators preserve $\mathcal{H}_{\rm phys}$ — is one of the framework's central open problems.

The shared pattern is:

1. Write a large formal space.
2. Impose a constraint.
3. Physical states/histories are those satisfying the constraint.

But the *kind* of constraint, and the mathematical machinery for implementing it dynamically, is genuinely different in QIQT-H from anything in gauge theory or BRST.

---

# 22. Bohmian equivariance and why Born weights matter

QIQT-H wants to reproduce ordinary Born statistics. A useful comparison is Bohmian mechanics.

## 22.1 Bohmian mechanics in brief

Bohmian mechanics adds actual particle positions $Q(t)$.

The wavefunction obeys Schrödinger’s equation. The particles obey a guidance equation.

For one particle,

$$
\frac{dQ}{dt}
=
\frac{\hbar}{m}\operatorname{Im}
\frac{\nabla\psi}{\psi}(Q).
$$

The probability density

$$
\rho(q,t)=|\psi(q,t)|^2
$$

is special.

## 22.2 Equivariance

Equivariance means:

> If particle positions are distributed as $|\psi(q,0)|^2$ initially, then they remain distributed as $|\psi(q,t)|^2$ at later times.

Why?

Schrödinger’s equation implies the continuity equation

$$
\frac{\partial |\psi|^2}{\partial t}
+
\nabla\cdot j=0,
$$

where

$$
j=\frac{\hbar}{m}\operatorname{Im}(\psi^*\nabla\psi).
$$

The Bohmian velocity is

$$
v=\frac{j}{|\psi|^2}.
$$

So a distribution of particles moving with velocity $v$ obeys

$$
\frac{\partial \rho}{\partial t}
+
\nabla\cdot(\rho v)=0.
$$

If initially $\rho=|\psi|^2$, then both obey the same equation. Therefore equality persists.

That is equivariance.

## 22.3 What QIQT-H needs analogously

QIQT-H does not add particle positions. But it needs a measure over admissible histories.

The natural candidate is the Born/decoherence weight:

$$
w(h)=D(h,h).
$$

An analogue of equivariance would be a theorem saying:

> The admissibility constraint and the dynamics preserve Born-weight consistency across time and coarse-graining.

In other words, if probabilities are Born-like at one stage, the branch-summed constraint should not spoil them at later stages.

This is one of the technical tasks for the framework.

---

# 23. Bell’s theorem and measurement independence

Any foundations proposal must face Bell’s theorem.

## 23.1 Bell setup

Two experimenters, Alice and Bob, measure entangled particles.

Alice chooses setting $a$, gets outcome $A=\pm1$.

Bob chooses setting $b$, gets outcome $B=\pm1$.

A hidden-variable theory introduces variables $\lambda$ that determine or influence outcomes.

A local hidden-variable model assumes

$$
A=A(a,\lambda),
$$

$$
B=B(b,\lambda).
$$

The joint expectation is

$$
E(a,b)=\int d\lambda\, \rho(\lambda) A(a,\lambda)B(b,\lambda).
$$

Bell/CHSH inequalities follow, for example:

$$
|E(a,b)+E(a,b')+E(a',b)-E(a',b')|\leq 2.
$$

Quantum mechanics can violate this bound up to

$$
2\sqrt{2}.
$$

Experiments agree with quantum mechanics.

## 23.2 Measurement independence

Bell’s derivation assumes measurement independence:

$$
\rho(\lambda|a,b)=\rho(\lambda).
$$

That means the hidden variables $\lambda$ are statistically independent of the later choices of measurement settings $a,b$.

If this fails, Bell inequalities need not follow.

## 23.3 Is rejecting measurement independence superdeterminism?

Often, any violation of measurement independence is called superdeterminism.

But there are different possible attitudes.

A crude superdeterministic picture says:

> The universe conspiratorially prearranged your detector settings and particle variables to fake quantum correlations.

QIQT-H aims for a different picture:

> The admissible global histories are constrained by holographic record consistency. Settings, outcomes, and hidden/global variables are not sampled independently because only globally admissible record configurations exist.

In probability terms, the framework may have

$$
\rho(\lambda|a,b)\neq \rho(\lambda),
$$

not because of a malicious conspiracy, but because $\lambda,a,b$ are all parts of one constrained physical history.

However, one should be honest:

> Many physicists would still classify any denial of measurement independence as a form of superdeterminism in the broad sense.

So QIQT-H must do more than say “measurement independence fails.” It must explain the correlations naturally, quantitatively, and without destroying experimental freedom in ordinary practice.

---

# 24. How the pieces fit together

Let’s now assemble the framework.

## 24.1 Starting point

We begin with ordinary quantum theory:

- a global state,
- unitary evolution,
- decoherence producing branches,
- Born/decoherence weights for histories.

## 24.2 The problem

Decoherence gives effective branches, but not definite outcomes.

Many-worlds accepts all branches as real. QIQT-H says:

> In quantum gravity, the total record content of a causal region is finite. Therefore, the formal branch structure must be constrained.

## 24.3 The entropy budget

For a region $D$,

$$
S_{\rm gen}(\partial D)
=
\frac{A(\partial D)}{4G\hbar}
+
S_{\rm matter}^{\rm ren}.
$$

This is the maximum information budget.

## 24.4 The branch information

For a decoherent family of histories, define a support-like entropy

$$
I_{\rm branch}^{\varepsilon}
=
\log N_{\rm eff}^{\varepsilon},
$$

where $N_{\rm eff}^{\varepsilon}$ is the smoothed number of distinguishable recorded alternatives.

## 24.5 The QIQT-H constraint

The central condition is

$$
I_{\rm branch}^{\varepsilon}(D)
\leq
S_{\rm gen}(\partial D).
$$

This is branch-summed: it counts alternatives across the family, not only within one branch.

## 24.6 The role of operator algebras

In continuum QFT, local algebras are Type III, so naïve entropy is divergent.

Tomita-Takesaki modular theory supplies a canonical modular flow for a region and state.

The crossed product by modular flow produces a semifinite continuous core (Type II$_\infty$ in the typical Type III$_1$ case) with a trace.

This framework supports entropy *differences* canonically (via Araki relative entropy and CPW generalized-entropy-difference results) and, with additional choices of reference state and normalization, absolute-like renormalized entropies.

Thus, schematically:

$$
\begin{aligned}
&\text{QFT region} \rightarrow \text{Type III algebra} \rightarrow \text{modular flow} \\
&\rightarrow \text{crossed-product core with semifinite trace} \\
&\rightarrow \text{entropy differences / renormalized entropies with choices} \rightarrow S_{\rm gen}.
\end{aligned}
$$

That is the mathematical pipeline.

---

# 25. A finite-dimensional toy model of QIQT-H

Let’s make a toy model that captures the logic without Type III complications.

Suppose a system undergoes repeated binary measurements. After $n$ measurements, ordinary quantum theory gives

$$
2^n
$$

possible bit-string records:

$$
h=(b_1,b_2,\dots,b_n),
\qquad b_i\in\{0,1\}.
$$

If all are nonzero-probability and distinguishable, the support entropy is

$$
I_{\rm branch}= \log 2^n = n\log 2.
$$

Now suppose the region has entropy budget

$$
S_{\rm max}=m\log 2.
$$

That corresponds to $m$ bits.

The QIQT-H constraint says

$$
n\log 2 \leq m\log 2,
$$

or

$$
n\leq m.
$$

If $n>m$, then the full $2^n$-branch record family cannot be physically realized as mutually distinguishable records inside the region.

With smoothing, if most probability is concentrated on fewer histories, the effective support can be smaller.

Example:

Suppose after many measurements, probabilities are heavily concentrated on $2^m$ histories, with total probability $1-\varepsilon$. Then

$$
N^\varepsilon_{\rm eff}=2^m,
$$

and the family may be admissible.

This toy model is crude, but it shows the logic:

> QIQT-H constrains not amplitudes directly, but physically distinguishable recorded alternatives.

---

# 26. Another toy model: decoherence plus finite record capacity

Let a qubit system interact with a memory register of $m$ bits.

The memory Hilbert space has dimension

$$
2^m.
$$

It can store at most $2^m$ orthogonal classical records.

Now imagine a formal process that tries to create $N>2^m$ perfectly distinguishable outcomes.

Unitary quantum mechanics on a memory of dimension $2^m$ cannot map $N$ orthogonal input alternatives to $N$ orthogonal memory states if $N>2^m$.

This is just linear algebra.

QIQT-H generalizes this idea gravitationally:

- finite memory register $\rightarrow$ finite causal region,
- memory dimension $2^m$ $\rightarrow$ $e^{S_{\rm gen}}$,
- record capacity bound $\rightarrow$ holographic entropy bound.

---

# 27. What is new in QIQT-H?

QIQT-H is not merely saying “there is decoherence.” Decoherence is already standard.

It adds:

1. **A holographic record-capacity constraint.**
2. **A branch-summed support entropy.**
3. **A modular-algebraic way to define entropy in QFT regions.**
4. **A rule for admissible histories rather than a collapse law.**

The hope is that definite outcomes emerge because the physical record structure is finite and constrained.

---

# 28. What remains open?

Several major problems remain.

## 28.1 Precise definition of branch information

One must define

$$
I_{\rm branch}^{\varepsilon}(D)
$$

in a way that is:

- basis-independent,
- compatible with decoherence,
- stable under coarse-graining,
- physically computable.

Pointer bases and spectrum broadcast structures help, but a full definition is hard.

## 28.2 Equivariance-like theorem

QIQT-H needs a theorem showing that Born weights are preserved under admissible dynamics and coarse-graining.

Without this, it risks either disagreeing with quantum experiments or smuggling in the Born rule.

## 28.3 Relativistic covariance

The constraint must not depend on arbitrary choices of time slicing.

Using causal diamonds, local algebras, and modular flow helps, but a complete covariant formulation is needed.

## 28.4 Gravity beyond semiclassical approximation

The generalized entropy formula

$$
S_{\rm gen}=\frac{A}{4G\hbar}+S_{\rm matter}^{\rm ren}
$$

is semiclassical. A full quantum gravity version may require more.

## 28.5 Bell correlations

If QIQT-H violates measurement independence, it must explain precisely how, without making science impossible.

It must reproduce observed Bell violations while preserving the practical independence of experimental choices.

## 28.6 Experimental signatures

A framework is more convincing if it predicts deviations from standard quantum theory somewhere.

Possible places to look:

- near black holes,
- cosmological horizons,
- extreme entropy-saturating systems,
- high-complexity quantum information experiments,
- gravitationally constrained quantum memories.

At present, this is speculative.

---

# 29. Summary in one picture

The framework can be summarized as:

$$
\boxed{
\text{Unitary quantum theory}
+
\text{decoherent histories}
+
\text{holographic finite-information constraint}
}
$$

with the entropy side defined using:

$$
\boxed{
\text{Type III local QFT algebra}
\rightarrow
\text{modular theory}
\rightarrow
\text{crossed product Type II core}
\rightarrow
\text{renormalized entropy}
}
$$

and the central inequality:

$$
\boxed{
I_{\rm branch}^{\varepsilon}(D)
\leq
S_{\rm gen}(\partial D)
=
\frac{A}{4G\hbar}
+
S_{\rm matter}^{\rm ren}
}
$$

The interpretation is:

> A finite gravitational region cannot support an arbitrarily large set of mutually distinguishable quantum records. Measurement outcomes are tied to the admissible record structure of the universe, not to an explicit dynamical collapse.

---

# 30. Glossary

## Branch

An effectively noninterfering component of the wavefunction produced by decoherence.

## Record

A physical encoding of an outcome, such as a pointer position, detector click, scattered photon pattern, or memory state.

## Decoherence

The suppression of interference between branches due to entanglement with the environment.

## Einselection

The environment-induced selection of stable pointer states.

## Quantum Darwinism

The idea that classical objectivity arises because many environment fragments redundantly encode the same pointer-state information.

## Decoherent histories

A formulation of quantum mechanics assigning probabilities to whole sequences of events when interference between histories is negligible.

## Von Neumann algebra

An algebra of operators closed under adjoints and suitable limits, equivalently equal to its double commutant.

## Type I algebra

The ordinary algebra of all operators on a Hilbert space. This is standard QM.

## Type II algebra

An infinite-dimensional algebra with a trace and continuous projection dimensions.

## Type III algebra

An algebra with no finite trace and no ordinary density matrices for subregions. Local QFT algebras are typically Type III.

## Cyclic vector

A vector $|\Omega\rangle$ such that applying algebra elements to it generates the whole Hilbert space.

## Separating vector

A vector $|\Omega\rangle$ such that no nonzero algebra element annihilates it.

## Modular flow

A canonical automorphism flow of an algebra determined by a state. In finite dimensions:

$$
\sigma_t(A)=\rho^{it}A\rho^{-it}.
$$

## Modular Hamiltonian

$$
K=-\log\rho
$$

in finite dimensions. It generates modular flow.

## Crossed product

An enlarged algebra obtained by adding unitaries that implement a symmetry or flow.

## Takesaki theorem

A result saying, roughly, that crossing a Type III algebra by its modular flow produces a Type II algebra with a trace.

## Renormalized entropy

A finite entropy obtained by subtracting universal UV divergences from QFT entanglement entropy.

## Generalized entropy

$$
S_{\rm gen}
=
\frac{A}{4G\hbar}
+
S_{\rm matter}^{\rm ren}.
$$

## Rényi-0 entropy

The logarithm of the number of nonzero-probability outcomes.

## Smooth support

A regularized support count that ignores outcomes with total probability at most $\varepsilon$.

## Measurement independence

The Bell assumption

$$
\rho(\lambda|a,b)=\rho(\lambda).
$$

It says hidden variables are statistically independent of measurement settings.

## Equivariance

The preservation of a probability measure under dynamics, as $|\psi|^2$ is preserved in Bohmian mechanics.

---

# 31. Final perspective

QIQT-H is motivated by a simple physical suspicion:

> The measurement problem may look impossible because we usually ignore gravity. We allow the wavefunction to generate unlimited independent records inside finite regions. But quantum gravity suggests finite information capacity.

The hard part is turning that suspicion into mathematics.

That is why the framework uses:

- decoherent histories to define record-bearing alternatives,
- Quantum Darwinism to identify objective records,
- Rényi-0 and smooth support to count alternatives,
- generalized entropy to set the gravitational budget,
- Type III algebra to describe QFT regions correctly,
- modular theory and crossed products to renormalize entropy,
- gauge-like constraints to define physical admissibility.

Whether this ultimately works is open.

But the roadmap is clear:

$$
\text{measurements create records}
$$

$$
\text{records require information capacity}
$$

$$
\text{gravity bounds information capacity}
$$

$$
\text{therefore quantum histories must satisfy holographic record constraints}.
$$

That is the core of QIQT-H.