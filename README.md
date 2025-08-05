# Riemann Integration in Lean

This project is a (currently incomplete) implementation of Riemann integration in Lean. The way this is implemented is meant to be more general than what one would usually call Riemann integration. The basic notions are as follows.

### Setup

Given some space $X$, a *polygonal path in* $X$ is just an ordered list of points in $X$. We place a partial order on the set of all polygonal paths as follows. Given polygonal paths $p$ and $q$, we say that $p\leq q$ if $p$ is a sublist of $q$. Alternatively, we say that '$q$ refines $p$'. Note that if we have a polygonal path in $[a,b] \subset \mathbb{R}$ whose list of points is in increasing order and starts at $a$ and ends at $b$, then this is essentially the same data as a partition of the interval $[a,b]$.

We define a *path in* $X$ to be a [directed set](https://en.wikipedia.org/wiki/Directed_set) of polygonal paths with respect to the refinement ordering. An example of a path is the set of *all* partitions of an interval in $[a,b] \subset \mathbb{R}$. The fact that this set is directed is equivalent to the familiar statement that any two partitions of $[a,b]$ have a common refinement.


It is easy to check that if we have two spaces $X$ and $Y$ and a map $f : X\to Y$, then $f$ lifts to a monotone map from polygonal paths on $X$ to polygonal paths on $Y$ (with respect to the refinement orderings on $X$ and $Y$). Consequently, $f$ also lifts to a map from paths in $X$ to paths $Y.$

Note that we haven't imposed any topology on $X$ and $Y$ and there is no continuity requirement on $f$. Recall that the *usual* notion of a path in a topological space $X$ is a continuous map $\gamma : [0,1]\to X$. Under our definitions, we can realize this path as follows: take the the directed set of all partitions of $[0,1]$, and then push this forward via $\gamma$ to get a directed set of polygonal paths in $X.$

Now suppose $R$ is a commutative ring and $M$ is a module over $R$. Then given a function $f : R \to M$ and a polygonal path $p$ in $R$, there is a natural way to compute the left or right Riemann sum of $f$ along $p$. Consequently, given a path $\gamma$ and a function $f$, we get a [net](https://en.wikipedia.org/wiki/Net_(mathematics)) by taking the Riemann sums of $f$ along each polygonal path $p \in \gamma$. If $M$ has a topology and the net converges, then this give a definition of the integral of $f$ along $\gamma$.

**Todo:** The definitions are stated and the relevant details about paths have been proved. The next step is to show that integrability is implied by certain regularity assumptions. For example, showing that continuous functions on $\mathbb{R}$ or $\mathbb{C}$ are integrable on paths induced by continuous functions $\gamma : [0,1] \to \mathbb{R}$ or $\mathbb{C}$ (where  we mean 'induced' in the sense described previously).

**Notes:**

* The usual notion of a path is "1-dimensional", but in the setup above the data we are providing about the path is zero dimensional in some sense since each polygonal path is just a list of points. This is a bit unnatural, but the nice thing is that it doesn't require any regularity assumptions about the path in order to give the definition. Hence, in principle this definition can assign a value to the integral even when the path arises from a fractal shape.

* One could also set up measure theory using directed sets. In that case one replaces the polygonal paths with "partitions into measurable pieces". Any two such partitions have a common refinement.



