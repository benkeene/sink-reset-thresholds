# Informal proof (proof of record)

This file is the VERIFIED packet's `PROOF.md` of claim_0001 (lab `~/conductor-lab/agents/shared/claim_0001`,
prove run `2026-10-24_prove-claim-0001`, approved 2026-10-25), copied verbatim below the rule. The statements of
record in `records.yaml` cite its sections: the upper bound is §5 Theorem with §3 Proposition 10; the lower bound is
§5 Theorem with §4 Lemmas 12, 13, 14; the pair `(5,2)` is the §5 Theorem's list of nine pairs, with the automaton
`C_{2,2}` of Lemma 14. Appendix B (packet errata) has been applied to the copies `docs/CLAIM.md`,
`docs/CONTEXT.md` and `docs/COMPUTATION.md` in this repository; the packet files themselves are unchanged.

---

# Proof

**Status of this file.** PROOF.md held no candidate proof (there is no Astra section). The proof below is the
Opus prover's own, written by hand. It is the **proof of record**. It is self-contained: it does not rely on any
computation (none was run for this attempt), and it reproves the Lipin–Volkov endpoint results that it uses.
The computational record that CLAIM.md cites (COMPUTATION.md, EVIDENCE.md) belongs to an earlier, separate
exhaustive computation for $3\le n\le5$. It is independent corroboration and is not a premise of any step below.
Whether that record is complete has no bearing on the validity of this proof. The record itself (artifact location,
SHA-256 hashes, reproduction command, recorded output and the verifier's stated assumptions) is copied into
Appendix A below, so that this packet supplies it directly. Two sentences of CLAIM.md (line 9) and one label of
CONTEXT.md (line 5) are less accurate than this file about where the computational record is and about the
literature status. The responder may not edit those files. Appendix B gives verbatim replacement text for them, and
for the empty COMPUTATION.md, to be applied at packaging. **Where those files and this one differ on either point,
this file (Literature status, Appendices A and B) takes precedence.** Neither point affects the mathematics.

**Literature status.** The sources inspected are Lipin–Volkov, arXiv:2601.18362v1 (§2.1 for the game conventions,
§3.4 for the construction $L^k_m$ and the conjecture); arXiv lists only v1. The later CiE 2026 chapter
(doi:10.1007/978-3-032-31348-5_24) was **not** inspected in full text. "Open" below means only this: *no resolution
of the conjecture was located in the inspected sources*. It is not a claim about the current literature. Nothing in
the proof depends on it. The status record that CONTEXT.md:5 cites
(`conductor-scratch/runs/2026-10-24_trial/discover/status/finite-state-dynamics-and-automata--sink-adversarial-reset-threshold/status.json`,
read in this round) carries the same qualification. Its framing A verdict is `UNCLEAR`, with "remains unresolved in
the inspected sources, and the later conference chapter could not be checked for a resolution". Its framing B verdict
is `OPEN`, with "no resolution was located, and the later conference full text remains uninspected". So the label
`OPEN_ASYMPTOTIC` in CONTEXT.md:5 is a dated classification by the discovery gate. Read together with its source, it
asserts no more than this paragraph does. Appendix B gives replacement text that makes this explicit.

**What is proved, and a stronger statement.** Write
$$f_k(n)=\sum_{i=1}^{n-1}\left\lceil \tfrac{i}{k}\right\rceil .$$
The claim asks for $M(n,k)=f_k(n)$ for $3\le n\le 5$, $1\le k\le n-1$. We prove more:

> **$M(n,k)=f_k(n)$ for all $n\ge2$, $k\ge1$ with $k=1$ or $n\le k+3$** (no restriction $k\le n-1$ is needed).

Every one of the nine pairs of the claim satisfies $k=1$ or $n\le k+3$: $(3,1),(4,1),(5,1)$ have $k=1$;
$(3,2),(4,3),(5,4)$ have $n=k+1$; $(4,2),(5,3)$ have $n=k+2$; $(5,2)$ has $n=k+3$. The general statement covers
infinitely many further pairs, for example $(6,3),(6,4),(7,4),(8,5)$. In closed form it says
$M(n,k)=n-1$ for $n\le k+1$, $M(k+2,k)=k+2$ for all $k\ge1$, and $M(k+3,k)=k+4$ for all $k\ge 2$.

---

## 0. Conventions and notation

An automaton is $\mathcal A=(Q,\Sigma)$ with $Q=\{0,\dots,n-1\}$, every letter $a\in\Sigma$ a map $Q\to Q$ fixing $0$,
acting on the right: $q\cdot a$; words act by composition, $q\cdot(uv)=(q\cdot u)\cdot v$, and
$S\cdot w=\{q\cdot w: q\in S\}$. Put $P=Q\setminus\{0\}$ (the nonzero states). For $S\subseteq Q$ with $0\in S$, the
*active part* of $S$ is $S\setminus\{0\}$. Since $0$ is fixed by every letter, $0\in Q\cdot w$ for every $w$, and $w$
is a reset word iff $Q\cdot w=\{0\}$, i.e. iff $q\cdot w=0$ for all $q$. For $S\ni 0$ let $\operatorname{rt}(S)$ be
the least length of a word $w$ with $S\cdot w=\{0\}$ (or $\infty$); $\operatorname{rt}(\mathcal A)=\operatorname{rt}(Q)$.
For $q\in Q$ let $d(q)=\operatorname{rt}(\{0,q\})$, the distance from $q$ to $0$.

Two facts used throughout without comment:

* (Monotonicity) if $S\subseteq S'$ then $S\cdot w\subseteq S'\cdot w$, hence $\operatorname{rt}(S)\le \operatorname{rt}(S')$.
* (Killing step) if $q\in S\setminus\{0\}$ and $q\cdot w=0$, then $S\cdot w$ has at most $|S\setminus\{0\}|-1$ active
  states, because $q$ and $0$ have the same image.

Also $d(q\cdot a)\ge d(q)-1$ for every letter $a$ (a word of length $d(q\cdot a)$ sends $q\cdot a$ to $0$, so $a$
followed by it sends $q$ to $0$).

The graph $G=G(\mathcal A)$ has vertex set $P$ and an edge $p\to p\cdot a$ for each $p\in P$ and $a\in\Sigma$ with
$p\cdot a\neq 0$. A path in $G$ is labelled by a word, and a path never visits $0$. We say $\mathcal A$ is
*strongly connected (SC)* if $G$ is strongly connected (for $|P|=1$ this holds trivially).

Put $Z=\{q\in P:\ \exists a\in\Sigma,\ q\cdot a=0\}=\{q: d(q)=1\}$ and $Y=P\setminus Z$.

**The game.** We use the k-game of the claim. A *round* is: Alice plays a letter, then Bob plays a word of length
$<k$ (possibly empty). The history is the concatenation of all moves so far. Alice wins as soon as the history is a
reset word. $\mathcal A$ is $A_k$ if Alice has a strategy (a function from histories to letters) winning against
every behaviour of Bob. Unless stated otherwise Alice moves first; Lemma 1 shows this does not matter.

---

## 1. Basic lemmas

**Lemma 1 (first move; synchronization).** Let $k\ge1$.
(a) Alice has a winning strategy when she moves first iff she has one when Bob moves first.
(b) If $\mathcal A$ is $A_k$ then $\operatorname{rt}(\mathcal A)<\infty$; in particular $d(q)<\infty$ for every $q$.

*Proof.* (a) Suppose Alice wins moving first with strategy $\sigma$. In the Bob-first game, after Bob's opening word
$u$, Alice plays $\sigma$ as if the game started now; if $h$ is the history produced after the opening, the true
history is $uh$. Since $\sigma$ wins, some prefix $h'$ of $h$ has $Q\cdot h'=\{0\}$, and
$Q\cdot uh'\subseteq Q\cdot h'=\{0\}$ because $Q\cdot u\subseteq Q$. Conversely, a winning strategy for the Bob-first
game wins in particular against Bob openings with the empty word; Alice uses its reply to that opening as her first
move and continues with it, and every Alice-first play is then a Bob-first play with empty opening.
(b) Let Bob always play the empty word. Alice's winning strategy then produces a reset word. $\square$

**Lemma 2 (classical bound for $k=1$).** Let $\mathcal A$ be a synchronizing automaton with sink $0$ and $n$
states. Then $\operatorname{rt}(S)\le\sum_{j=1}^{m}(n-j)$ for every $S\ni0$ with $m$ active states; in particular
$\operatorname{rt}(\mathcal A)\le n(n-1)/2$.

*Proof.* Induction on $m$; $m=0$ is trivial. Let $A=S\setminus\{0\}$, $|A|=m\ge1$, and pick $q\in A$ with $d(q)=:d$
minimal over $A$ ($d<\infty$ since $\mathcal A$ is synchronizing). Let $q=p_0\to p_1\to\dots\to p_d=0$ be the states
along a shortest word $w$ with $q\cdot w=0$. Then $d(p_i)=d-i$, so $p_1,\dots,p_{d-1}$ are distinct, nonzero, and not
in $A$ (their distance is below the minimum over $A$). Hence $d-1\le |P\setminus A|=n-1-m$, i.e. $d\le n-m$. By the
killing step $S\cdot w$ has at most $m-1$ active states, so by induction
$\operatorname{rt}(S)\le (n-m)+\sum_{j=1}^{m-1}(n-j)$. $\square$

**Lemma 3 (reduction to the strongly connected case).** Let $k\ge1$ and let $\mathcal A$ be an $A_k$ automaton with
sink and $n$ states such that $G$ is not strongly connected. Then there are $A_k$ automata with sink $\mathcal A'$ and
$\mathcal B$ with $c+1$ and $n-c$ states respectively, for some $1\le c\le n-2$, such that
$\operatorname{rt}(\mathcal A)\le\operatorname{rt}(\mathcal A')+\operatorname{rt}(\mathcal B)$.

*Proof.* Since $G$ is not strongly connected, it has a source strongly connected component $C\subsetneq P$ (no edge
of $G$ enters $C$ from $P\setminus C$); put $c=|C|$, so $1\le c\le n-2$. Let $R=Q\setminus C$. Then $R$ is closed
under every letter: $0\cdot a=0$, and for $q\in P\setminus C$, $q\cdot a$ is $0$ or a vertex reached by an edge from
$q$, which is not in $C$.

*The subautomaton $\mathcal B$* has states $R$ (sink $0$) and the letters of $\Sigma$ restricted to $R$; it has $n-c$
states.

*The quotient $\mathcal A'$* has states $C\cup\{0\}$ (sink $0$) and, for each $a\in\Sigma$, the letter
$q\cdot' a=q\cdot a$ if $q\in C$ and $q\cdot a\in C$, and $q\cdot' a=0$ otherwise. Let $\pi:Q\to C\cup\{0\}$ be the
identity on $C$ and send $R$ to $0$. Then $\pi(q\cdot a)=\pi(q)\cdot' a$ for all $q,a$: for $q\in C$ this is the
definition, and for $q\in R$ both sides are $0$ because $R$ is closed. By induction on length,
$\pi(q\cdot w)=\pi(q)\cdot' w$ for all words $w$, so $\pi(S\cdot w)=\pi(S)\cdot' w$.

*Both are $A_k$.* Let $\sigma$ be Alice's winning strategy in $\mathcal A$; she uses the same $\sigma$ (histories are
words over the same alphabet $\Sigma$) in $\mathcal B$ and in $\mathcal A'$. Every play of either game is a play of
the game on $\mathcal A$, so some prefix $h$ of the history has $Q\cdot h=\{0\}$. Then $R\cdot h\subseteq Q\cdot h=\{0\}$
and $(C\cup\{0\})\cdot' h=\pi(Q)\cdot' h=\pi(Q\cdot h)=\{0\}$.

*The bound.* Let $u$ be a shortest reset word of $\mathcal A'$ and $v$ one of $\mathcal B$. For $q\in C$,
$\pi(q\cdot u)=q\cdot' u=0$, so $q\cdot u\in R$; for $q\in R$, $q\cdot u\in R$. Thus $Q\cdot u\subseteq R$ and
$Q\cdot uv\subseteq R\cdot v=\{0\}$. $\square$

**Lemma 4 (superadditivity of $f_k$).** For $k\ge1$ and $1\le c\le n-2$: $f_k(c+1)+f_k(n-c)\le f_k(n)$.

*Proof.* $f_k(n)-f_k(n-c)=\sum_{i=n-c}^{n-1}\lceil i/k\rceil=\sum_{t=1}^{c}\lceil (n-c-1+t)/k\rceil\ge
\sum_{t=1}^{c}\lceil t/k\rceil=f_k(c+1)$, since $n-c-1\ge0$. $\square$

---

## 2. Structure of strongly connected $A_k$ automata

**Lemma 5 (few states without a killing letter).** Let $k\ge1$ and let $\mathcal A$ be an SC $A_k$ automaton with
sink. If $Y\neq\emptyset$ then $|Z|\ge k$; equivalently $|Y|\le n-1-k$.

*Proof.* Suppose $Y\ne\emptyset$ and $|Z|\le k-1$. For each $x\in Z$ choose a shortest path in $G$ from $x$ to a state
of $Y$; it exists because $G$ is strongly connected and $Y\neq\emptyset$. Its states before the last one are distinct
and lie in $Z$ (by minimality), so its length is at most $|Z|\le k-1$. Let $u_x$ be its label: $|u_x|<k$ and
$x\cdot u_x\in Y$.

Fix $y\in Y$ and let Bob play as follows, tracking the token $t=y\cdot h$ ($h$ the current history). We claim that at
each of Alice's turns $t\in Y$. Initially $t=y$. If $t\in Y$ and Alice plays $a$, then $t\cdot a\neq0$ because
$t\notin Z$. If $t\cdot a\in Y$, Bob plays the empty word. If $t\cdot a=x\in Z$, Bob plays $u_x$, which moves the
token along a path of $G$ (never through $0$) to $x\cdot u_x\in Y$. So the token is nonzero after every move, no
prefix of the history sends $y$ to $0$, and no prefix is a reset word. Alice's strategy does not win against this
Bob, contradicting $A_k$. $\square$

**Lemma 6 (distances).** Let $\mathcal A$ be an automaton with sink in which every state has finite distance, and
suppose $Y\neq\emptyset$. Then (a) $\min_{y\in Y}d(y)=2$; (b) $D:=\max_{q\in P}d(q)\le |Y|+1$; (c) if $|Y|=1$, the
unique $y\in Y$ has $d(y)=2$.

*Proof.* (a) Every $y\in Y$ has $d(y)\ge2$. Let $y$ minimize $d$ over $Y$ and let $y\cdot a$ be the first state on a
shortest path to $0$; then $d(y\cdot a)=d(y)-1$. If $d(y)\ge3$ then $d(y\cdot a)\ge 2$, so $y\cdot a\in Y$ has smaller
distance, a contradiction. (b) Along a shortest path $q=p_0,\dots,p_D=0$ from a state with $d(q)=D$, the states
$p_0,\dots,p_{D-2}$ have distances $D,\dots,2$; they are distinct and lie in $Y$, so $D-1\le|Y|$. (c) follows from
(a). $\square$

**Lemma 7 (no way back up).** Let $k\ge2$ and let $\mathcal A$ be an $A_k$ automaton with sink and $Y=\{y_1,y_2\}$,
$d(y_1)=2$, $d(y_2)=3$. Then (a) every letter maps $y_2$ into $\{y_1,y_2\}$, and some letter $c$ has $y_2\cdot c=y_1$;
(b) no letter maps $y_1$ to $y_2$.

*Proof.* (a) For every letter $x$, $d(y_2\cdot x)\ge d(y_2)-1=2$, so $y_2\cdot x\in Y$. A shortest word sending $y_2$
to $0$ starts with a letter $c$ with $d(y_2\cdot c)=2$, so $y_2\cdot c\ne y_2$ and hence $y_2\cdot c=y_1$.
(b) Suppose $y_1\cdot b=y_2$ for a letter $b$. Bob tracks $t=y_2\cdot h$ and keeps $t=y_2$ at Alice's turns: if
Alice's letter $x$ gives $y_2\cdot x=y_2$ he plays the empty word; otherwise $y_2\cdot x=y_1$ by (a), and he plays
$b$ (allowed since $1<k$). The token is never $0$, so no prefix of the history is a reset word, contradicting
$A_k$. $\square$

**Lemma 8 (greedy accounting).** Let $\mathcal A$ be an automaton with sink, $n$ states, every state of finite
distance. Then
$$\operatorname{rt}(\mathcal A)\le \max\Big(\{n-1\}\cup\big\{(n-1-|A|)+\operatorname{rt}(A\cup\{0\}):\ \emptyset\ne A\subseteq Y\big\}\Big).$$
The maximum is over a finite nonempty set of integers, since it always contains $n-1$. When $Y=\emptyset$ the second
set is empty and the bound reads $\operatorname{rt}(\mathcal A)\le n-1$.

*Proof.* Build a reset word greedily from $S_0=Q$. While the active part $A$ of the current set meets $Z$, apply one
letter sending some $q\in A\cap Z$ to $0$; by the killing step this lowers the number of active states by at least
one. If the active part becomes empty this way, at most $n-1$ letters were used; this is the only possible outcome
when $Y=\emptyset$, because then every nonempty active part meets $Z=P$. Otherwise, at the first moment
the active part $A$ is nonempty and contained in $Y$, at most $(n-1)-|A|$ letters have been used, and a further
$\operatorname{rt}(A\cup\{0\})$ letters finish the reset. $\square$

---

## 3. Upper bounds

**Proposition 9 (strongly connected case).** Let $k\ge1$ and let $\mathcal A$ be an SC $A_k$ automaton with sink and
$n$ states.
(a) If $n\le k+1$ then $\operatorname{rt}(\mathcal A)\le n-1$.
(b) If $n=k+2$ then $\operatorname{rt}(\mathcal A)\le n=k+2$.
(c) If $n=k+3$ and $k\ge2$ then $\operatorname{rt}(\mathcal A)\le n+1=k+4$.

*Proof.* By Lemma 1(b) all distances are finite, so Lemmas 6 and 8 apply. If $Y=\emptyset$, Lemma 8 (whose second
set is then empty) gives $\operatorname{rt}\le n-1$, which is at most each of the three bounds. Assume $Y\ne\emptyset$; by Lemma 5,
$|Y|\le n-1-k$.

(a) $n\le k+1$ gives $|Y|\le0$, a contradiction; so $Y=\emptyset$.

(b) $|Y|\le1$, so $Y=\{y\}$ and $d(y)=2$ by Lemma 6(c). The only nonempty $A\subseteq Y$ is $\{y\}$, and Lemma 8 gives
$\operatorname{rt}\le\max(n-1,(n-2)+2)=n$.

(c) $|Y|\le 2$ and, by Lemma 6(b), $D\le3$. By Lemma 8 it suffices to show
$(n-1-|A|)+\operatorname{rt}(A\cup\{0\})\le n+1$ for every nonempty $A\subseteq Y$.

* $|A|=1$, $A=\{y\}$: $\operatorname{rt}(A\cup\{0\})=d(y)\le D\le 3$, giving $(n-2)+3=n+1$.
* $|A|=2$: then $A=Y=\{y_1,y_2\}$, and we show $\operatorname{rt}(\{0,y_1,y_2\})\le4$, giving $(n-3)+4=n+1$.
  By Lemma 6(a) we may label so that $d(y_1)=2$.
  - If $d(y_2)\le2$: let $w$ with $|w|=2$ and $y_1\cdot w=0$. Then $\{0,y_1,y_2\}\cdot w$ has at most the one active
    state $r=y_2\cdot w$, and $d(r)\le D$. Since $D\le 2$ in this subcase (both states of $Y$ have distance 2 and
    $Z$-states have distance 1), the total is at most $2+2=4$.
  - If $d(y_2)=3$: take $c$ as in Lemma 7(a), so $\{y_1,y_2\}\cdot c=\{y_1\cdot c,\ y_1\}$. Here $y_1\cdot c\ne0$
    ($y_1\notin Z$) and $y_1\cdot c\ne y_2$ (Lemma 7(b)), so $y_1\cdot c\in\{y_1\}\cup Z$. If $y_1\cdot c=y_1$, the
    active part is $\{y_1\}$ and two more letters finish: total $3$. If $y_1\cdot c=z\in Z$, apply a letter $b$ with
    $z\cdot b=0$. The active part becomes at most the single state $y_1\cdot b$, and $y_1\cdot b\ne y_2$ by
    Lemma 7(b), so it lies in $\{0,y_1\}\cup Z$ and has distance at most $2$. Total at most $1+1+2=4$. $\square$

**Proposition 10 (upper bound).** Let $k\ge1$ and let $\mathcal A$ be an $A_k$ automaton with sink and $n$ states.
If $k=1$, or if $n\le k+3$ (with $k\ge2$ when $n=k+3$), then $\operatorname{rt}(\mathcal A)\le f_k(n)$.

*Proof.* For $k=1$, $f_1(n)=n(n-1)/2$, and Lemmas 1(b) and 2 give the bound. Now fix $k\ge2$. We first record the
values $f_k(m)=m-1$ for $m\le k+1$ (every term is $1$), $f_k(k+2)=k+2$, and $f_k(k+3)=k+4$ (the terms
$i=k+1,k+2$ equal $2$ because $k+2\le 2k$). We then prove the bound by strong induction on $n\le k+3$. For $n=1$,
$\operatorname{rt}=0$. Let $n\ge2$.
If $G$ is SC, Proposition 9 gives exactly $f_k(n)$ in each of the three ranges. If $G$ is not SC, Lemma 3 gives $A_k$
automata with $c+1$ and $n-c$ states, both fewer than $n$, so the induction hypothesis applies. Lemma 4 then gives
$\operatorname{rt}(\mathcal A)\le f_k(c+1)+f_k(n-c)\le f_k(n)$. $\square$

(The same induction with only Proposition 9(a) reproves the Lipin–Volkov endpoint $M(n,n-1)\le n-1$, and more
generally $M(n,k)\le n-1$ for $n\le k+1$: every automaton met in the induction has at most $k+1$ states. For $k=1$
it reaches only $n\le2$. The SC three-state case at $k=1$ needs Proposition 9(b) or Lemma 2; for example $\beta=(0,0,2)$,
$\tau=(0,2,1)$ on $\{0,1,2\}$ is SC and $A_1$ with $\operatorname{rt}=3$. Proposition 10 itself treats $k=1$ by
Lemma 2, the classical sink bound $M(n,1)\le n(n-1)/2$.)

---

## 4. Lower bounds: explicit extremal automata

**Lemma 11 (potential bound).** Let $w:P\to\mathbb Z_{\ge0}$ and $\Phi(A)=\sum_{q\in A}w(q)$ for $A\subseteq P$. Suppose
that, for every letter $a$ and every $A\subseteq P$, $\Phi((A\cdot a)\setminus\{0\})\ge\Phi(A)-1$. Then
$\operatorname{rt}(\mathcal A)\ge\Phi(P)$.

*Proof.* For a reset word $v$ of length $\ell$, induction on prefixes gives $0=\Phi((P\cdot v)\setminus\{0\})\ge\Phi(P)-\ell$.
$\square$

**Lemma 12 ($k=1$: transposition automaton).** For $n\ge2$ let $\mathcal T_n$ have states $0,\dots,n-1$ and letters
$\beta$ ($1\mapsto0$, all other states fixed) and $\tau_i$ for $1\le i\le n-2$ (swap $i,i+1$, all other states fixed). Then
$\mathcal T_n$ is $A_1$ and $\operatorname{rt}(\mathcal T_n)=n(n-1)/2$.

*Proof.* Take $w(q)=q$. The letter $\beta$ changes $\Phi$ by $-[1\in A]$. The letter $\tau_i$ is a permutation and
changes $\Phi$ by $+1$, $-1$ or $0$ according to which of $i,i+1$ lie in $A$. By Lemma 11,
$\operatorname{rt}\ge\sum_{q=1}^{n-1}q=n(n-1)/2$. Conversely, $\beta$ sends $P$ to $\{2,\dots,n-1\}$. If the active
set is $\{j+1,\dots,n-1\}$ ($1\le j\le n-2$), then $\tau_j\tau_{j-1}\cdots\tau_1$ makes it
$\{1,j+2,\dots,n-1\}$, and $\beta$ makes it $\{j+2,\dots,n-1\}$; this costs $j+1$ letters. So
$\beta\,(\tau_1\beta)(\tau_2\tau_1\beta)\cdots(\tau_{n-2}\cdots\tau_1\beta)$ is a reset word of length
$\sum_{j=0}^{n-2}(j+1)=n(n-1)/2$. In the 1-game Bob only plays the empty word, so Alice wins by playing this word. $\square$

**Lemma 13 ($n\le k+1$: path automaton).** For $n\ge2$ let $\mathcal P_n$ have one letter $a$ with $q\cdot a=q-1$ for
$q\ge1$ and $0\cdot a=0$. Then $\operatorname{rt}(\mathcal P_n)=n-1$, and $\mathcal P_n$ is $A_k$ for every $k\ge1$.

*Proof.* Every word is $a^m$, and $a^m$ is a reset word iff $(n-1)\cdot a^m=0$, i.e. iff $m\ge n-1$. Whatever Bob
does, after Alice's $(n-1)$-st letter the history is $a^m$ with $m\ge n-1$. $\square$

**Lemma 14 (cycle automata).** Let $k\ge1$ and $m\ge1$. Let $\mathcal C_{k,m}$ have
states $0$ and $c_0,c_1,\dots,c_{k+m-1}$ (so $n=k+m+1$) and letters
$e$: $c_i\mapsto c_{i+1\bmod (k+m)}$, $0\mapsto0$; and, for $1\le i\le k$, $\beta_i$: $c_i\mapsto0$, all other states
fixed. Write $K=\{c_1,\dots,c_k\}$ and $O=P\setminus K=\{c_0,c_{k+1},\dots,c_{k+m-1}\}$ ($|O|=m$). Then
$\mathcal C_{k,m}$ is $A_k$ and $\operatorname{rt}(\mathcal C_{k,m})=k+2m$. For $1\le m\le k$ this equals
$f_k(k+m+1)$; in particular $\operatorname{rt}(\mathcal C_{k,1})=k+2=f_k(k+2)$, and for $k\ge2$,
$\operatorname{rt}(\mathcal C_{k,2})=k+4=f_k(k+3)$. Moreover $\mathcal C_{k,m}$ is not $A_{k+1}$.

*Proof.* *Lower bound.* Let $w=1$ on $K$ and $w=2$ on $O$, so $\Phi(P)=k+2m$. The letter
$\beta_i$ changes $\Phi$ by $-[c_i\in A]$. The letter $e$ is a permutation of $P$ and changes $\Phi$ by
$-[c_0\in A]+[c_k\in A]$ (only the moves $c_0\to c_1$ and $c_k\to c_{k+1\bmod(k+m)}\in O$ change weight; $e$ maps
$c_1,\dots,c_{k-1}$ into $K$ and $c_{k+1},\dots,c_{k+m-1}$ into $O$). So Lemma 11 gives $\operatorname{rt}\ge k+2m$.

*Upper bound.* $\beta_1\cdots\beta_k$ leaves the active set $O$. For $0\le j\le m-1$ put
$O_j=\{c_0\}\cup\{c_{k+s}: j+1\le s\le m-1\}$, so $O_0=O$ and $O_{m-1}=\{c_0\}$. The letter $e$ maps $O_j$ to
$\{c_1\}\cup\{c_{k+s}: j+2\le s\le m\}$, where $c_{k+m}=c_0$; for $j\le m-2$ this is $\{c_1\}\cup O_{j+1}$, and for
$j=m-1$ it is $\{c_1\}$. Then $\beta_1$ removes $c_1$ and fixes the rest. So $O_j\cdot e\beta_1=O_{j+1}$ for $j\le m-2$
and $O_{m-1}\cdot e\beta_1=\emptyset$ (active parts). Thus $\beta_1\cdots\beta_k(e\beta_1)^m$ is a reset word of length
$k+2m$. (For $m=2$ this is $\{c_0,c_{k+1}\}\to\{c_1,c_0\}\to\{c_0\}\to\{c_1\}\to\emptyset$.)

*$A_k$.* Alice uses the positional strategy: if the current active set $T$ meets $K$, play $\beta_i$ for some
$c_i\in T\cap K$; otherwise play $e$. We show that from every nonempty $T$ with Alice to move, the number of active
states strictly drops within at most $m+1$ rounds, whatever Bob plays. No move can raise this number. So Alice wins
from every position, hence from $Q$, whether she or Bob moves first. Every letter maps distinct nonzero states to
distinct states ($e$ is a permutation, $\beta_i$ fixes all nonzero states but $c_i$), so the count drops in a round iff
some token is sent to $0$ in that round.

A single token at $c_j$ under a word $u$ of Bob's ($|u|\le k-1$) either goes to $0$ or ends at $c_{j+r\bmod(k+m)}$,
where $r\le k-1$ is the number of letters $e$ in $u$. This holds because $\beta_i$ fixes or kills it and $e$ advances
it by one. Hence in a round in which Alice plays $e$, a surviving token advances by exactly $s=1+r$ positions, with
$1\le s\le k$.

For $c\in O$ let $\delta(c)\in\{1,\dots,m\}$ be the number of applications of $e$ that take $c$ to $c_1$
($\delta(c_0)=1$, $\delta(c_{k+t})=m-t+1$ for $1\le t\le m-1$). From $c\in O$, advancing by $s$ positions with
$1\le s<\delta(c)$ ends in $O$ at $\delta$-value $\delta(c)-s$. Advancing by $s$ with
$\delta(c)\le s\le\delta(c)+k-1$ ends in $K$. Since $s\le k\le\delta(c)+k-1$, every round of $e$ followed by Bob's
reply either sends the token into $K$ or strictly lowers its $\delta$-value, unless the token is killed.
* If $T\cap K\ne\emptyset$, Alice's $\beta_i$ kills a token: the count drops in one round.
* If $T\cap K=\emptyset$, then $T\subseteq O$. Fix a token of $T$, at $c$ with $\delta(c)\le m$. While the count has not
  dropped, the token survives, the active set misses $K$ at Alice's turn (else we are in the first case), Alice plays
  $e$, and by the above the token either enters $K$ or lowers its $\delta$-value by at least $1$. So within at most
  $m$ rounds the count drops or the token lies in $K$ at Alice's turn, and then the count drops in the next round.
  The count drops within $m+1$ rounds.

*Not $A_{k+1}$.* In the $(k+1)$-game Bob may reply with any word of length $\le k$. Bob tracks the token $t=c_0\cdot h$
and keeps it in $O$ at each of Alice's turns. If Alice plays some $\beta_i$, $t\in O$ is fixed and Bob passes. If Alice
plays $e$ and $t=c_{k+s}$ ($1\le s\le m-1$), the token moves to $c_{k+s+1}\in O$ (with $c_{k+m}=c_0$) and Bob passes.
If Alice plays $e$ and $t=c_0$, the token moves to $c_1$ and Bob plays $e^k$, which moves it to
$c_{k+1\bmod(k+m)}\in O$. Only letters $e$ act on it while it is in $K$, so it is never sent to $0$, and no prefix of
the history is a reset word. If Bob moves first he opens with the empty word (Lemma 1(a)).

Finally, for $1\le m\le k$, $f_k(k+m+1)=\sum_{i=1}^{k}1+\sum_{i=k+1}^{k+m}2=k+2m$, since $k<i\le k+m\le 2k$ gives
$\lceil i/k\rceil=2$. In particular $f_k(k+2)=k+2$ for $k\ge1$ and $f_k(k+3)=k+4$ for $k\ge2$, as in
Proposition 10. $\square$

(For $m\le k$ the automata $\mathcal C_{k,m}$ thus give self-contained witnesses $M(n,k)\ge f_k(n)$ for
$k+2\le n\le 2k+1$. This range is already covered by the Lipin–Volkov construction $L^k_m$. For $m>k$ the
threshold $k+2m$ falls below $f_k(k+m+1)$. Only $m\in\{1,2\}$ is used in the Theorem.)

(For $k=2$, $m=2$: $\mathcal C_{2,2}$ has states $0,c_0,c_1,c_2,c_3$, letters $e=(c_0\,c_1\,c_2\,c_3)$, $\beta_1$, $\beta_2$,
and $\beta_1\beta_2e\beta_1e\beta_1$ is a shortest reset word, of length $6$.)

---

## 5. Main result

**Theorem.** Let $k\ge1$ and $n\ge2$ (no relation between $k$ and $n$ is assumed). If $k=1$, or $n\le k+3$, then
$$M(n,k)=f_k(n)=\sum_{i=1}^{n-1}\left\lceil\tfrac{i}{k}\right\rceil .$$
In particular, for every $3\le n\le5$ and $1\le k\le n-1$, $M(n,k)=f_k(n)$, namely
$M(3,1)=3$, $M(3,2)=2$, $M(4,1)=6$, $M(4,2)=4$, $M(4,3)=3$, $M(5,1)=10$, $M(5,2)=6$, $M(5,3)=5$, $M(5,4)=4$.
So every 5-state $A_2$ automaton with a sink has a reset word of length at most $6$, and $6$ is attained.

*Hypotheses.* $M(n,k)$ is the supremum of $\operatorname{rt}$ over all $n$-state $A_k$ automata with sink $0$ over
arbitrary finite alphabets, as defined in CLAIM.md. The game is the k-game of CLAIM.md; by Lemma 1(a) the order of
moves is irrelevant.

*Proof.* *Upper bound.* If $k=1$, or $k\ge2$ and $n\le k+3$, Proposition 10 gives $\operatorname{rt}\le f_k(n)$ for
every $n$-state $A_k$ automaton with sink. So the supremum is finite and $M(n,k)\le f_k(n)$. (The case $k=1$,
$n\le 4=k+3$ is covered by $k=1$.)

*Lower bound.* We exhibit an $n$-state $A_k$ automaton with $\operatorname{rt}=f_k(n)$:
* $k=1$: $\mathcal T_n$ (Lemma 12), with $\operatorname{rt}=n(n-1)/2=f_1(n)$.
* $n\le k+1$ (including $k\ge n$): $\mathcal P_n$ (Lemma 13), which is $A_k$ for every $k\ge1$, with
  $\operatorname{rt}=n-1=f_k(n)$.
* $n=k+2$: $\mathcal C_{k,1}$ (Lemma 14), with $\operatorname{rt}=k+2=f_k(n)$.
* $n=k+3$, $k\ge2$: $\mathcal C_{k,2}$ (Lemma 14), with $\operatorname{rt}=k+4=f_k(n)$.

"$n\le k+3$" means $n\le k+1$, $n=k+2$ or $n=k+3$; with $k=1$ (which covers $n=k+3=4$) every case is listed
above. So $M(n,k)\ge f_k(n)$, and equality follows. For $k\ge n-1$ this reads $M(n,k)=n-1$.

*The nine pairs.* The pairs $(3,1),(4,1),(5,1)$ have $k=1$; $(3,2),(4,3),(5,4)$ have $n=k+1$; $(4,2),(5,3)$ have
$n=k+2$; and $(5,2)$ has $n=k+3$ with $k=2$. The listed values are $f_k(n)$:
$f_1(3)=3$, $f_2(3)=2$, $f_1(4)=6$, $f_2(4)=1+1+2=4$, $f_3(4)=3$, $f_1(5)=10$, $f_2(5)=1+1+2+2=6$,
$f_3(5)=1+1+1+2=5$, $f_4(5)=4$. $\square$

**Remarks.**
1. When $k\mid n-1$, $f_k(n)=(n-1+k)(n-1)/(2k)$, so the Theorem confirms the Lipin–Volkov conjecture whenever
   $n\le k+3$ (in particular $(5,2)$, and $(n,n-1)$ for all $n$), and confirms its ceiling-sum form in the
   non-divisible cases $n\in\{k+2,k+3\}$, for example $(4,2)$, $(5,3)$, $(6,4)$, $(7,5)$.
2. Where the method stops. For $n=k+4$, Lemma 5 gives $|Y|\le3$. Then greedy accounting needs finer control of
   sets $A\subseteq Y$ with $|A|\in\{2,3\}$ and of depth $D\le4$. Lemma 7 has to be extended to longer escape
   words. This case analysis was not carried out here, so the general conjecture is not claimed beyond $n\le k+3$.
3. The extremal automata for $n=k+2,k+3$ are strongly connected, as Lemmas 3 and 4 force: when $c\le n-2$ the
   inequality of Lemma 4 is strict for $n\in\{k+2,k+3\}$, so a non-SC automaton cannot reach $f_k(n)$ there.
   This remark is not used in the proof.

---

## Appendix A. Computational record (corroboration only; not a premise of any step)

This appendix records the earlier exhaustive computation that CLAIM.md refers to. It is included because
COMPUTATION.md in the packet is an empty template. Nothing above depends on it.

* **Location.** `/Users/ben/conductor-lab/agents/runs/2026-10-24_research-sink-ak-small/isolated/audit-1/`.
* **Verifier.** `verifier__verify.py`, SHA-256 `456ff3770a2f5256a23d8732f217fd87d40ad6eb21c14d43b202b42b53ff9c7f`.
* **Certificate.** `experiment__out__cert.json`, SHA-256
  `72af5a40653bb796a3132ede643129ef81ea718b33b71e18905dfdc0cf36ceb5`.
* **Stored verification record.** `verifier__results__20261024T083044703883.json` (lines 6–12 hold the two hashes
  above and the PASS outcome).
* **Reproduction.** Run from any directory:
  `python3 -I -B <dir>/verifier__verify.py <dir>/experiment__out__cert.json`, where `<dir>` is the location above.
  Expected exit status is 0, with the single output line
  `PASS M(n,k) = sum_i ceil(i/k) for all 9 cases 3<=n<=5, 1<=k<=n-1; 72 witnesses checked; every maximum recomputed exhaustively over all alphabets of <= n-1 letters (n<=4 by two engines; n=5 bit-parallel)`.
* **What it checks.** The verifier imports no searcher code. It recomputes every maximum exhaustively
  (`verifier__verify.py:340–352`) rather than trusting the certificate's `complete` flag. It also checks the 72
  witness automata.
* **Assumptions it relies on** (`verifier__README.md:47–69`). (i) The token game and the active-set game are equivalent.
  (ii) A positional winning strategy uses at most $n-1$ distinct letters, so alphabets of at most $n-1$ letters
  suffice. (iii) Padded alphabet multisets modulo relabelling of nonzero states cover all cases. Informational orbit
  counts are *not* independently certified (`README:26–28`, `verify.py:329–331`); the maxima do not depend on them.
* **Provenance of this record.** The hashes were matched against the stored record by the Astra adversary (job
  20261024T091633). The Astra reviewer (job 20261024T092424) independently reran the command above, with exit
  status 0, the output line above, and matching `shasum -a 256` hashes. This responder could not read that directory
  in the current round, so the entries above are transcribed from those two audit transcripts and were not
  re-executed here.
* **Status.** The Theorem is a handwritten proof (Sections 1–5). The computation is independent corroboration for
  $3\le n\le 5$; it is neither formal verification nor a premise.

---

## Appendix B. Packet errata (to be applied at packaging; not part of the proof)

The proof loop does not allow the responder to edit CLAIM.md or CONTEXT.md, and COMPUTATION.md is not in the
responder's working copy. The corrections below are therefore recorded here verbatim, for P-package to apply. Until
they are applied, this appendix, the Literature status paragraph and Appendix A supersede the quoted passages (see
"Status of this file"). None of them changes the mathematical statement of CLAIM.md, which is true and is proved
above.

1. **CLAIM.md line 9, literature status.** Replace "the general conjecture remains open." with: "no resolution of the
   general conjecture was located in the inspected sources (arXiv:2601.18362v1, §§2.1 and 3.4; the CiE 2026 chapter,
   doi:10.1007/978-3-032-31348-5_24, was not inspected in full text)."
2. **CLAIM.md line 9, location of the computation.** Replace "The computation and its independent verification are
   in COMPUTATION.md and EVIDENCE.md." with: "An earlier exhaustive computation for $3\le n\le5$ corroborates the
   statement. Its artifacts, hashes and reproduction command are recorded in PROOF.md Appendix A (and in
   COMPUTATION.md once item 4 is applied), and its methodology audit in EVIDENCE.md. The statement is proved by hand
   in PROOF.md, which uses no computation."
3. **CONTEXT.md line 5, status label.** Replace "literature status OPEN_ASYMPTOTIC checked 2026-10-24" with:
   "literature status OPEN_ASYMPTOTIC as classified by the discovery status gate on 2026-10-24 (framing A: UNCLEAR;
   framing B: OPEN). This means no resolution was located in the inspected sources; the CiE 2026 full text was not
   inspected. It is not a certification of current open status."
4. **COMPUTATION.md.** Replace the empty template body with the text of Appendix A above, from "**Location.**" to
   "**Status.**" inclusive.
