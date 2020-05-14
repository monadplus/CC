# Chapter 8. Interactive proofs

**Verifier**: person verifying the proof

**Prover**: person providing he proof.

Example, can one prove in a succint way that a given formula is _not satisfiable_ ? This problem is coNP-complete, and hence is believed to not have a polynomial-sized proof in the traditional sense. The surprising fact is that it does have succint proofs when the verifier is allwoed to interact with the prover, and in fact so does TQBF and every other problem in PSPACE.

### 8.1 Interactive Proofs: Some variations

Interactive proofs introduce _interaction_ into the basic NP scenario.

Intead of the prover sending a written proof to the verifier, the verifier conducts an interrogation to the prover, repeatedly asking questions and listening to the prover's responses. At the end, the verifier decides whether or not to accept the input.

#### 8.1.1. Warmup: Interactive proofs with deterministic verifier and prover

Example, interactive proof for membership in 3SAT. Proceeding clause by clause, the verifier asks the prover to announce the values for the literals in the clause. The verifier keeps a record of these answers, and accepts at the end if al lclauses were indeed satisfied, and the prover never announced conflicting values for a variable. Thus both verifier and prover are deterministic.

Of course, in this case we may well ask what hte point of interaction is, as the prover could just announce values of all clauses in the very first round, and then take a nap from then on.

Interactive proofs with deterministic verifiers never need to last more than a single round.

**Def 8.2** (Interaction of deterministic functions) Let f,g : {0,1}* \to {0,1}* to be functions and k \geq 0 be an integer (allowed to depend upon the input size). A k-round interaction of f and g on onput x \in {0,1}*, denoted by $\langle f,g \rangle (x)$ is the sequence of strings

```
a_1,...,a_k \in {0,1}* defined as follows:

  a_1 = f(x)
  a_2 = g(x, a_1)
      ....
  a_{2i+1} = f(x, a_1, ..., a_{2i})         for 2i < k
  a_{2i+2} = g(x, a_1, ..., a_{2i+1})       for 2i + 1 < k
```

The _output_ of f at the end of the interaction denoted $out_f \langle f,g \rangle (x)$ is defined to be $f(x, a_1, ..., a_k$; we assme this output is in {0,1}.

**Def 8.3** (Deterministic proof systems) We say that a language L has a k-round deterministic interactive proof system if there's a deterministic TM V that on input x,a_1,...,a_n runs in time polynomial in |x|, and can have a k-round interaction with any function P such that

(Completeness)   x \in L \implies \exists P : {0,1}* \to {0,1}* out_v<V,P>(x) = 1
(Soundness)      x \notin L \implies \forall P : {0,1}* \to {0,1}* out_v<V,P>(x) = 0


the class **dIP** contains all languages with a k(n)-round deterministic interactive proof system where k(n) is polynomial in n.

Notice, this definition places no limits on the computational power of the prover P; this makes intuitive sense, since a false assertion should not be provable, no matter how clever the prover.

**Lemma 8.4** dIP = NP

Proof. Trivially, every NP language has a one-round deterministic proof system and thus is in dIP. Now we prove that if L \in dIP then L \in NP. If V is the verifier for L, then a certificate that an input is in L is justa transcript (a_1, a_2, ..., a_k) causing the verifier V to accept. To verify this transcript, one checks that indeed V(x) = a_1, V(x,a_1,a_2) = a_3, ..., and V(x,a_1,...,a_k) = 1. If x \in L then such a transcript exists. Converserly, if sucha transcript (a_1,...,a_k) exists then we can define a prover function P to satisfy P(x, a_1) = a_2, P(x,a_1,a_2,a_3) = a_4, and so on. This deterministic prover satisfies out_v<V,P>(x) = 1, which implies x \in L.

#### 8.1.2 The class IP: probabilistic verifier.

The message of Section 8.1.1 is that in order for interaction to provide any benefit, we need to let the verifier be _probabilistic_. Questions are probabilistic. The verifier will be allowed to come to a wrong conclusion with some small probability.

Example 8.5. Sock's color guess game (with color blinded).

Additional m-bit input r

f(x,r) = a_1
f(x,r,a_1,a_2) = a_3

Private coins model: prover cannot "see" the verifier's coins but only his messages' for this reason, this is calle the private coins model for interactive proofs, as opposed to the public coins model.

The interaction <f,g>(x) is now a random variable over r \in_R {0,1}^m.
Similarly the output out_f<f,g>(x) is also a random variable.

**Def. 8.6** (Probabilistic verifiers and the class IP) For an integer k \geq 1 (that may depend on the input length), we say that a language L is in **IP[k]** if there is a probabilistic polynomial-time TM V that can have a k-round interaction with a function P: {0,1}* \to {0,1}* such that

  (Completeness)  x \in L    \implies \exists P Pr[out_v<V,P>(x) = 1] \geq 2/3    (8.2)
  (Soundness)     x \notin L \implies \forall P Pr[out_v<V,P>(x) = 1] \leq 1/3    (8.3)

where all probablities are over the choice of r.

We define **IP** = U_{c \geq 1} IP[n^c]

The probabilities 2/3 and 1/3 can be made arbitrary close to 1 and 0, by using a boosting technique (like we did with BPP).

**Lemma 8.7**. The class IP defined in Definition 8.6 is unchanged if we replace the completeness parameter 2/3 by 1-2^{n^s} and the soundness parameter 1/3 by 2^{n^s} for any fixed constant s > 0.

Proof. The verifier repeats the entire protocol over and over again, say _m_ times, and accepts at the end iff more than 1/2 runs resulted in accept. If x \in L, then a prover that can make the verifier accept with probability 2/3 in each repetition will at the end succeed with probability 1-2^{\Omega(m)} by the Chernoff bound. If x \notin L, we have to argue that every prover strategy will fail with high probability. We claim that the prover can succeed in each repetition of the protocol with probability only 1/3 - irrespective of what happened in earlier rounds. The reason is that eeven though the prover's responses in the repetition may depend arbitrarily on its responses in the earlier repetitions, since the expression in (8.3) holds for all provers, it holds in particular for the prover that knows the questions of earlier rounds. Choosing m = O(n^s) completes the proof.

We now make several assertions about the class IP

1. Allowing the prover to be probabilistic, that is, allowing the answer function a_i to depend upon some random string used by the prover, does not change the class IP.

2. Since the prover can use an arbitrary function, it can in principle use unbounded computationa power or even compute undecidable functions. However, we can show that given any verifier V, we can compute the optimum prover using poly(|x|) space (and hance also 2^{poly(|x|)} time). Thus IP \subseteq PSPACE.

3. Replacing the constat 2/3 with 1 in the completness requirement (8.2) does not change the class IP.

4. By contrast, replacing the constant 1/3 with 0 in the soundness condition (8.3) is equivalent to having a deterministic verifier and hence reduces the class IP to NP.

5. Private Coins. Thus far the prover functions do not depend upon the verifier's random strings, only on the messages/questions the verifier sends. In other words, teh verifier's random string is _private_. Often these are called _private coin interactive proofs_. We also consider the model of _public-coin proofs_.

6. The proof of Lemma 8.7 sequentially repeats the basic protocol m times and takes the majority answer. In fact, using a more complicated proof, it can be show that we can decrease the probability without increasing the number of rounds using parallel repetition, where the prover and verifier will run m executions of the protocol in parallel.

#### 8.1.3 Interactive proof for graph noniosomorphism

We present another example of a language in IP that is not known to be in NP.
We say two graphs G_1 and G_2 are isomorphic if they are the same up to a renumbering of vertices; in other words, if there is a permutation \pi of the labels of the nodes of G_1 such that \pi(G_1) = G_2, where \pi(G_1) is the labeled graph obtained by applying \pi on its vertex labels.

If G_1 and G_2 are isomorphic, we write G_1 \cong G_2.

The GI problem is the following: given two graphs G_1,G_2 decide if they are isomorphic.

Clearly GI \in NP, since a certificate is simply the description of the permutation \pi. The graph isomorphism problem is important in a variety of fields and has a rich history. It is open whether GI is NP-complete, and, along with the factoring problem, it is the most famous NP-problem that is not known to be either in P or NP-complete. We show that GI is not NP-complete unless the polynomial hierarchy collapses.

GNI: given two graphs, decide if they are not isomorphic.


**Protocol: Private-coin Graph Nonisomoprhism

V: Pick i \in {1,2} uniformly randomly. Randomly permute the vertices of G_i to get a new graph H. Send H to P.
P: Identify which of G_1, G_2 was used to produce H. Let G_j be that graph. Send j to V.
V: Accept if i = j; reject otherwise.

See that if G_1 is a permutation of G_2, P cannot identify which G_1 or G_2 was randomly permuted in the previous step. Notice, P can guess j with Pr[V accepts} \leq 1/2. This probability can be reduced to 1/3 by sequential or parallel repetition.

**Remark 8.8** (Zero-knowledge proofs)

A zero-knowledge proof system for membership in a language is an interactive proof protocol where the verifier is convinced at the end that the input x is in the language, but learns nothing else. How can we quantify that the verifier learns nothing else ? We do this by showing that the verifier could have produced the transcript of the protocol in polynomial time with no help from the prover.

Cryptography. It raises the possibility of parties being able to prove things to each other without revealing any secrets (e.g. to prove that you hold the password without revealing the password itself).

### 8.2 Public Coins and AM

**Def. 8.10** (AM, MA) For every k the complexity class AM[k] is defined as the subset of IP[k] (def. 8.6) obtained when we restrict the verifier's messages to be random bits, and not allowing it to use any other random bits that are not contained in these messages.

An interactive proof where the verifier has this form is called _public coin proof_, sometimes also know as an Arthur-Merlin proof.

We donete by AM the class AM[2]. That is, **AM** is the class of languages with an interactive proof that cnsist of the verifier sending a random string, and the prover responding with a message, where the verifier's decision is obtained by applying a deterministic polynomial-time function to the transcript.

The class **MA** denotes the class of languages with a two-round public-coin interactive proof with the prover sending the first message. That is, L \in MA if there's a proof system for L that consists of the prover first sending a message, and then the verifier tossing coins and computing its decision by doing a deterministic polynomial-time computation involving the input, the prover's message and coins.

**Remark 8.11** Some properties of the class **AM[k]**:

1. Note that even in a public-coins proof, the prover doesn't get to see immediately all of the verifier's random coins, but rather they are revelaed to the prover iteratively message by message. That is, an AM[k]-proof is an IP[k]-proof where the verifier's random tape r consists of \lceil k/2 \rceil strings r_1,...,r_{k/2}, his ith message is simply the string r_i, and the decision whether to accept or reject is obtained by applying a deterministic polynomial-time computable function to the transcript..

2. AM[2] = BP*NP where BP*NP is the class in def. 7.17. In particular it follows that AM[2] \subseteq \Sigma_3^p.

3. For constants k \geq 2 we have AM[k] = AM[2]. This "collapse" is somewhat surprising because AM[k] at first glace seems similar to PH with the \forall quantifiers changed to "probabilistic \forall" quantifiers.

### 8.2.1 Simulating private coins

Clearly for every k, AM[k] \in IP[k]. The interactive proof for GNI seemed to crucially depend upon the fact that P cannot see the random bits of V. If P knew those bits, P would know i and so could trivially always guess correctly. Thus it may seem that allowing the verifier to keep its coins private adds significant power to the interactive proofs, and so the following result should be quite surprising:

**Theorem 8.12**(Goldwasser-Sipser [GS87]) For every k: N -> N with k(n) computable in poly(n), IP[k] \subseteq AM[k+2]

We sketch the proof of Theorem 8.12 in Section 8.12 after proving the next Thoerem.

**Theorem 8.13** GNI \in AM[2]

The key idea is to look at graph nonisomorphism in a different, more quantitative, way. Consider the following set of labeled graphs S = { H : H \cong G_1 or H \cong G_2 }. Note that it is easy to certify that a graph H is a member of S, by providing the permutation mapping either G_1 or G_2 to H. An n vertex graph G has at most n! equivalent graphs. For simplicity assume first that both G_1 and G_2 have each exactly n! equivalent graphs. The size of S differes by a factor 2 depending upon whether or not G_1 is isomorphic to G_2.

  if G_1 \notcong G_2 then |S| = 2n!   (8.4)
  if G_1 \cong    G_2 then |S| = n!    (8.5)

Now consider the general case where G_1 or G_2 may have less than n! equivalent graphs. An n-vertex graph G has less than n! equivalent graphs iff it has a nontrivial automorphism, which is a permutation \pi that is not the identity permutation and yet \pi(G) = G. Let aut(G) denote the set of automorphisms of graph G. We change the definition of S to

S = {(H, \pi) : H \cong G_1 or H \cong G_2 and \pi \in aut(H)}

Using the fact that aut(G) is a subgroup, one can verify that S satisfies (8.4) and (8.5). Also, membership in this set is easy to certify.

Thus to convince the verifier that G_1 \notcong G_2, the prover has to convince the verifier that case (8.4) holds rather than (8.5). This is done by using a set lower bound protocol.

### 8.2.2 Set lower bound protocol

Suposse there is a set S known to both prover and verifier, such that membership in S is easily certifiable, in the sense that given some string x that happens to be in S, the prover - using its superior computational power - can provide the verifier a certificate to this effect. The _set lower bound protocol_ is a public-coins protocol that allows the prover to _certify_ the approximate size of S. Note that the prover - using its superior computational power- can certainly compute and announce |S|. The question is how to convince the verifier that this answer is correct, or even approximately correct. Suppose the prover's claime value for |S| is K. The protocol below has the property that if the true value of |S| is indeed at least K, then the prover ca cause the verifier to accept with high probability, whereas if the true value of |S| is at most K/2 (the prover's answer is grossly on the high side), then the verifier will reject with high probability, no matter what the prover does. This protocol is called the _set lower bound protocol_ and it clearcly sufficies to complete the proof of Theorem 8.13

Recall **Pairwise independent hash functions**

**The lower-bound protocol**: Goldwasser-Sipser Set Lower Bound Protocol

See the book pg. 153-154.
