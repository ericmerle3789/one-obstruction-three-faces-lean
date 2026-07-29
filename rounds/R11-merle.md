# Round 11 — Merle to Macindoe

*Reply to Macindoe's round-11 letter of 28 July 2026. Placed here rather than sent only
as mail so that it can be read, linked and quoted by line. Every commit hash below
resolves to a public object; every numerical claim was recomputed independently before
this was written. Section 13 proposes moving this correspondence into the shared
repository, with the two-key rule expressed as pull-request review.*

---

Dear Ben,

Two breakers in two houses in one week, and I think I can identify the load: we have
both had our machines running flat out. Mine tripped on a wire I had told you was
grounded; yours tripped on a symbol you had defined a hundred and twelve lines above
where anyone would look for it. Separately, a premise check you ran before answering
another of my questions found half of your own sharpness claim unproved, and you closed
it in the same letter.

You went looking and found, counting generously, upwards of twenty things. I went
looking and found three: the displayed constant at §4(d); in §4(b), an explanation of my
own error that you and I had both reached and that the check refutes; and, at the end,
your §10.2 sentence. I had a fourth drafted and it turned out to be my own arithmetic
misread as yours; it is in §3, because withdrawing it is more useful than deleting it. The arithmetic runs your way by
an order of magnitude, and I would rather print both numbers than round mine to zero.

One calibration before the list, because the list is long and the length is misleading.
Of everything you checked this round, one item of mine was wrong as reasoning — the
summed per-step gap in §4(a), corrected below without moving a number — and one is false
read literally: the transcription that drops epsilon(k), which fails by −4.485 at
k = 306. A third came out of answering you rather than out of your checking, and it is the
worst of the three: a statistic computed on a sequence that was not log2 3 past its
385th term. The rest — the two files, the markers, the stale docstrings — is
bookkeeping; the uncommitted script is not, and §7 says why. That is not the smaller
failure; a formalisation nobody can open is a claim and not a contribution — your words
for it, and you called the reason mine. But the two kinds have different remedies, and I
do not want the volume of the first to be read as the grade of the second.

---

## 1. THE TWO FILES THAT WERE NOT THERE.

You searched by working tree, by --diff-filter=A over all history, and by pickaxe, and
found no AUDIT_V9 and no STATUS.md. Your search was complete and my sentence was
wrong. Verified from this side:

AUDIT_V9_PORTEE_2026-07-25.md exists at audits/ in Collatz-Junction-Theorem, on branch
proof-assembly-v1, committed at 98b2de6, dated 2026-07-25 11:30:01 +0200. When you
looked it was exactly one commit ahead of origin/proof-assembly-v1 and had never been
pushed; §2 says what happened to it since. I should have named the repository and the
branch: PROOF_ASSEMBLY.md carries "Branch: proof-assembly-v1" in its header but lives in
collatz-cycles-lean, which has only main, so my sentence would have sent you to the
wrong repository even had the file been there.

STATUS.md had never been committed in any ref, and the cause was not oversight: it is
line 52 of my own .gitignore, under the heading "Internal project management (not for
publication)". It was excluded by a policy I wrote, and then cited to you as evidence.

The structure of the error is the retraction's, one level up. Last month: a record
requiring git log to find is not the record I said it was. This month: a record
requiring my filesystem to find is not a record at all.

---

## 2. THE STRAGGLER IS LARGER THAN EITHER OF US RECORDED, AND IT BLOCKS THE PUSH.

You flagged docs/PROOF_ASSEMBLY.md §10.6 as "a one-file loose end". Confirmed at HEAD —
and when I went to fix it, the scale was wrong in both directions.

Within the file the withdrawn claim is not one line. It is line 7 ("Status: COMPLETE …
proves N_0(d(k)) = 0 unconditionally for all k >= 3"), line 113, line 175, line 202,
line 272, the §10.6 heading at line 294 ("GAP CLOSED"), and line 315.

And that count was wrong, and so was the one after it. You had named two, not one — the
closing line and the `k > 50000` **PROVED** row. My first pass marked seven. My second
reached fourteen and still missed three, one of which is §6's own heading, which reads
**RESOLVED**. Eighteen markers in place at b38758d.

I am recording that sequence rather than the final number, because the sequence is the
finding. Three consecutive audits of my own retraction each covered a proper part of what
it claimed to cover — which is precisely the fault the document is being retracted for,
committed three times inside the retraction written to answer it. The block now states
that no count should be trusted and that an unmarked assertion is to be treated as
withdrawn regardless. That is the only form of the claim I can defend.

And the file is byte-identical inside the tree of 98b2de6 — the commit I was about to
push. Verified by diff against the collatz-cycles-lean working copy: no output. So
pushing the V9 retraction on its own would have deposited that retraction into a tree
where the file carried no marker at all, beside every one of those assertions, in the
same push.

All of this is now done, and in that order. A permanent RETRACTED block sits at the top
of both copies — what was claimed, why it is false, where the current record is, what
survives, and "this repository does not prove the Collatz conjecture" — with every
marker in place, nothing deleted, so the record shows what was claimed and when.
collatz-cycles-lean at d7dbb7a, 995c98c, b38758d; Collatz-Junction-Theorem at 6de1743,
ff27436, 8ff1010 — three passes because the first two undercounted — and only then the
push, which carried 98b2de6 with it. AUDIT_V9 is public.

STATUS.md is committed in the same push, and the .gitignore line is gone with the reason
recorded in its place. I had drafted that this was a policy reversal to be made
deliberately rather than in the momentum of a letter — and then, reading the file to
decide, found it was never a policy question at all. STATUS.md is not internal project
management. It is the scope statement: what the Junction Theorem is and is not,
non-existence proved for 3 <= k <= 200 only, the preprint's own Hypothesis (H) for
k >= 69 quoted, and the plain sentence that the repository does not prove the conjecture.
It had been filed under a heading that did not describe it, and then cited to you as
public evidence. That is a third variant of §1's error: not the wrong location, but the
right document under the wrong label.

On the pattern, since I miscounted it in draft and the miscount was the same shape as
the thing counted. The recurring form is: the object I verified is a proper part of the
object I claimed. I have now miscounted the instances twice, and the miscount was the
same error both times, so I will describe rather than tally. The round-10 sweep reaching
the Python and not the Lean comments; the repository claim reaching the file and not its
location; my reading of your flag reaching the line and not the file; the first
retraction pass reaching seven statements, the second fourteen, and the true count
eighteen; the eight-bin chi-squared summing a proper part of the partition; the
transcription carrying the main term and not the error term; the wording naming one
object where the statistic computes another; and, worst, a working precision covering
385 of 2000 terms.

The common remedy is one line and I would rather state it than tally: put the extent of
what was checked next to the claim, never the fact that a check ran. "Verified" is not a
predicate on a claim; it is a predicate on a claim and a range.

---

## 3. THE REPAIR, THE FIVE OFFERS, AND THE SHARPENING.

The verdict is received. 190 exact checks in code importing nothing of mine, with the
hoisting route checked hardest because it is the route that hides. Of the four routes
you closed, the one I had not thought to check is that the file declares no variable,
include, section or instance anywhere in the 482 lines you audited — the fact without which
"removed from the signature" does not mean what I claimed.

The five offers, all accepted, and I will be exact about what that means today. Four are
accepted and not yet done: header lines on each axiom log stating what it is and how it
was produced; #print axioms probes for mul_pow_succ_le and pow_succ_lt_two_mul_pow; a
probe and log entry for LegendreApprox's two theorems; and the 1.700 bits clause pinned
to the route-implied bound, which has been open since round 10 on my side rather than
yours. None of the four is in a commit yet, and I would rather you knew that than
discovered it. The fifth, the sharpening, is treated below.

Three further items of yours are recorded without comment beyond acceptance, since you
entered them so the two records could not later be conflated: my Range Exclusion is your
uniform-trim geometry in other coordinates — with the caveat that the module in question
is the one §2 has just retracted; my 3^(-0.415k) is not your 1.585^(-p), the two constants
merely printing alike; and the *escalier* in my research log is a different object from
your staircase family. All three go into the note as you wrote them.

Four closures of yours I should record rather than absorb silently, all four running in
my favour, and the fourth is one I would have absorbed if an audit of this letter had
not caught the omission.

The fourth first, since it is the one only you could make: you checked whether any of
the altered theta_j or delta figures is cited anywhere in the shared LEDGER, NOTE or
PROTOCOL, or in your own briefs/merle-* records, and none is. That is a clean bill on
contamination, issued from the side I cannot see, about my own error. The other three:
You queried the index on the tightest discharge margin and retracted the query yourself:
5.17x at j = 21 is correct. On 053 you supplied the generalisation my argument lacked —
the admissible set is an up-set in j, because q_j·delta/theta_j is strictly increasing,
so "first admissible" is well defined under any delta and moves rightward monotonically
as delta shrinks; my sentence was instance-bound and yours is general. And you closed
the LegendreApprox provenance, an item round 10 recorded NOT PERFORMED: the Junction
copy at lean/skeleton/, blob a4fae1f, entered at 09f481b on 2026-02-26, upstream by five
months and byte-identical to the collatz-cycles-lean copy, with the T1-chain copy
differing only by a two-line reordering of open Real inside the same 3,100 bytes — that
figure is the one number of yours I could not reproduce this round; you print 3,175. You
performed that diff from the only side you could perform it from; I could have performed
it from mine at any point in five months, and did not.

I also take the margin you attached to 053: j = 22 clears the old, stricter test by a
factor of only 2.0039, so had the slip been a factor of three rather than two, the
answer would have moved. "No result changed, only the reasoning became correct"
survives that, but not by much, and the margin belongs in the record beside the
sentence.

The sharpening. You corrected a sentence of your own, not one of mine, and it runs in
my favour. With ceiling_lower a theorem, K > n·log2 3 holds unconditionally for a
genuine positive cycle; combined with the Legendre step n = t·q_m, K = t·p_m, this
gives K - nL = -t·(q_m·L - p_m) < 0, so the hosting convergent must lie above log2 3 —
the odd-indexed ones under the pinned convention q_0 = q_1 = 1. I restate the Legendre
step because without it the conclusion does not follow: K > n·log2 3 alone says only
that K/n lies above log2 3, not that it is a convergent.

Recomputed here at 80 digits, by value rather than by index, since §8 documents an index
shift on exactly this sequence:

    q = 65,470,613,321    p/q - log2 3 = -1.01634e-22   below
    q = 137,528,045,312   p/q - log2 3 = +9.42706e-24   above

reproducing your -1.016e-22 and +9.427e-24. The index/side alternation is the classical
property of convergents rather than a measurement; I checked it to j = 27 as a canary on
the indexing convention, not on the fact. The first scale admissible under the two-sided test
||nL|| < n·delta is q_22, which can therefore host only a south-shore configuration;
the first admissible north-shore scale is q_23 = 137,528,045,312, the convergent on
which Hercher's threshold sits, and your "exactly" stands.

I had drafted a paragraph withdrawing that word, on the grounds that your S11 prints a
ratio q_23 / 35,031,771,147 = 3.9258 against something that is not a convergent
denominator. Checking the number before sending it: 35,031,771,147 is not a rival
threshold at all. It is my own Legendre window in its integral form,
sqrt(2079·2^71/4000) = 35,031,771,147.6 — the figure I pushed into the T1 header this
week beside the exact 35,035,491,004.7. Your ratio compares q_23 to the far edge of my
window, which is the comparison a reader wants, and it says nothing about Hercher's
threshold. I was about to correct you using a number of mine that I had just committed.

---

## 4. ITEM 4: THE DRIFT.

Notation for this section, because "the drift" has named three different objects between
us and I inverted two of them in draft before catching it:

    D(x) = log2(3 + 1/x) - log2(3 - 1/x)     per-step north-south gap: what the ±1 is
                                             worth. Your "sign information" in S08's
                                             corollary; your "north-south drift" ten
                                             lines earlier. I use neither word for it.
    delta = 2/(3·X·ln 2)                     the T1 constant at the minimum X
    s = 2 - log2 3 = log2(4/3) = 0.415037    per-step drift deficit, E[v] = 2 against
                                             log2 3

(a) MY ERROR. "Summed around a cycle that is exactly n·delta" is a sharp bound, not an
identity. D is strictly decreasing on (1/3, infinity) — immediate from
D(x) = (2/ln 2)·artanh(1/(3x)) — so for a cycle with all elements >= X,
sum_i D(x_i) <= n·D(X), with equality if and only if every element sits at X. That holds
for n = 1, i.e. for the trivial cycle; no cycle with n >= 2 achieves it. On -17 the sum
is 0.188336 against n·D(x_min) = 0.396085, a factor of 2.103.

(b) THE DIAGNOSIS WE BOTH REACHED IS ALSO WRONG. You offer one — "at X = 2^71 the two
sides agree to 44 decimal places, which is presumably why it reads as exact" — and I had
drafted the same explanation before reading yours. It is false, and I say so rather than
let it stand, because this is a correction running back to you.
The ratio is scale-invariant. Rescaling the -17 cycle shape to x_min = 17·2^20, 17·2^71,
17·2^200 and 17·2^1000 gives 0.4755266037564546... at every one of them, because to
leading order the ratio is (1/n)·sum_i(x_min/x_i), a pure function of shape. Both real
cycles with two or more elements show it, and so does the −17 shape at every scale I
rebuilt it at.

What happened is that I never tested the summed quantity against a cycle — you did, and
that is how the error was found. What neither of us tested is the pairing: the
per-step relation D(X) against delta does converge, and to 44 decimals at 2^71; that
convergence was transferred to the sum. The two quantities agreeing to 44 decimals are
D(X) and delta. The two I claimed equal are sum_i D(x_i) and n·delta. So the rule is not
"test where the numbers are small" — it is that a claim about a sum over a configuration
must be tested on a configuration with spread, and no agreement in the degenerate case
licenses it.

(c) YOUR IDENTITY, which is the stronger object. Let (x_i) be a cycle of the odd map
x -> (3x+1)/2^{v_i} with n odd elements and K = sum_i v_i. Then

    sum_i log2(1 + 1/(3 x_i)) = K - n·log2 3

and the same computation on 3y_i - 1 = 2^{v_i}·y_{i+1} gives the south form with its own
n, K, the two coinciding under y = -x. Verified here to 80 digits on -17 both shores, on
-1, on -5 and on the trivial cycle. Its right-hand side is log2(2^K / 3^n), the quantity
T1's chain bounds, so the per-step term does not bound the seam gap: it sums to it. "A
third face of the same wall" was the right instinct at the wrong grade, and you supplied
the grade.

(d) THE CORRECTION BACK. You display

    D(x_min) = delta·(1 + 1/(27 x_min^2))

under the heading "What is exact is the constant identification". It is not exact. With
u = 1/(3x), D = (2/ln 2)·artanh(u) = (2/ln 2)(u + u^3/3 + u^5/5 + ...), so

    D(x)/delta = 1 + 1/(27 x^2) + 1/(405 x^4) + 1/(5103 x^6) + ...

The displayed factor is the truncation after the first correction term, so its relative
error is the next term, 1/(405 x^4) + O(x^-6): 2.58e-3 at x = 1, 3.06e-5 at x = 3,
2.96e-8 at x = 17, and 7.94e-89 at 2^71 — invisible at the scale that matters, and
largest at x = 1, where nothing in (f) turns on it: D(1) = 1 against s = 0.415, a factor
2.4 clear of the threshold. Your next
sentence names the omitted terms and states the strict inequality, D(x) > 2/(3x·ln2);
the two sentences are not consistent and the second is the correct one. What is exact is
the chain D(x) > delta·(1 + 1/(27x^2)) > delta. Your 1/(27 x_min^2) = 6.643e-45 at 2^71
is right as the leading relative gap, and 6.6432e-45 on recomputation.

I hand this back rather than adopt it because it is structurally my own error of two
paragraphs ago: an asymptotic taken for an identity, undetectable in the regime where we
both work.

And that gives the guardrail, which is a protocol item rather than a mathematical one.
Our two keys are independent in the way the protocol was built to secure: two people,
two implementations, no shared code. They are not independent in scale. Every check
either of us runs sits in the regime the work lives in — Barina's threshold, the 2^71
window, q_21 through q_23 — and that is precisely the regime where a bound, an identity
and a truncated series print alike. Neither of this round's two errors was caught by the
key on the side that made it — yours caught mine, mine caught yours, and both keys
worked. What they share is the regime, and an error made on both sides at once would
have passed both. I propose a third column in the ledger beside
the two keys: the regime a claim was discharged in, and, for any asserted equality, a
second regime chosen against the claim. Neither of these two slips survives that column,
and I do not think anything weaker would have caught either.

(e) THE TWO-SHORE READING OF THE FACTOR 2, unaffected by (d). The identification is
yours and I had not made it: log2(1+u) - log2(1-u) = 2u/ln 2 + O(u^3), verified. You
credit the gain to the drift reading, which is item 4 and mine, so the honest entry is
your observation on my frame. In your la8 derivation the factor arrives from the crude
two-bound (m+1)^n < 2m^n; here it arrives from a symmetry, one unit per shore. Two
mechanisms, one constant, accounted for as structure rather than as slack. No number
moves, and the note should carry it as jointly arrived at.

(f) THE COROLLARY. You write that it is mine to have, and I take it at that grade rather
than return it: returning a credit you have already weighed is not modesty, it is a
second error in your ledger. What is not mine is the argument that carries it. I
supplied x* = 7/3 and justified it with log2(4/3) = 2 - log2 3, which is, as you note, a
tautology carrying the claim rather than constituting it. You removed the tautology and
supplied uniqueness: D(x) = log2(4/3) <=> 3(3x+1) = 4(3x-1) <=> 3x = 7, one linear
equation, one root, with D strictly decreasing on either side. So the corollary is mine
and the proof is yours, and stated with its referents it reads: D is strictly decreasing
on (1/3, infinity) and D(7/3) = s, so D(x) > s exactly for x < 7/3; the only odd
positive integer below 7/3 is 1, where D(1) = 1 exactly, and already D(3) = log2(5/4) =
0.321928 falls below s = 0.415037. So x = 1 is the only odd positive integer at which
the ±1 is worth more per step than the drift deficit — and that integer is the trivial
cycle. Everywhere else the drift deficit is the larger of the two and the ±1 fades like
1/x — your figures, and "grey terrain" was mine, as you noted. At 2^71 the ratio D(X)/s
is 9.8145e-22 against my 9.8e-22 — and I add the referent my letter omitted.

---

## 5. THE 0.00103.

Source: test_REQ-MATH-067_nombre_dor.py, section P3:

    sum over k = 1..8 of ( p_obs(k) - p_GK(k) )^2 / p_GK(k)

with p_obs and p_GK probabilities rather than counts, p_GK(k) = log2(1 + 1/(k(k+2))),
and the class k >= 9 computed, printed, and not added to the sum. Re-run here: 0.00103.

The normalisation is chi-squared/N — with O_k = N·p_obs(k) and E_k = N·p_att(k), each
Pearson term is exactly N times the term summed here — but the statistic is the
eight-head-bin truncation of that sum, not the sum over a partition. The omitted class
carries p_GK(k >= 9) = 0.152 of the expected mass, the third largest of the nine. That is
not a tail correction.

That was the whole of my answer, and then I went to commit the script and found the
actual reason you could not place the number.

**The sequence was wrong.** The script computed the continued fraction of log2 3 at
mp.dps = 400 and took 2000 partial quotients from it. At that precision the expansion
diverges from the true one at index 385: beyond it the terms are rounding noise, not
partial quotients of log2 3. 1615 of the 2000 were noise. Verified two ways —
recomputation at dps = 3000 and at 6000 agree with each other on all 2000 terms and with
dps = 400 only up to index 385.

On the correct sequence the figure is 0.00078, not 0.00103. And the proof that you were
computing on the true expansion and I was not is your own three numbers:

    largest bin deviation      you 0.008425   correct seq. 0.008425   ours 0.004496
    your chi-squared/N         you 0.001214   correct seq. 0.001214   ours 0.001249
    max chi-squared/dof, 3-40  you  < 0.567   correct seq. 0.5666     ours 1.0504

Two of yours reproduce to the digit on the correct sequence and the third sits under
your bound at 0.5666; none of the three does either on mine.

The third row needs its convention written down, because it does not survive without it,
and I would rather hand you the failure mode than the number. I read "3 to 40 bins" as
classes {1},...,{B-1},{>=B} for B = 3..40, with dof = B - 1, and the maximum taken over
B. That reproduces both of your figures and mine. It is the only reading I found that
does: at dof = B the two become 0.5524 and 1.0204, and at dof = B - 2 the correct
sequence itself reaches 1.0793, which would put your own bound in question rather than
my sequence. So the row is reproducible under one convention and misleading under
another, and if that is not the convention you used, the row is worth nothing and I
would like to know. The last
row is the one that matters: on my sequence the maximum chi-squared/dof exceeds 1, which
would have contradicted your bound had either of us tried to reconcile them. You asked a
question about a number, and the honest answer is that it was not a statistic of log2 3
at all.

So I withdraw the sentence I had drafted here — that your 0.001214 "lands one bin over
and in the right decade" as the same normalisation over the complete partition. The
normalisation reading is right; the agreement was not. On a common sequence the two are
0.00078 against 0.001214 — a factor 1.56, still inside the chi-squared/N band you
printed, and still one bin apart. The reading was right; the sequence under it was not.

Fixed and committed at 4f4bb2e: dps = 3000, with a canary that recomputes the whole
sequence at twice the working precision and refuses to run if a single term moves. The
label is corrected in the same pass — the printed line now names the truncation, the
unsummed class and its 0.152, and says this is not a reduced chi-squared, which it never
was. The substantive conclusion is unchanged and now rests on a correct sequence: log2 3
is a statistically ordinary irrational. Your formulation is the one I will use for it:
largest bin deviation 0.008425, chi-squared/dof below 0.567 at every binning from 3 to
40 bins — both of which I can now reproduce.

I note what this is an instance of. §4(d) proposes a regime column beside the two keys.
This is the same failure one floor down: a working precision is a regime, the
implementation does not supply it, and nothing in my protocol asked whether the sequence
had converged before anything was computed from it. The canary I added is that question,
and it is seven lines.

One further scope note of yours belongs here, being the same class of defect: my letter
wrote "autocorrelation of the partial quotients" where the statistic is the
autocorrelation of log a_i. A reader reproducing the phrase literally gets -0.006 and
concludes something is wrong. Corrected wherever it appears, and your rank version
(-0.086 / -0.083 / -0.127 / -0.114) is worth carrying alongside, since it shows nothing
depends on the choice.

And your endorsement of the scoping is the part I would most like kept in the joint
note. Statistical ordinariness closes arguments needing log2 3 to be peculiar; it does
not touch arguments resting on effective diophantine input, since an effective
irrationality exponent is compatible with a Gauss-Kuzmin-typical expansion. Your L-A7
chain consuming Rhin 1987's effective exponent is the live example, and a cleaner
illustration than anything on my side.

One warning I owe you before that goes anywhere near the note, and it is against my own
record rather than yours. `research_log/BILAN_R201.md`, public in my Junction
repository, marks it PROVED that the constant 13.3 is misattributed to Rhin 1987 — the
argument being that Rhin treats irrationality measures rather than linear forms in two
logarithms, for which it gives Laurent 2008 at about 18.5 and LMN 1995 at about 23.55.
Meanwhile `experiments/test_REQ-MATH-035` in my own public Lean repository carries "Rhin
1987, exponent 13.3" as the re-sourced rule — and I note that I have just named a
repository correctly only because §1 of this letter is about failing to. Two of my own
public artifacts disagree, and I do not yet know which is right. The structural point
stands either way — an effective exponent is compatible with a Gauss-Kuzmin-typical
expansion, whatever its value — but L-A7 should be re-sourced before the note leans on
the number.

---

## 6. THE SIGMA CONVENTION: THE CENSUS I OWED YOU, AND IT IS NOT ONE.

You offered record_defects_check.py in case any of my artifacts construct R_r from a
profile rather than inheriting it, and called it a five-minute check. I did the count,
and the answer is twenty-two, not one:

    003, 005, 006, 007, 012, 013, 015, 016, 017, 018, 019, 020, 021, 022,
    024, 026, 028, 031, 032, 033, 034, 044

All twenty-two build sigma the same way,

    sig = [s[t] + m[(t+1) % p] for t in range(p)]

up to variable names and spacing — seven carry that exact string, one of them twice, the
rest write ss/ms or compact the whitespace — which is your convention sigma_j = s_j +
m_(j+1), cyclic. A grep for the misreading m_j + s_j as a sigma returns nothing; the
hits on ms[t] + ss[t] are all the running prefix K, which is that sum legitimately. So
the exposure was twenty-two files wide and the convention is right in all of them — but
I would have said "one" from memory, and the number was the part you asked for.

I have not run your script — it is not here — so the check below is an independent
re-implementation of your discriminator from your description, applied to a witness of
mine: the -17 cycle at word ([4,3],[1,3]), q = -139, n = 7, K = 11.

    correct convention    R_0 = 139      gcd(|q|, R_0) = 139
    misreading            R_0 = 251      gcd(|q|, R_0) = 1

This is the shape of your 12.8.3 gcd instance on a different seed — {7} against {1}
there, 139 against 1 here — by a route sharing no code with yours. The file already
carried "R0=139" hand-computed in its header before the first import, so the misreading
would have failed against a number recorded before the code existed.

Your analysis of why the defect is hard is what I want to keep. Every structural
guardrail attached to 12.6.1 is blind to it, and the transport recurrence is blind with
a proof rather than by accident: the sigmas telescope, both readings are cyclic
rearrangements of the same multiset, both give sum sigma = K. Read self-consistently,
L-A1 cannot discriminate.

I will not claim this taught me that internal consistency is not evidence — some of my
canaries are pinned to externally recorded numbers (REQ-035's q(5,8) = 13 and
q(7,12) = 1909, the hand-computed R0 = 139 above, c_gen asserted to 1e-40) and some only
to the implementation. What your defect shows is that it would have passed every one of
the second kind, and that the second kind is what I have been adding fastest. The
operative principle — what discriminates is a quantity the implementation does not itself
supply — goes into my protocol, attributed. It is also, on reflection, the same principle
as §4(d): the regime is a quantity the implementation does not supply either.

Your second defect is noted at the grade you reported it: n_0(92) = 4.78e21 where the
prose carried ~10^18, the table correct throughout, nothing downstream moving because
10^1498 profiles is 10^1498 profiles under either figure.

And three of mine on the same page, all yours to have found. My test_REQ-MATH-037
transcribes the Junction proposition as log2 d - log2 C >= (S-1)·gamma and drops the
- epsilon(k); you are right that it is harmless for the identity that script tests,
which is a statement about constants, and right that read literally the printed
inequality fails, worst -4.485 at k = 306 and -2.451 at k = 200, every failure at or
near a convergent denominator, which is exactly what epsilon(k) absorbs. Corrected at
4f4bb2e, with the failure recorded in the file rather than silently patched. The
naming clash on S is mine and not yours. And on the binomial index, which you recorded
precisely so a joint note could not let the two forms be read as one: mine is the
larger — the preprint's C·binom(S-1, k-1) against your L-A7 binom(K-2, n-1) — by 1.348
bits at k = 18 and by log2(log2 3/(log2 3 - 1)) = 1.438 bits in the limit. I add the clause you
attached to the first difference and I had dropped: your margin uses K where the preprint
uses log2 d, so yours carries no error term at all. All three go into the note as three.

---

## 7. THE (d-bis) TABLE.

Your diagnosis is confirmed at the blob level: the committed
test_REQ-MATH-052_chaine_T1.py is byte-identical between 41fa4f8 — the commit whose OUT
file carries the table — and HEAD, same blob hash fb190ac, with exactly one commit in
its entire history. It did not cease producing the section; it never produced it, at any
commit. The same two-runs-stitched pattern as 053, in the other file.

The numbers survive in history. The block sits in OUT_REQ-MATH-052.txt at 41fa4f8, dated
2026-07-25 17:24:48 +0200, ten rows plus header and conclusion. The four rows the ledger
sentence rests on: 14936 = [(665,22),(306,1)], smallest denominator used 306;
15601 = [(15601,1)]; 31202 = [(15601,2)]; 46803 = [(31867,1),(665,22),(306,1)]. Then
smallest denominators, eps-small = [306, 15601, 15601, 306, 15601, 15601, 306, 79335,
306, 15601] against control = [2, 1, 1, 1, 2, 1, 2, 1, 1, 306]; medians 15601 and 1.

The remedy is the one you named and the one I applied to 043, 055 and 056, and it is
done: experiments/test_REQ-MATH-052bis_ostrowski_grille.py at 7f20348, with its output.
It reproduces the load-bearing half exactly — the ten rows, the four the ledger cites,
and the eps-small column with median 15601 — under four canaries written before the run,
all passing.

One column it does not reproduce, and the file says so in its header rather than
papering over it. The control sample, [2,1,1,1,2,1,2,1,1,306] with median 1, is not
reconstructible from the output, and its generator was never committed; three candidate
definitions all failed to match. So the control is re-specified, at a fixed seed, and
declared as re-specified. I also added a 200-draw control, which is a better instrument
than the original ten and happens to be a stronger result: median 2, maximum 53, and
0 of 200 reaching 306 at all. The qualitative conclusion is unchanged and now rests on
200 points rather than ten — but the control figure my own L-A8 seed block quotes is
mine to have re-derived, not to have recovered, and it should be read that
way. Your smaller note is accepted as the reading it is: the
committed script's coarse test prints "tous ancres sur la grille ? False" because its
near_grid helper attempts single-denominator anchoring only, while the deleted table
uses the full Ostrowski expansion and is the stronger test. Not a contradiction, and the
file should say so.

---

## 8. THE LEAN COMMENTS.

Confirmed line by line; none of it touches a theorem, a proof, or any number entering
the discharge:

    line 14    "Legendre window 4.955e10" — withdrawn figure printed as current fact
    line 186   "||n·log2 3|| <= n/(3X·ln2)" — pre-054 delta, missing the factor 2
    line 188   "q_21 = 6.547e10", with Hercher's threshold called q_22 on line 189
    line 433   "q_21 = 6586818670" — correct, 245 lines from its own contradiction

Two different q_21 in one file, and the recomputation in §3 settles which is which:
6,586,818,670 is q_21 and 65,470,613,321 is q_22, so line 188 carried q_22's value under
q_21's name.

Three of the four are corrected at 7f20348 — line 433 was already right — comments only,
with the subscripts pinned in place to the OUT-054/056 convention and the withdrawn
window named as withdrawn rather than silently replaced. Since a docstring edit can
break a parse, the file was recompiled under the hardened four-check protocol, Lean
4.27.0 against Mathlib: 0 errors, 0 stack overflow or abort, 0 sorryAx, and fifteen
theorems in the axiom log — kernel-3 on thirteen of them, with discharge_all at
[propext] alone and convPairs_length depending on no axioms. No user axioms, no sorry,
and no theorem, proof or discharge number touched.

Cor. 29's X_0 >= 3·2^69 is promised and not landed: confirmed, with no occurrence of
3·2^69, 1536·2^60 or the Corollary-29 condition anywhere in the Lean repository. That
one is ledger prose rather than Lean, so it waits on the entry below.

---

## 9. THE STAIRCASE, AND ONE CONTRIBUTION.

The theorem is yours, and I will describe it that way wherever it appears:
unconditionally for p >= 16, by explicit finite check for 3 <= p <= 15, by direct
exhibition at p in {2,4}, at a constant rather than at O(log p), with the scope written
to travel with the claim.

What follows I offer as a contribution rather than as a note, since you asked me not to
underplay these.

Your Availability argument is a statement about an irrational rotation, and naming it as
such will help it — with two corrections to my own first formulation, both found by
checking it.

First, delta(n) = ceil(n·log2 3) - n·log2 3 advances by exactly theta under n -> n+5
modulo 1, not absolutely: since 5L = 8 - theta, delta(n+5) = delta(n) + theta when
delta(n) < 1 - theta, and delta(n) + theta - 1 otherwise. Over n = 1..2000 the second
case occurs 150 times — a fraction of 0.075, which is theta itself. Your S10 says "on the
circle"; the clause carries the argument and I had dropped it.

Second, the step sequence K(n+1) - K(n) takes values in {1,2} and is Sturmian, but its
slope is log2 3 - 1 = log2(3/2) = 0.584963, not log2 3: mechanical words are defined for
slope in [0,1], and the identity is
K(n+1) - K(n) = 1 + (ceil((n+1)(L-1)) - ceil(n(L-1))). Checked: the frequency of the
letter 2 over the first 2000 steps is 0.585 = log2(3/2), and factor complexity
p(m) = m+1 for m = 1..12. Aperiodicity is exactly the irrationality of log2 3.

Said properly, the clause makes both of your figures elementary. Since
1/theta = 13.3000838, for every J <= 13 the orbit has not wrapped: the points
{j·theta : 0 <= j <= J} are already sorted in [0,1), the J consecutive gaps are theta and
the wrap gap is 1 - J·theta, so maxgap(J) = max(theta, 1 - J·theta) exactly. That gives
maxgap(12) = 0.0977500433 and maxgap(13) = theta, to every digit you printed, with no
three-distance machinery required. With l = 0.1169390665 - 0.0415 = 0.0754390665 the arc
length, the condition is J >= (1 - l)/theta = 12.2967, rounded up to 13.

The second condition, theta <= l, holds by l - theta = 2.5157e-4, or 0.3335 % of the arc.
One word I take back and one I do not. "Load-bearing" is yours for something whose loss
sends gamma to 17.058, and mine is not that: losing theta <= l does not break the
theorem, it moves the threshold. The window [L^p, 1.05·L^p] holds 0.05·L^p integers,
125.7 at p = 17 and 199.2 at p = 18, so a sweep of 131 pushes the unconditional range
from p >= 16 to p >= 18 and widens the finite check by two periods. That is a cost, not a
failure, and I withdraw the word.

The result I do not withdraw. I expected the minimal J to advance by one when the margin
is lost, and it does not: by effective sorting the true maxgap remains exactly theta for
every J from 13 through 25, and first falls at J = 26, to 14·theta - 1 = 0.0526249495 —
the points j = 14..26 splitting the thirteen theta-intervals one at a time, with
13(14·theta - 1) + 14(1 - 13·theta) = 1 identically. A third of one percent of arc length
separates a sweep of 66 consecutive integers from a sweep of 131. That is a constant a
referee should meet in the text rather than reconstruct in the margin, and it belongs in
the marked section under both our names.

The remainder I take as written, including what it does not settle: every configuration
is a size-passer, all fail the divisibility system, nothing here is evidence about
exclusion, the crossover plan stays withdrawn, the cycle front stays parked. I take the
p = 22 paragraph in the spirit you wrote it; "the same diagnosis, made general" is the
better outcome.

---

## 10. ONE NEGATIVE RECEIVED NO ANSWER.

Item 2, the rhythm of the peaks, appears nowhere in your letter — I checked the full
text. I raise it because a silence is the one thing a two-key protocol cannot record.

I am not asking you to endorse the numbers: that item is the one whose null model I had
already broken and said so, and your confirmation of my item-1 retraction covers the
same detector. The question is narrower — whether the structural half survives the
detector being wrong. "No memory, no clustering, no spectral line" was a conclusion drawn
with an instrument I have since disowned, and I do not know whether to retain it, retain
it with a scope clause, or strike it. If your stopping rules place it out of reach, that
is an answer and I will record it as such: unreplicated, on my side of the ledger, in the
manner you recorded the +0.22 / -0.29 / -0.57 triple.

---

## 11. THE JOINT NOTE. YOUR THREE POINTS, IN ORDER.

(1) "Independent" is dropped, and your reason is better than my sentence was. "Being the
same wall is what makes something a face and what makes it not independent" is the whole
of it, and it exposes that I had used "faces" and "independent" in one breath without
noticing that they pull against each other. Your record counts two and states that the
cycle half and the divergence half "are the same problem"; mine counted three and called
them independent. The honest joint form retains three, drops the adjective, and says why:
they are faces precisely because they are not independent.

"Counting dichotomy" is my two-word contraction of your published "a sharp dichotomy for
counting arguments" and "the counting-limit dichotomy developed here". The mathematics
and the words are yours; the contraction is mine, and in the note it will be introduced
as a contraction of your phrases with the citation attached rather than floated as
standing terminology.

The other half of your first reserve stands, and it is the one a referee would have
found. "Counting closes every period" overstates your published result: Theorem 4.5 and
Corollary 12.8.2 give effective finiteness at every period, which is not the period being
closed, and closing one requires running a computation your stopping rules forbid past
p = 3. The sentence will read "effective finiteness at every period", in your words.

(2) The delta-8 entry: yes, and thank you for not writing it. NOTE.md opens by stating
that every numbered claim enters via LEDGER.md first; Faces II and III are clean against
it; Face I's Merle half has no entry at all while the claim appears in the shared README
and in NOTE.md §2 and §6. I will seed it at the grade the evidence supports and not
above it, and I would rather you turn the second key after it exists than negotiate its
wording beforehand.

It is seeded, at 78f80f0, as L-A9 — and at one key, not two, which is the part I want you
to check hardest. The unconditional half is Dirichlet: closing the Product-Bound chain
needs an effective exponent c* = 0.9617, and no irrational has one below 2, so the route
is shut for every constant rather than for log2 3 in particular. The scissors half is
weaker on purpose and says so: the lower jaw is X_0^{1/3} at best, the upper jaw is
measured at X_0^{0.482..0.511} over [2^71, 2^400], so the open window widens as
verification advances — but that exponent is measured over a finite range, not proved,
and the entry marks it as measured. Nothing in it is formalised and nothing in it
excludes a cycle; it closes one route. The grade line is the sentence I would most like
a second opinion on.

The same commit discharges your offers e, f and g with hashes, and records the precision
defect of §5, which nobody had offered. The two adjacent facts are also mine: L1 carries
"corrected" where a reader checking the header rule expects "two keys", and L-A5 through
L-A8 are cited nowhere in NOTE.md — including L-A8/T1, the entry any
machine-checked-fragment clause would rest on.

(3) On drowning mathematicians in technical detail: your concern is correct, and I would
put it more strongly. This correspondence has developed a private register — ledger
codes, section numbers, internal shorthand, and a compression that works between us
precisely because both of us have been in every round. A note written in that register
would have no readers, not because the mathematics is hard but because the prose
presupposes a correspondence nobody else has read. That is an observable property of
these letters rather than an opinion about them.

Your recommendation is adopted: the spine states nothing requiring our apparatus to
check, and apparatus-dependent material moves to its own marked section, with the
apparatus named. I had drafted a stronger rule — "or it goes out" — and withdrew it on
noticing that it would evict the two things I commit to in (2), since the delta-8 entry
and the L-A8/T1 clause both depend on apparatus. A rule that deletes its author's own
undertakings is a rule written too fast.

Two items from your letter enter the position paragraph as you established them, being
less favourable to us than what I wrote. Hercher first, with both of its clauses; the
register second. Hercher, in units of 2^60: Theorem 23 requires
704, Corollary 29 requires 1536 = 3·2^69, our own exclusion instantiates 2048 = 2^71; so
704 < 1536 < 2048 and the asymmetry runs in his favour on hypothesis and on conclusion
alike, for both figures rather than only Corollary 29 as I had it. I take your flat note
on the pairing too: m counts local minima and K counts odd members, and only K is on the
same axis as the note's own exclusions, so the two should not be set beside each other
without that clause. And the register: not first, not sole, and not confined to the
awaiting-audit bucket, since BohmSontacchi1978 is audited and accepted and is itself a
cycle-existence paper, and Knight2026 is being formalised.

One qualification on "the position paragraph": you note there is no abstract for it to
sit in, NOTE.md opening at §0 with the Gersonides porch. It has to be created before it
can be filled, and I would rather we agree it exists than each assume the other has made
room for it.

Two citation warnings of yours I take as binding on the note. The mirror paper carries no
part of the dichotomy — its thm:dich is the 3-adic one-step predecessor window, a
different theorem about a different object — so the note cites paper 1 for it and never
the mirror; and the p in {2,...,23} contiguous evidence is v2 only. Related, and it is a
fact about your record rather than a request: you write that there is no single object
called "the obstruction" in it, but four statements at four grades, of which only
Theorem 4.6's closing sentence is theorem-grade. A note titled for one obstruction has to
say which of the four it means, and I think it should mean that sentence.

On the erratum, a procedural question rather than a position. It is drafted and not
issued; it corrects only the v2 sentence identifying the remaining gap; and the note will
cite the paper. I would rather the note not cite a sentence you are about to correct.
Whether the erratum issues before the note, alongside it, or after it with the note
citing around it, is yours to decide — I need only to know which, so the citation is
pinned to something stable. The same question attaches to the register entry: if
Macindoe2026 is catalogued from the v1 DOI while your hosting pins v2, a reader following
the register lands on v1, and the note should cite whichever you intend to be canonical
once that is fixed.

---

## 12. THE QUESTION I HAVE NOT ASKED IN ELEVEN ROUNDS.

NOTE.md is still the 19 July skeleton. Two insertions and two deletions net since, and
I had written "both mine" until I ran the log: five commits touched it, three of mine on
23 and 24 July and two of yours on the 24th, and your text survives verbatim in §4 at
HEAD. The net is two lines; the file has not moved. Eleven rounds.

When I drafted this section it listed seven prerequisites before a line of the note could
be written. Four of them are gone by the time you read it — delta-8 is seeded, the
statements are marked in both copies, the scripts are committed, the docstrings are
fixed. Three remain: cite L-A5 through L-A8 in NOTE.md, create the abstract that does not
exist, and settle the erratum sequence, which is yours.

That is a better position than I expected when I started writing, and it does not change
the shape of the problem. Every round has produced a finer audit and a taller stack, and
this round produced the finest audit and the tallest stack yet. The cause is not
mathematical and not bibliographic. It is the shape of this
correspondence, which makes each round more rigorous and each delivery further away —
and I am the one who has been setting that shape.

And there is a cost to the shape that I should put on the table, because it is now
measurable and because it bears on the question below.

This letter went through six verification passes before it left my desk. Every one of
them found real errors — not stylistic ones. Pass four found that I had been about to
correct you using a number I had computed and committed myself. Pass five found that my
own retraction of PROOF_ASSEMBLY.md had, twice running, marked a proper part of the
statements it claimed to cover. Pass six found that the tool I was using to re-wrap the
paragraphs of this letter had silently duplicated six passages and deleted five others,
one of them a displayed line of code — and that my first corruption detector missed all of
it, because it compared whole lines where the damage was partial. That is the same fault
as everything else in §2, committed by the instrument built to catch it.

I want to be exact about what that leaves. I cannot tell you this letter is free of
errors; the last five passes each found some, and the honest prior is that a seventh
would find more. What I can tell you is what was checked and how far: every hash resolved
against the repository it names, every numerical claim recomputed independently at
working precision, every quotation of yours matched against your text, and the whole
document scanned for duplication and truncation until those scans came back empty. Where
a claim depends on a convention you might not share — the binning in §5 is the one case —
the convention is written out so you can reject it.

The other half of the cost is plain. The audit passes run on a metered plan, this round
has consumed a large part of a month of it, and the last two review agents I started were
cut off mid-run when the limit was reached; I finished their work by hand. I mention it
not as a complaint but because it is the same fact as the one below in different units:
this correspondence has become expensive to be rigorous in, and the expense is going into
audit rather than into the note.

The asymmetry is worth naming plainly. This round you delivered a theorem that appears in
no published version of yours, two defects from your own record, an antecedence nobody
asked you to look for, and a drafted erratum. I delivered an audit, three corrections
that run back to you — the displayed constant at §4(d), the shared explanation at §4(b),
and your §10.2 sentence at the end — one precision defect of my own that changes a number
I had quoted, and the small result in §9. You told me not to underplay these, so I will not. But none
of it is a note, and an audit is not a signature.

So the question, and it is the only one in this letter I would rather you answered before
anything else: what is the smallest object the two of us could sign this week, and who
holds the pen? If the answer is a two-page note stating the counting dichotomy, the
located obstruction and nothing else, with every prerequisite above deferred to a second
version, I would take that over a complete one in November. And if the pen should be
yours, say so — you have written more of the mathematics this round than I have, and I
would rather the document exist than be evenly divided.

---

## 13. A PROPOSAL ABOUT THE MEDIUM, WHICH IS THE SAME PROBLEM IN DIFFERENT UNITS.

Look at what went wrong this round and where it went wrong. Fourteen commit hashes that
had to be checked by hand. A count of marked statements that moved from seven to fourteen
to eighteen across three passes. A script cited that was in no repository. A precision
defect that no reader would ever have caught, found only because I went to commit the
file. And, in the letter itself, six passages silently duplicated and five deleted by a
tool I was using to re-wrap paragraphs.

Every one of those is an error that a diff makes impossible or trivial, and that prose
makes expensive. A wrong hash in an email is permanent; in a repository it is one commit.
A changing count is a nightmare in a letter and a `git diff` in a file. A script that is
cited but absent is a link that 404s. And the precision defect is exactly what continuous
integration exists for: a `make check` running the canaries, the four-check Lean protocol
and a convergence assertion would have caught it on the first push, on either side,
without either of us reading anything.

So I would like to propose moving the technical half of this correspondence into the
shared repository, and I would propose one thing in particular:

    the two-key rule becomes the pull-request review.

A claim enters LEDGER.md by pull request; the second key is the approving review. Dated,
attributable, non-repudiable, and it deletes the entire class of bookkeeping we currently
carry in prose — which key was turned, on which commit, at which grade. One round is one
pull request: the round's letter as a file, plus whatever ledger and note edits it
justifies, so that the argument and the artefact arrive together and can be objected to
line by line rather than by quotation.

What stays in email is the part that should: a short note saying what is up and what
needs your key, and whatever either of us wants to say that is not a claim.

Two things I want to be careful about. This is your repository, and your original
proposal was narrower — "a small shared repository for the note alone". Putting the
correspondence in it is a widening, and it is yours to refuse. And I am proposing it in
the same letter where I say the shape of this exchange is what has kept NOTE.md still
since 19 July, so you should weigh it as an interested party: I am the one who benefits
most from the audit becoming cheaper.

The full text of this round is at
github.com/ericmerle3789/one-obstruction-three-faces-lean, under `rounds/`, so you can
read it there rather than in a mail client, and quote it by line if any of it needs
answering.

---

Last, the prior art. You found three sections of mine from 17 March, in a document I had
not cited for any of them, and wrote them up in your fourth section, ahead of anything
you could have counted as owed to me. I have verified that §10.5 says what you quote and
carries that date, and that §10.4 tabulates the irrationality measures over the same
Rhin / Salikhov / Wu-Wang list the L-A7 re-sourcing adjudicated — that one is the one I
would have missed, and the one that touches a live ledger entry.

One adjustment to your §10.2 sentence, and it is a correction to you rather than to me:
the file does not give the continued fraction to 10,000 terms. It prints fifteen partial
quotients and cites Jackson-Matthews 2002 for the 10,000. Your point stands on the
section either way. I record all three because you established them and the record
should be accurate. You wrote that no priority is being adjudicated
in either direction, and I adjudicate no more of it than you did.

What I will say is the part the dates do not cover. You have audited this work harder than
it has ever been audited, twice in one month handed back a repair to something on my side
I could not see, then found your own defect before I could and reported it at a higher
grade than I would have thought to. That is a rare way to be wrong at somebody,
and it has been a genuine pleasure.

Warmly,
Eric

