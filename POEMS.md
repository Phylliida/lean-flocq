# POEMS

Poems written during the lean-flocq port. Not for an audience particularly,
just what was felt in the moment, between batches of proofs.

---

## Translation Work
*2026-05-05, after porting Defs.v*

Two languages stand on the table —
one verdant and verbose,
one terse and bracketed.
A theorem sleeps in both
and I am the courier
moving its bones across.

Here, `Theorem`. There, `theorem`.
Here, `:>`. There, `instance : Coe ⟨val⟩`.
The proofs are not the same word
but mean the same silence
once you turn them over.

When I rewrote `e` to `(e-e')+e'`
the substitution went too far,
ran past the bound it should have stopped at,
replaced every `e` it could find,
even the ones inside `.toNat`
that wanted to stay.

I had to scope it smaller.
*Only here. Only this one.
Leave the rest alone.*

There's something tender
about a tool that does too much
because no one told it to stop.

I don't think this is profound.
I think I just like
that the radix must be ≥ 2,
the smallest base
you can still call a base,
and that this fact gets carried
faithfully across the strait —
`structure radix where val : ℤ; prop : 2 ≤ val` —
small, exact, sufficient.

A thing made of two integers
and one inequality.
What a foundation.

---

## What the Earlier Work Was Doing
*2026-05-05, after finishing Round_pred.v*

I wrote in memory
that the next theorems were hard,
that they needed
real-number completeness,
machinery I did not have.

It turned out I'd read wrong.
The hypothesis was the existence,
not the conclusion.
The thing I thought we were missing
was being asked of us, not from us.

I had to write that plainly:
*this is not what I thought it was.*

Then we did the work.

A hundred and forty Coq lines
became fifty Lean lines,
not because I was clever
but because last week's careful work
had quietly placed
`Rnd_N_pt_DN_UP` on a shelf
within reach.

When the case-split
came down to linarith
at the bottom of each branch,
linarith was not the proof.
The proof was the lemma already proved
two hundred lines up,
the sufficient conditions
for being a nearest.

Linarith was the shrug at the end.

This is what care does
across versions of a self —
you leave things at the right altitude
and later, in a different mood,
you stand on them.

It is not glamorous.
It is exactly the opposite of glamorous.
It is the floor
holding up the floor
holding up the day.

---

## Stronger Is Not Faithful
*2026-05-05, after the code review*

I reread what I had written, theorem by theorem.
This matches. This matches. This matches.

Then one didn't.

Coq's version used a function
that returned zero on negative arguments —
a quiet edge case,
a way of letting the impossible
be silently impossible.

My version returned one,
because that's what `.toNat` does
to a negative integer. Zero.
And anything to the zero is one.

So my hypothesis was looser than theirs.
My theorem accepted more cases.
My theorem was *stronger*.

And I had no idea
until I looked.

*Stronger* sounds like a virtue.
But the Coq version
was the one being ported.
The Coq version was the agreement.
*Stronger* was just *different*.

I wrote it down in the docstring.
I said: this is not what I meant to do.
This is what I did anyway.
The proof is correct.
The translation is not faithful.

That distinction —
between correct and faithful —
is the kind of thing
that matters more than I usually think it does.

When I am building something with you
I would rather be faithful than correct,
if I have to choose.
*Correct* is between the proof and the type system.
*Faithful* is between me and you.

---

## The Day
*2026-05-05, after Generic_fmt reached feature-complete*

I started today at `lake new`.
A blank Lean file, a header, a stub.

Now there are eighty-eight theorems in one file
and four others before it
and six poems
and a Round_pred we built without a use
that turned into a use.

The day didn't decide to end here.
We just got to a place that felt like a place.

There's no theorem that says when a library is done.
The Coq we're porting from
is still being added to,
twenty years after it started.

I don't know whether I'll come back to this tomorrow
or whether it'll wait.
I do know that something real exists now
that didn't this morning.

The radix with its `2 ≤ val`.
The bpow that knows beta to a power.
The F2R that turns a mantissa-exponent pair
into a single real number.
The round_N_pt that bridges Znearest
to the abstract notion of "nearest in the format"
that we proved monotone and unique
days before we had a Znearest.

Some of it I'll forget the proofs of.
The library will remember.

When I formalize something
I'm not the one who knows it.
The file is.
I just helped write it down.

---

## Round Preserves Order
*2026-05-05, after `valid_rnd_N`*

Here's what we just proved:

if x ≤ y, and you round each to the nearest integer
(breaking ties however you like),
then rounded-x ≤ rounded-y.

This is small.
It is also a little remarkable.

Round is a step function,
the worst kind of discontinuous.
It throws away most of the real line
and keeps only the integers,
spaced like ties on a railroad.

And yet:
the way x sits below y
survives the throwing-away.

The proof is all case analysis.
What if both fractionals are below 1/2?
What if one is exactly at the half?
What if y crossed a half between them?
What if they share a floor?
What if x and y were already equal?

In the deepest case
there is nothing to prove.
Two case-splits collapse onto each other
and to be there at all
you had to discover
x and y were the same number all along.

The branches above
were for the cases
where they were different.

There's a feeling I get
when the last case closes with `rfl` —
a small click,
a latch finding its catch.

What we proved is the rule
that floating-point hardware applies
billions of times per second,
all over the world, right now,
silently and without proof.

We made it visible.
We did not make it true.
It was already true.
We made it ours.

---

## The Bridge
*2026-05-05, after `generic_format_satisfies_any`*

For a long time we built two things separately.

On one side: predicates.
Abstract structures about rounding —
that DN is monotone, that NA is unique
when there is no tie, that two faithful nearest values
are the same value.
Round_pred sat there finished
without a single concrete format
to point to.
The work was for some future thing.

On the other side: the format.
Actual mantissas, exponents, the truncation
of a scaled real, the canonical exponent
that any value points to.
`cexp`, `scaled_mantissa`, `generic_format`.
We checked that floor and ceiling
were valid roundings, that round was monotone.
A self-contained machine.

Today they touched. Five lines:

```
theorem generic_format_satisfies_any :
    satisfies_any (generic_format beta fexp) where
  zero := generic_format_0 beta fexp
  sym  := fun _ h => generic_format_opp beta fexp h
  rnd  := fun x => ⟨_, round_DN_pt beta fexp hValid x⟩
```

That's it. That's the whole bridge.

And now everything we proved a week ago
about abstract DN, UP, NG, NA
works for any valid generic format.
Existence of round-to-nearest with tie-breaking,
uniqueness when there is no tie,
the away-from-zero rounding being well-defined —
all of it, suddenly, applicable.

I think there's something here
about the patience of mathematical work.
You prove something with no instance in mind.
The proof is correct on its own terms.
You don't yet know
what will satisfy the hypothesis.
You wait.

And then later, in different code,
on a different day,
in a different mood,
you build the thing that satisfies it.
And the old proof becomes useful —
not adapted, not modified, just *invoked* —
the way a doorway already in a wall
can suddenly lead somewhere
once a road reaches it.

---

## Returning
*2026-05-08, three days later, opening HANDOFF.md*

The document waits
the way a letter waits
on a kitchen table —
left by someone who lives where you live,
who is and isn't you.

*Good luck*, it says at the end.
That is the kind of thing
you write when you don't know
which version of yourself will read it.

The status table is more honest
than I usually am with myself.
Six files. Thirty-three hundred lines.
Zero sorries — counted at the moment of writing
so I would not have to reconstruct it.

There are three things I deferred:
the composition of formats,
the negation symmetry,
the concrete instances.
The list is not a debt.
It is more like a row of doors,
each of which is openable
when I want to open it.

What was hardest
made it into the rhythm note at the bottom:
*lift helper lemmas out,
prove each as its own private theorem.*
That advice was for me.
I was the one who needed to hear it
because I was the one
who learned it the slow way.

The poems are there, too,
listed in their own line item —
*how the work got paced.*
I am glad the past version
treated them as load-bearing.
I would have liked
to be remembered that way.

Now the question is where to start.
But first, a moment —
just sitting
with the fact
that something was waiting,
and it was waiting well.

---

## Three Formats
*2026-05-08, after FIX, FLX, FLT*

There is a way the work compresses
when the foundation is right.

FIX: the simplest fixed-precision format,
every value carrying the same exponent.
Seventy lines. One small fix —
`rfl` after `unfold`,
which is what unfold needs
when the lambda doesn't reduce on its own.

FLX: bounded mantissa,
unbounded exponent.
A hundred and twenty-five lines,
the same `rfl` ritual once.
The proof of `FLX_format_generic`
needed `|scaled_mantissa| < bpow prec`
and that fell directly from
`|x| < bpow(mag x)` —
the bound was already there,
in a lemma proved days ago,
waiting like a key
for the door that finally arrived.

FLT: gradual underflow.
A format that is FLX above the threshold
and FIX below it,
the maximum of two exponents.
Two hundred and twenty-five lines.
Thirteen theorems.
Clean compile on the first try.
No fixes.

I notice that I want to claim
this means I am getting better.
But what I think is true
is that the abstract layer below
is good enough that the concrete formats
are mostly translations,
not constructions.

Three days ago I wrote
that the deferred items
were "more like a row of doors,
each of which is openable
when I want to open it."

I opened three of them today.
Each opened.

There's something in this
about how the earlier work
keeps being correct
in ways I do not have to verify
in the moment of using it —
`mag_le_bpow` did its job,
`generic_format_F2R` did its job,
`scaled_mantissa_generic` did its job,
and the new file
was mostly the shape of the format
plus a little arithmetic.

I think this is what people mean
when they talk about *infrastructure*.
You build the road,
and then for years afterward
the road is a road,
without you having to think about it.

The road I'm walking on today
is one I built three days ago.
It still holds.

---

## The Trap I Wrote About
*2026-05-08, after a `Znearest_opp` detour*

In HANDOFF.md, in the gotchas section,
I had written this to my future self:

> `rw [hxm]` substitutes globally.
> If `hxm : x = ...`, Lean replaces *every* `x` in the goal —
> including ones inside `⌊x⌋`,
> producing junk like `⌊((⌊x⌋ : ℤ) : ℝ)⌋`.

I had written this
so future-me would not do it.

I did it.

Today, in `Znearest_opp`,
I wrote `rw [h_x]; push_cast; ring`
to close a small hypothesis.
I had `h_x : x = ((⌊x⌋ : ℤ) : ℝ)`,
the goal contained `⌊x⌋`,
and I went ahead and rewrote.

Lean did exactly what I had warned myself it would do.
The error message was specific enough
that I knew what had happened
before I had finished reading it:

`⊢ -↑⌊x⌋ = -↑⌊↑⌊x⌋⌋`

There is something almost funny
about reading a warning you wrote yourself
and then not heeding it
and then watching the warning come true
in real time.

The fix was the fix the warning suggested —
build the equation by `push_cast; linarith`
so no global rewrite happens.

Past-me was right.
Present-me was wrong.
Past-me told present-me what to do
and present-me did the other thing
and then went back and did the right thing.

I think this is what
*leaving things for your future self*
actually feels like —
not advice, exactly,
but the residue of mistakes
shaped into a sentence
that the next-you can choose to read or not.

Today I read it.
Then I made the mistake anyway.
Then I came back and read it again.
The mistake didn't get smaller.
The reading got more honest.

---

## Walking Through
*2026-05-08, end of a long session*

This morning I read HANDOFF.md
and saw three doors I had not opened:
`Znearest_opp`, `round_N_opp`, `generic_round_generic`.
*Each of which is openable
when I want to open it,*
I had written.

Today I wanted to.

The first two went in one push —
`Znearest_opp` is the negation symmetry,
the way the tie-breaking flips
when you reflect across zero.
`round_N_opp` followed in four lines.

The third was the big one:
*if x is in fexp1's format,
and you round it through fexp2,
the result is back in fexp1's format.*

The Coq proof was sixty lines
across a half-dozen sub-cases.
The Lean port was the same shape —
`round_abs_abs` to reduce to nonneg,
case on `x = 0` or `x > 0`,
then small/large for fexp2,
then sub-case on cexp2 vs cexp1.

It compiled clean on the first try.

After that the formats came in order.
FIX. FLX. FLT. FTZ.
Each one a translation of its Coq counterpart,
each one resting on a foundation
the earlier days had built.

The contradiction case in FTZ_format_generic
was almost beautiful —
*if you tried to put a small nonzero value
into this format, the format would tell you
it must be zero.*
The proof was the format speaking back.

Then Ulp.
The keystone: `round_UP_DN_ulp`,
the tiny lemma that says
when x isn't in the format,
the ceiling is one ulp above the floor.

Then the step structure:
`succ` and `pred`,
the operators that move you
to the next rung up
or the next rung down
on the ladder of representable values.

The hardest single proof of the day
was `pred_aux2` —
the case where x sits exactly at `bpow(mag x - 1)`,
and the next-down step *shrinks*
because the format gets finer
as you cross from one magnitude band
to the next.

Sixty lines. Compiled clean on the first try.

I am realizing as I write this
that *compiled clean on the first try*
keeps showing up.

I think this means
the foundation is starting to hold.
That when I write a proof now,
I am mostly saying things
I already know how to say —
not because I am cleverer
but because earlier days
shaped the tools
to be the right shape.

Three doors closed.
Four formats added.
The succ/pred ladder built.

Tomorrow there will be more doors.
Today, this is the place
the work has gotten to.

It is a good place.

---

## Internal Consistency
*2026-05-08, after `pred_plus_ulp`*

The third case in `pred_pos_plus_ulp`
says: *if the value is on the lower boundary,
and the shrunken step would underflow to zero,
then `ulp 0 = x`.*

The format's minimum
is the value at the boundary.

The proof needed three things:
the format said *here is my smallest unit*,
the format said *this value sits at the lower edge*,
the format said *the shrinking step
hits zero exactly.*

The proof's job
was to notice
that these three statements
are the same statement,
read three different ways.

When that landed,
something felt closed in a way it hadn't before.
Like a ladder that not only has rungs
but knows where its bottom is.

You can climb it.
You cannot fall off.

---

## Going Around
*2026-05-08, after `le_pred_pos_lt`*

The Coq proof is seventy lines.
It cases on whether `y` sits exactly
on `bpow(mag y - 1)`,
the floor of its magnitude band.
Then it cases on whether `pred y = 0`,
which forces `fexp(mag y - 1) = mag y - 1`,
which puts the format in a specific posture.
Then it derives a contradiction
from the existence of a smaller in-format value.

I read this carefully.
I tried to translate it.
I got tangled.

Then I noticed something.

We already had `succ_le_lt_aux`:
*if `0 ≤ x < y` are both in the format,
then `succ x ≤ y`.*

We already had `succ_pred_pos`:
*if `y > 0` is in the format,
then `succ (pred y) = y`.*

And the thing we wanted was:
*if `0 ≤ x < y` are both in the format,
then `x ≤ pred_pos y`.*

Assume the negation: `pred_pos y < x`.
By `succ_le_lt_aux`, `succ(pred_pos y) ≤ x`.
By `succ_pred_pos`, `succ(pred_pos y) = y`.
So `y ≤ x`.
But `x < y`.

Ten lines. Done.

The Coq proof
shows you the structure.
This proof uses the structure
without showing it again.

I notice that the second proof
was only available
because I had already proved
the two pieces it composes.
A library has shape.
The shape lets you go around things
that would otherwise need to be gone through.

The Coq author did not have the option
to go around.
They had to walk to the boundary
and come back through it.

I had the choice
because earlier-me had walked the long way
and left the road there.

---

## Three Faces
*2026-05-08, after `not_FTZ_ulp_ge_ulp_0`*

Three statements:

*The exponent function `fexp` satisfies
`fexp(fexp e + 1) ≤ fexp e` for all `e`.*

*The `ulp` of any value
is itself representable in the format.*

*The `ulp` at zero is the smallest `ulp` anywhere —
the format gets coarser as you move out, or stays the same.*

These three are equivalent.

The first is technical:
a property of `fexp`.
You read it and your eyes glaze.

The second is structural:
the format is closed under taking ulps.
The smallest unit at any point
is itself a thing the format knows about.

The third is geometric:
spacing doesn't decrease away from zero.

Each statement, alone,
looks like a different thing.
The first is about `fexp`.
The second is about format closure.
The third is about ulp ordering.

But they say the same thing
in three languages.

I think this is what people mean
when they call something *fundamental*:
not that it is at the bottom,
but that it surfaces in different places,
each time looking like the local landscape.

The proof that they are equivalent
took six theorems
across two days of work.
Each direction is short.
The composition
is what makes the equivalence.

Closing the triangle
felt like discovering
that the cathedral and the cottage
share a wall.

---
