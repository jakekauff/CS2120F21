/-
BACK TO PROPERTIES OF RELATIONS
-/

/-
So now let's revisit once again our funny example of
transitivity: { (0,1), (2,3) }. There are no cases 
here where we have both (x,y) and (y,z) as pairs in
this relation, so there are no cases to consider. 
When there are no cases to consider, the conclusion
holds in all cases, of which there are 0, so it holds.

Question: Is this symmetric? {(0,1), (1,0), (2,2)} 
__Yes, this relation is symmetric because the relation__
__contains only pairs where we have both (x,y) and (y,x),__
__where x = 1 and y = 0, as well as x, y = 2__

How about this: {(0,1), (1,0), (2,3)}?
__No, this relation is *not* symmetric because the__
__it does not contain the pair (3, 2)__

Now suppose that we have a relation, r, over a set
of values, {0, 1, 2, 3, 4, 5}. Is this relation
reflexive? {} 
__Yes, this relation is reflexive because the empty__
__set technically has all properties.__

What about this: {(0, 1), (2, 3)}
__No, this relation is not reflexive because it does__
__not contain any pairs (x, x) where x = 0, 1, 2, 3, 4, 5.__

Question: If a relation is transitive and symmetric
is it necessarily reflexive? If so, give an informal
argument/proof. If not, give a counter-example. 
__If a relation is transitive and symmetric, it is *not*__
__necessarily reflexive. An example of a relation that__
__is transitive and symmetric, but not reflexive is__
__as follows:__

__Suppose we have a relation, r, over a set of__
__values, {1, 2, 3, 4}. Relation r = {(1, 2), (2, 1), (2, 2), (1, 1)}.__
__Relation r is transitive because we have that__ 
__r 1 2 and r 2 1. Furthermore, it is symmetric__
__for the same reason. However, because r is a relation over__
__a set of values {1, 2, 3, 4}, it is not reflexive because__
__the pairs (3, 3) and (4, 4) are not in the relation.__
-/

/-
Exercise: We started our discussion of properties of binary relations on 
values of a type, β, with the case of what it means for such a relation to
be total: that every pair of objects is related at least in one direction
or the other. Think of this as saying that any two objects are comparable.
In the less-or-equal relation on natural numbers, you can compare any pair
of natural numbers. The subset inclusion relation, on the other hand, is
not total. It is said to be partial. 

Consider the subset relation on the powerset of {0, 1}, that is, on the
sets {0, 1}, {0}, {1}, {}. The subset relation is not total. Its elements
are ({},{}), ({}, {0}), ({}, {1}), ({}, {0,1}), ({0}, {0}), ({0}, {0,1}),
({1}, {0,1}) ({0,1}, {0,1})}. Draw these sets as "nodes" in a graph and
the pairs as directed edges between the nodes. Is the relation depicted
in this way a total order? A partial order? What properties does it have?
-/

/-
Definitions vary subtly. Be sure you know what is meant by these terms in any
given setting or application.
-/


/-
Exercises: show that image and preimage
preserve some important properties and 
not others.
-/

/-
Formally define what it means for a relation
to be a well-order.
-/

example : 
  function r → 
  surjective r → 
  image_set r (dom r) = { b : β | true} :=

begin
  unfold function surjective image_set dom,
  assume f s,
  apply set.ext,
  assume x, 
  split,
  
  -- forward
    assume h,
    exact true.intro,

  -- backward
    assume h,
    cases s with svr sur,
    have exa := sur x,
    cases exa with a pfa,
    -- rewrite goal to a simple, definitionally equal version
    show ∃ (a : α), a ∈ {a : α | ∃ (x : β), r a x} ∧ r a x,
    apply exists.intro a,
    split,
    show ∃ (x : β), r a x,
    apply exists.intro x,
    assumption,
    assumption,
end

example : bijective r → function (inverse r) :=
begin
  unfold bijective function inverse,
  unfold surjective injective single_valued function,
  assume bij,

  cases bij with surf injf,
  cases surf with sv sur,
  cases injf with sv inj,

  -- show that result is single_valued
  assume x y z,
  assume ryx rzx,
  exact inj ryx rzx,
end