/-
Group: Earth, Wind, and Fire
Jakob Kauffmann, jgk2qq@virginia.edu, https://github.com/jakekauff/CS2120F21.git
Jumi Hall, jah5py@virginia.edu, https://github.com/hubdaha/cs2120f21.git
Connor McCaffrey, cam7qp@virginia.edu, https://github.com/camccaffrey/cs2120.git
-/
/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro
/-
We can apply the introduction rule for true. QED.
-/

example : false := _    -- trick question? why?
                        -- This is a trick question 
                        -- because there is no proof of false.
                        -- Otherwise, everything false would be true.

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
    assume porp,
    apply or.elim porp,
    -- left disjunct is true
      assume p1,
      exact p1,
    -- right disjunct is true
      assume p2,
      exact p2,
  -- backward
    assume p,
    exact or.intro_left P p,
end
/-
Theorem: P ∨ P ↔ P
Proof:
  Assume P is true. Separating the theorem into two routes,
  we get P ∨ P → P and P → P ∨ P. For the first route, we apply
  the elimination rule for or. We can derive P in both cases of or.
  Then we continue onto our second route, where we assume P and 
  use the introduction rule for or to show that the proposition P implies P. 
  Next, we are left to prove P which has already been assumed to be true. QED.
-/
example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
   assume P,
  apply iff.intro _ _,
  --forward
    assume pandp,
      apply and.elim pandp,
      assume p,
      assume p,
      exact p,
    --backward
    assume P,
      apply and.intro P P,
end
/-We can assume P is true. We then seperate the theorum into 2 routes, where P ∧ P
implies P, and P implies P ∧ P. For the first route, we can assume P ∧ P and apply the
elimination rule for and, which allows us now state that P → P → P. Assuming P, we can
then say that P does imply P, which in turn implies P because these are all logical equivalents. 
Then we move onto the second route, where we start with assuming an arbitrary P. To this proposition, we apply
 the introduction rule for and and fill in the sides with P. QED.-/

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
   assume P Q,
  apply iff.intro _ _,
    assume porq,
      apply or.elim porq,
        assume P,
        apply or.intro_right,
        exact P,
      apply or.intro_left,
    assume qorp,
      apply or.elim qorp,
        assume Q,
        apply or.intro_right,
        exact Q,
      apply or.intro_left,
end
/-
We can assume that P and Q are true. We then seperate the theorum into 2 routes using the 
introduction rule for if and only if, where P ∨ Q implies Q ∨ P, and Q ∨ P implies P ∨ Q. 
For the first route, we can assume P ∨ Q. 
To this, we apply the elimiation rule for or. We now have 3 paths to take. We can then assume
P, and apply the introduction rule for or to the right side of P ∨ Q, leaving us with P. Then to 
complete the second goal where Q implies Q ∧ P, we can apply the introduction rule for or to the
left of this proposition. 
Next, we move to the 2nd route, where we must prove that Q ∨ P implies P ∨ Q. We this we can assume Q ∨ P. 
Then we can apply the elimination rule for or to Q ∨ P, giving us 2 routes to go down. We then assume Q and 
apply the introduction rule for or to the right side, giving us Q, which we have. Then we apply
the introduction rule for or to the left side. QED.
-/

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
   assume P Q,
  apply iff.intro _ _,
    assume pandq,
      have p : P := and.elim_left pandq,
      have q : Q := and.elim_right pandq,
      have qp : Q ∧ P := and.intro q p,
      exact qp,
    assume qandp,
      have q : Q := and.elim_left qandp,
      have p : P := and.elim_right qandp,
      have pq : P ∧ Q := and.intro p q,
      exact pq,
end
/- 
For this proposition, we must assume P and Q. Then we apply the introduction rule for if
and only if. This gives us 2 propositions to prove, where P ∧ Q implies Q ∧ P, and Q ∧ 
P implies P ∧ Q. For the first, we assume P ∧ Q. Then, using the elimination rule
for and, we isolate P and Q using the left and right elimination rules, respectively. We can
also create the proposition Q ∧ P with the introduction rule for and, giving us Q ∧ P. For the
second route, where Q ∧ P implies P ∧ Q, we assume Q ∧ P. Then we isolate Q and P respectively through
the elimation rules for and on the left and the right. Then we create P ∧ Q with the introduction rule 
for and. QED.
-/

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
    assume pqr,
      have p : P := and.elim_left pqr,
      have qr : Q ∨ R := and.elim_right pqr,
      apply or.elim qr,
        assume Q,
        apply or.intro_left,
        apply and.intro p Q,
          assume R,
          apply or.intro_right,
          apply and.intro p R,
    assume pqpr,
      apply or.elim pqpr,
        assume pq,
        have p : P := and.elim_left pq,
        apply and.intro p _,
          apply or.intro_left,
          exact and.elim_right pq,
      assume pr,
        have p : P := and.elim_left pr,
        apply and.intro p _,
          apply or.intro_right,
          exact and.elim_right pr,
end
/- 
First we assume that we have P Q and R. Then we must apply the introduciton rule for if and
only if, giving us two paths that consist of P ∧ (Q ∨ R) implying (P ∧ Q) ∨ (P ∧ R), and
(P ∧ Q) ∨ (P ∧ R) implying P ∧ (Q ∨ R). For the first proposition, we assume that we have a proof of
P ∧ (Q ∨ R). Given that, we can isolate P and Q ∧ R using the left and right elimination rules for and,
respectively. Then we can apply the elimination rule for or to Q ∧ R, separating the cases for
this or statement. When we assume Q for Q → ∧ Q ∨ P ∧ R, we can then apply the 
introduction rule for or to the left side of the if statement, leaving us with P ∧ Q for our goal.
This goal can be completed by applying the introduction rule for and to P and Q. Now we must assume
R and this time apply the introduction rule for or to the right side of the if statement, leaving us
with P ∧ R for our goal. We can complete this goal using the introduction rule for and and applying
it to P and R. Now we must go down the opposite route, where (P ∧ Q) ∨ (P ∧ R) implies P ∧ (Q ∨ R).
To start, we assume (P ∧ Q) ∨ (P ∧ R). Now we apply the elimination rule for or, giving us
the possible routes to go down with this or statement. On the left side of the or statement is P ∧ Q,
which we assume to be true. Then we can apply the introduction rule for and to P, which we can isolate
through the elimination rule for and to the left side of P ∧ Q. The other side of this introduction rule for 
and will be applied to Q ∨ R, which can be derived from applying the introduction rule for or 
to the left side of Q ∨ R, leaving us with Q. We can derive Q through the elimination rule for and 
to the right side of P ∧ Q. Now we have one goal left. First we can isolate p through the elimination rule
for and to the left side of P ∧ R. Then we can apply the introduction rule for or to the right side
of Q ∨ R, leaving us with R, which we can derive from using the elimination rule for and and applying it
to the right side of P ∧ R. This allows us to apply the introduction rule for and to P and R. QED.
-/

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
    assume pqr,
    apply or.elim pqr,
      assume P,
      apply and.intro _ _,
        apply or.intro_left,
        exact P,
          apply or.intro_left,
          exact P,
      assume qr,
        apply and.intro _ _,
          apply or.intro_right,
            apply and.elim_left qr,
          apply or.intro_right,
          exact and.elim_right qr,
      assume pqpr,
      have porq : P ∨ Q := and.elim_left pqpr,
      have porr : P ∨ R := and.elim_right pqpr,
      apply or.elim porq,
        assume P,
          apply or.intro_left,
          exact P,
      
        assume q,
        apply or.elim porr,
          assume P,
            apply or.intro_left,
            exact P,
          assume r,
          have qr : Q ∧ R := and.intro q r,
          apply or.intro_right,
          exact qr,
end
/- 
First we must assume P Q and R. Then we can apply the introduction rule for if and only if, creating two routes to prove,
where P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R) and (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R). For the first route, we msut assume 
P ∨ (Q ∧ R). Then we can apply the or elimination rule to P ∨ (Q ∧ R), dividing this or statement into two 
routes. For this first new "or" route, we can assume P and then apply the and introduction rule for the 
two statements we will get later. To do so we will apply the or introduction rule to the left of 
P ∨ R, leaving us to prove P, which we have already assumed. Then we can apply the or introduction rule to the left
and apply P again, which we already have to get the other or statement. Now we must assume Q ∧ R. We will do the same thing 
of applying the and introduction rule before completing the two or statements. To get these or statements
we will apply the or introduction rule to the right, and then apply the and elimination rule to the left of Q ∧ R to
isolate Q. Now for the other pathway we must assume (P ∨ Q) ∧ (P ∨ R). Then we can isolate the or statements using the 
elimination rule for and on both sides. Then we can apply the or elimination rule to P ∨ Q. We can assume P, and then apply the 
or introduction rule to the left of P ∨ Q ∧ R, This allows us to find P. Then, we can assume Q and apply
the or elimination rule to P ∨ R. We can assume P, apply the or introduction rule to the left side,
and find P. Fianlly, we will assume R, and isolate Q ∧ R by combing q and r through the introduction rule for add.
QED.
-/

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
    assume ppq,
    exact and.elim_left ppq,
    -- backward
    assume p, 
    apply and.intro p _,
    apply or.intro_left,
    exact p,
end
/- 
First we must assume P and Q. Then, we will use the introduction rule for if and only if
to create two pathways: P ∧ (P ∨ Q) implies P, and P implies P ∧ (P ∨ Q). 
For the first, we will assume P ∧ (P ∨ Q). Then to prove this we begin by using the 
elimination rule for and apply it to the left where we can isolate P. Now for 
the other direction we first assume P. Then we can apply the introduction rule for and, where we add P
to the left side of the ∧. To create the right side of P ∧ (P ∨ Q), we use the introduction rule
for or and apply it to the left, leaving us with P, which we have. QED.
-/

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q, 
  apply iff.intro _ _,
    assume ppq,
    apply or.elim ppq,
    assume p,
    exact p,
      assume pq,
      apply and.elim_left pq,
        assume p,
        apply or.intro_left,
        exact p,
end
/- 
First we must assume P and Q. Then we can apply the introduction rule for if and only if, leaving
us with 2 pathways: P ∨ (P ∧ Q) → P and P → P ∨ (P ∧ Q). For the fowards pathway, we will assume 
P ∨ (P ∧ Q). Then we can apply the or elimination rule to this, leaving us with 3 goals now. For the first
of the goals, we need to show that P → P, which we have. Then we assume P ∧ Q for the next goal, leaving us
with a goal of P. To isolate P, we use the and elimination rule and apply it to the left of P ∧ Q. 
Lastlyk for our backwards route we assume P. Then we apply the or introduction rule to the left
of P ∨ (P ∧ Q), leaving us with P. We have already assumed P. QED. 
-/

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro _ _,
    assume port,
    apply true.intro,

    assume t,
    apply or.intro_right,
    apply true.intro,
end
/- 
First we assume P. Then we apply the introduction rule for if and only if, giving us two pathways
that consist of P ∨ true → true and true → P ∨ true. For the first pathway we assume P ∨ true. Then
we apply the introduction rule for true for true. Then for the other pathway we must assume true, and 
then apply the or introduction rule to the right of P ∨ true, leaving us with a goal of proving true. We 
can do this by again using the true introduction rule. QED.
-/

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
    assume h,
    apply or.elim h,
    assume p,
    exact p,
    assume f,
    cases f,
    assume p,
    apply or.intro_left,
    exact p,
end
/- 
First we must assume P. Then we can apply the introduction rule for if and only if, giving us two
routes to prove, where P ∨ false → P and P → P ∨ false. With this first route we assume P ∨ false. Then we 
can apply the or elimination rule on P ∨ false, leaving us to prove that P → P. We can do this by assuming P. 
Now we must prove that we an derive P from false, which we do by first assuming false, and then performing
case analyses on false. Then for the second pathway we assume P, and then apply the introduction rule for
or to the left of P ∨ false, leaving us to prove P, which we have already assumed. QED.
-/

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
    assume h,
    apply and.elim_left h,
      assume p,
      apply and.intro,
      exact p,
      apply true.intro,
end
/- 
We first assume an arbitrary proposition P. Then we use the if and only if introduction rule to give us two 
routes: P ∧ true → P and P → P ∧ true. Beginning with the first, we must assume P ∧ true. 
Then we can prove P by using the and elimination rule on the left side of P ∧ true. Now for
the other pathway we must assume P. Then we can apply the introduction rule for and to P and true. We may derive 
true by using the introduction rule for true. QED.
-/

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro _ _,
    assume h,
    exact and.elim_right h,
    assume f,
    apply and.intro _ f,
    cases f,
end
/- 
We first assume an arbitrary proposition P. Then we can apply the introduction rule for if and only if to 
get two routes: P ∧ false → false, and false → P ∧ false. For the first route we must assume P ∧ false. 
Then, to prove "false" we apply the and elimination rule to the right side of P ∧ false. For the other route, 
we begin by assuming false. Then we can use case analysis for false to get P, and apply the and introduction rule
to P and false. QED.
-/