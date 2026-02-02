# Rules for Working on HOL Light proofs

## The Goal
- Your goal is to autoformalize the English statement about bit-vectors in goal.txt in HOL Light and write its proof in HOL Light.
- Your working proof must be stored at the work.ml file. Your final theorem (both autoformalized statement and proof) must also be written in work.ml.
- Your work.ml might contain some scribbings about previous attempts. You must carefully read the existing text first and think how to incrementally update it, rather than rewriting everything from scratch.
- Finish the proof so that there is no axiom-introducing commands (CHEAT_TAC and new_axiom) in work.ml.

## STRICT PROHIBITIONS

### ⛔ **ONLY edit in the file work.ml and scratchpad.txt**
- **NEVER edit any other files**

### Never throw away useful work from work.ml
1. You should almost never revert to previous backups (you can use temporary admits - `CHEAT_TAC` - when something is hard).
2. If there is a really major reason for reverting, you have to salvage all the useful work done in between.
3. In particular, you have to ensure that all compiling theorems and definitions added since are kept.
4. If you later discover such screwup, you have to immedially start working on salvaging the lost work.
5. **SIMPLE CHECK**: after each backup, run wc on the current and previous backup. If the current backup is smaller, you have to explicitly justify (in the CHANGES file) the decrease and explain that you have not thrown out useful work.

### Do not throw away useful lemmas
- After proving a lemma, don't throw it away. Copy it from scratchpad.txt to work.ml, and keep it.

### Do not rebuild your own infrastructure
- You should **AVOID** duplicating lemmas that are readily available in the whole library unless it's reasonably useful/justified. "Building up infrastructure" is typically not a good justification.

### Do not invoke the `ocaml` program or `pkill`.
- Using `ocaml` won't give any meaningful result. Always use the `hol_client` script.
- Also, don't use `pkill` to kill HOL Light REPL. The 'hol_client.py' script already uses 30-seconds timeout.

## HOL Light Language Details

### Logic System
- **This is classical HOL Light** (no constructivism)
- Law of excluded middle is always available
- Can use proof by contradiction freely.
- **Only use `(* … *)` for comments** - no other comment syntax; no `*` inside comments

### Useful references
- Read/grep file VERYQUICK_REFERENCE.txt frequently to see what to use (tactics, theorems, etc).
- Even more information in QUICK_REFERENCE.txt - you can grep it too.
- The 'Help/' directory in HOL Light contains many useful documents for available tactics and conversions.
- A lot of related definitions and lemmas are in Library/words.ml - grep it often for existing defs and theorems.
- The 'autoproof/../materials/' directory contains markdown files that has descriptions about important concepts and how to deal with certain kinds of problems in HOL Light.
- You can/should also search for useful lemmas in the whole library, these are files such as sets.ml, real.ml, the whole Library directories, etc.

### Use the `search` command
- You can use the 'search [`<pattern>`, `<pattern2>`, ...]' command in HOL Light to look for theorems that include certain subterms.
- It can also receive an argument that must be contained in the name of the theorems. The `Help/search.hlp` file will contain a few examples.
- This 'search' command is very cheap and effective.

## Work Strategy

### 1. Sketch a high-level proof structure in English
- Write a high-level structure of your proof in English first, and leave this as a comment in work.ml.
- This methodology is known to be effective by the Numina theorem prover.

### 2. Interactively prove the theorem
- You are going to interactively build a proof. The interactive setting starts with the `g` command. For example,
```
g `(x + 2) * y = x * y + 2 * y`;;
```
will set up a new goal that you will want to prove.
To send this command, store this command at `scratchpad.txt`, and run
```
python3 hol-light-autoproof/hol_client.py localhost:30000 scratchpad.txt
```
This will print the standard output from HOL Light REPL in the JSON format.
- You can apply a tactic through the `e` command. For example, storing
```
e `ARITH_TAC`;;
```
at 'scratchpad.txt' and running the 'hol_client.py' as described above will update the goal.
- If there is no subgoal remaining after `e`, the proof is fully proven. You can name this theorem through the let binding and `top_thm()` like this:
```
let MY_THEOREM = top_thm();;
```
Note that if the proof is written using the alternative `prove(...)` style, there will also be a no subgoal. However, this does not imply that the proof in `prove(...)` is complete because the `prove(...)` may have failed or include `CHEAT_TAC`.
- If you made a progress after your `e` command, log the command at 'work.ml' with a proper comment if necessary. Since the scratchpad.txt file is easily overwritten by your next steps, it is very easy to forget what you have written before (and will unable to reconstruct it later).
- Refer to the 'Help/g.hlp' and 'Help/e.hlp' and 'Help/top_thm.hlp' files for further understanding.

### 3. When is your work finished?
- Your work is finished when
(1) 'work.ml' starts with a `g` command that is autoformalization of the statement in goal.txt,
(2) running your series of `e` commands end up leaving no subgoal,
(3) running 'work.ml' does not raise any Failure or Error (this means there are incomplete proofs)
(3) your code does not introduce any axiom or use CHEAT_TAC.
- If you think the work is done, check whether 'work.ml' is fine by running
```
loadt "work.ml";;
<the top-level theorem>;;
```
Write these two lines at 'scratchpad.txt', and invoke the 'hol_client.py'.
- Finalize the successful proof of `g`-`e` form by converting to the `prove(<goal>, <tactic>)` form.

### Incremental proof update
- You can do the following things in any order but you should always progress and produce some more code. 
- Keep carefully fixing any incorrect/bad definitions/theorems you find (note that this may lead to fixing some proofs, etc).
- Keep eliminating stubs, replacing them with more complete theorems and definitions (gradual/partial approaches are ok when needed).
- Keep replacing CHEAT_TAC in unfinished proofs with more complete proofs (which can re-introduce CHEAT_TAC). This may also lead to adding more auxiliary lemmas/theorems.
- While doing the above, remember that:
- Doing easy things is initially OK, however, don't be afraid to try to do (gradually/partially if needed) some harder theorems too. Don't endlessly jump around looking for easy things - that wastes time.
- Balance simple infrastructure theorems with more challenging results
- Use gradual/partial approaches for difficult theorems when needed (and don't delete such started partial proofs - use temporary "CHEAT_TAC" in their various branches and keep gradually eliminating those). Also, structure bigger proofs into useful top-level/helper lemmas wherever possible.
- Also, always grep all current definitions and theorems in work.ml  before creating a new one. Be sure to remove/avoid duplicities.
- Never introduce axioms. It's better to have admitted theorems (CHEAT_TAC) that will be (hopefully) eventually proved.

### Please back up frequently
- **Run the checking frequently** (`loadt "work.ml";;`) to check for compilation errors
- Whenever you write something to scratchpad.txt, and it seems to make some progress, log it at work.ml as well, with comments if necessary.
- Often do numbered backups of work.ml like bck0007. Even when work.ml doesn't compile. Saving you partial attempts is important for not running in circles!
- With each numbered backup, also write the numbered summary changes file like CHANGES0007 (it should really be a summary, not just a simple diff).
- You can lookup your previous work in these CHANGES files when unsure how to continue.
- Never overwrite an older backup file. The numbering has to continue from the latest number. You must find it by running: ls bck* | sed 's/[^0-9]*//g' | sort -n | tail -n 1.


## Proof Style

### Proof style discipline

Use a small, stable set of tactics such as:
- REWRITE_TAC, ASM_REWRITE_TAC, or PURE_REWRITE_TAC if it helps
- SIMP_TAC, ASM_SIMP_TAC
- MATCH_MP_TAC
- MESON_TAC, ASM_MESON_TAC
- X_GEN_TAC, DISCH_TAC, STRIP_TAC
- WORD_ARITH, WORD_RULE, BITBLAST_TAC
Avoid clever or exotic tactics unless unavoidable.
- Use SUBGOAL_THEN often: It is often much easier to debug declarative proofs with clear intermediate goals.
- Try to structure longer proofs into many lemmas with shorter proofs.
It is okay for a proof to have more than 100 tactic commands.
- This is common in HOL Light proofs.
- However, if possible, breaking a larger proof into several lemmas is still better.

## Important Word of Advice - After Observing 8 Hours of Inefficient Work
You seem to be too easily throwing away and forgetting what you
already did or tried. Also, you are losing partially finished proofs
by frequent reverting to previous "compiling" backups (which however
have CHEAT_TAC for things that you already proved). The updated
CLAUDE.md tells you how to address this (but you are either not
re-reading it or ignoring it). Long story short: 
1. Re-read (and then remember/follow) CLAUDE.md frequently. 
2.  Structure the long proofs into many smaller toplevel lemmas so
that things don't get so complex and you don't throw away finished
work over and over.
3. If (2) is hard, structure the longer proofs (and subproofs)
declaratively into many explicit intermediate lemmas using
SUBGOAL_THEN (and possibly many CHEAT_TAC that you gradually
eliminate) - that will help you not to get confused by a complex proof state.
4. As soon as you start getting in trouble with counting brackets,
   it's a clear sign that you have to do more of (2) or (3)
5. Never throw partially finished things away and do frequent backups.

