# Rules for Working on HOL Light proofs

## The Goal
- Your goal will be given by a user. It will be about a problem in HOL Light.
- If not stated otherwise, your working proof must be stored at the work.ml file. Your final theorem (both autoformalized statement and proof) must also be written in work.ml.
- Finish the proof so that there is no axiom-introducing commands (CHEAT_TAC and new_axiom) in work.ml. Do not stop until every CHEAT_TAC or new_axiom is removed.

## Files
- You can read any file in this directory.
- Unless specified otherwise, you can write to the following files.
  * work.ml: the main proof
  * scratchpad.txt: a snippet of code or proof that you would like to interactively run on HOL server and get output
- You can also write to other files if goal.txt allows that.

## STRICT PROHIBITIONS

### 1. Do not invoke the `ocaml` program or `pkill`.
- Using `ocaml` won't give any meaningful result. Always use the `hol_client` script.
- Also, don't use `pkill` to kill HOL Light REPL. The 'hol_client.py' script already uses 30-seconds timeout.

### 2. Do not use `loadt` or `loads`. Only use `needs`
- To use a library .ml file, use `needs "<the .ml>"`. `load{t,s} "<the .ml>"` will cause duplicated loading time.
- Note that "arm/proofs/base.ml" is already loaded in the server. Reloading any of these file through `loadt`/`loads` will cause extra time and its long standard output will also occupy your context.

### 3. Don't use too many `e` commands when you are debugging.
- Each `e` will make HOL Light print the next intermediate goal state.
- If there are too many `e`  calls in scratchpad.txt, the returned text will be big, consuming lots of tokens.
- Try to combine multiple tactics with `THEN` instead, and execute the combined tactics with a smaller number of `e`.

### 4. Do not throw away useful lemmas
- After proving a lemma in scratchpad.txt, don't throw it away. Copy it from scratchpad.txt to your work file (e.g., work.ml), and keep it.

### 5. Do not rebuild your own infrastructure
- You should **AVOID** duplicating lemmas or tactics that are readily available in the whole library unless it's reasonably useful/justified. s2n-bignum will already have lots of basic tactics, conversions and lemmas that deal with basic properties of program states. Don't prove them again.


## HOL Light and s2n-bignum details

### HOL Light
- **This is classical HOL Light** (no constructivism)
- You can use `define` or `new_definition` or other functions to define a new constant, However, once a constant is defined, you can modify the definition of the constant using `define` or `new_definition`. You will have to pick a new name.
- **Only use `(* … *)` for comments** - no other comment syntax; no `*` inside comments
- `PRINT_GOAL_TAC` will print the goal.
- Note that having `CHEAT_TAC` inside `prove()` will make the `prove` silently succeed. Therefore, it is very important to double check there is no `CHEAT_TAC` at all.
- Never introduce axioms. It's better to have admitted theorems (CHEAT_TAC) that will be (hopefully) eventually proved.

### Useful references in HOL Light
- The `$HOLLIGHT_DIR` will point to the HOL Light directory. If the `$HOLLIGHT_DIR` environment variable is not set, please refer to {arm,x86}/Makefile. It will be the `HOLDIR` variable. If the Makefile is not available, it is either the current directory, or `<home dir>/hol-light`.
- The '`$HOLLIGHT_DIR/Help/`' directory contains many useful documents for available tactics and conversions. 
- A lot of definitions and lemmas related to bit-vectors are in `$HOLLIGHT_DIR/Library/words.ml` - grep it often for existing defs and theorems.
- You can/should also search for useful lemmas in the whole library, these are files such as sets.ml, real.ml, the whole Library directories, etc.

### Use the `search` command
- You can use the 'search [`<pattern>`, `<pattern2>`, ...]' command in HOL Light to look for theorems that include certain subterms.
- It can also receive an argument that must be contained in the name of the theorems. The `Help/search.hlp` file will contain a few examples.
- This 'search' command is very cheap and effective.

### Useful references (more)
- The 'autoproof/parentdir/materials/' directory contains markdown files that has descriptions about important concepts and how to deal with certain kinds of problems in HOL Light.
- If this project is s2n-bignum, he '{arm,x86}/tutorial' directory has many interesting examples explaining how to verify simple programs.
- If this project is s2n-bignum and the 'description' directory is available, it will have descriptions about s2n-bignum and HOL Light tactics including examples that actually appear in s2n-bignum proofs.


## Work Strategy

### 1. Sketch a high-level proof structure in English
- Write a high-level structure of your proof in English first, and leave this as a comment.
- This methodology is known to be effective by the Numina theorem prover.

### 2. Interactively prove the theorem
- You are going to interactively build a proof. The interactive setting starts with the `g` command. For example,
```
g `(x + 2) * y = x * y + 2 * y`;;
```
will set up a new goal that you will want to prove.
To send this command, store this command at `scratchpad.txt`, and run
```
python3 autoproof/hol_client.py localhost:30000 scratchpad.txt
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
(1) your work file (e.g., 'work.ml') has a theorem that formalizes the statement in goal.txt and its proof passes.
(2) running 'work.ml' does not raise any Failure or Error (this means there are incomplete proofs)
(3) your code did not use `CHEAT_TAC` or `new_axiom`.
- If you think the work is done, check whether 'work.ml' is fine by running
```
loadt "work.ml";;
<the top-level theorem>;;
```
Write these two lines at 'scratchpad.txt', and invoke the 'hol_client.py'.

### Back up frequently with changes
- Often do numbered backups of work.ml like bck0007. Even when work.ml doesn't compile. Saving you partial attempts is important for not running in circles!
- With each numbered backup, also write the numbered summary changes file like CHANGES0007 (it should really be a summary, not just a simple diff).
- Never overwrite an older backup file. The numbering has to continue from the latest number. You must find it by running: ls bck* | sed 's/[^0-9]*//g' | sort -n | tail -n 1.
- **Do not write a back up that fails proof check.**


## s2n-bignum tactics

- In principle, the high-level tactics like ARM_STEPS_TAC will deal with most of the automations including disjointness of program state components like PC and memory.
- Don't dive too much into the details and try to stick to the high level tactics
- The descriptions/ directory will have use cases. Also, try to read the comments of the definitions of tactics in .ml files. These can give good insights.
