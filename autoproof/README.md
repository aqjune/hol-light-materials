# hol-light-autoproof

Dependencies:

- hol-light with local build.
- `expect`: can be installed with APT in Ubuntu
- Your best code agent, such as:
  * Claude Code, possibly connected to your Amazon Bedrock and model set to Opus 4.5. See also: https://code.claude.com/docs/en/amazon-bedrock
  * `kiro-cli` also works well with Opus 4.5

Step 0. In your work directory (e.g., hol-light, s2n-bignum, or anything else) create a symbolic link to this 'autoproof' directory:
```bash
pwd
# /home/ubuntu/s2n-bignum
ln -s <your hol-light-material>/autoproof ./autoproof
```

Step 1. Build a checkpointed binary of HOL Light.

```bash
export HOLLIGHT_DIR=/home/ubuntu/hol-light # Or any other HOL Light dir
$HOLLIGHT_DIR/make-checkpoint.sh ckpt.sh 'loadt "Library/words.ml"'
```

Step 2. Clone the HOL server from Alexey's repo.

```bash
git clone https://github.com/monadius/hol_server.git --branch vscode
```

Step 3. Run the server

```
expect autoproof/run-hol-server.exp ./ckpt.sh
```

Step 4. Open another terminal, go to `$HOLLIGHT_DIR`, make a soft link to this autoproof directory as a subdirectory.

Step 5. Copy INSTRUCTION.md from this directory to your workspace directory (e.g., s2n-bignum). Then, start your best agent (Kiro, Claude, etc)! A sample goal is at goal-sample.txt in this directory. The output of Opus from the sample goal is at work-sample.txt!

```
(Launch Claude Code or kiro-cli, and run the following command)
Read INSTRUCTION.md and start the task. Could 
Theorem: multiplication of two 64-bit vectors equals splitting each 64-bit vector into two high and low 32-bit vectors, multiplying each arm, and adding together with shifts.
```
