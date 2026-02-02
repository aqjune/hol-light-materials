# hol-light-autoproof

Dependencies:

- hol-light with local build.
- `expect`: can be installed with APT in Ubuntu
- Claude Code, possibly connected to your Amazon Bedrock and model set to Opus 4.5. See also: https://code.claude.com/docs/en/amazon-bedrock

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
expect run-hol-server.exp ./ckpt.sh
```

Step 4. Go to hol-light, make a soft link to this hol-light-autoproof as a subdirectory, copy CLAUDE.md to hol-light

Step 5. Write to goal.txt your goal of interest in English, and start claude! A sample goal is at goal-sample.txt in this directory. The output of Opus from the sample goal is at work-sample.txt!

```
(Launch claude, and run the following command)
Reread CLAUDE.md and start the task
```
