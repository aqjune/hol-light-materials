# HOL Light Setup

## 1. Building HOL Light

Assuming that [OPAM](https://opam.ocaml.org/doc/Install.html) is installed in your machine, you can install HOL Light from OPAM.
This will copy `hol.sh` to an executable path so that you can run `hol.sh` from anywhere.

```
opam install hol_light
```

Running `hol.sh` will launch an OCaml REPL with the kernel of HOL Light loaded, after
lengthy message prints for a few minutes.

Or, you can easily build HOL Light by yourself using the following instructions which are also described in [README](https://github.com/jrh13/hol-light/blob/master/README):

```
git clone https://github.com/jrh13/hol-light.git
cd hol-light
make switch # use 'make switch-5' if you want to use OCaml 5
eval $(opam env)
make
# Now you have 'hol.sh' .
```

**s2n-bignum**. If you want to build s2n-bignum proofs, you will want HOL Light with module compilation turned on.
Please see the 'Compiling HOL Light proofs' section below.

## 2. Setting up VSCode

It is possible to just rely on `hol.sh` and a text editor to develop,
by writing a statement, copying it to `hol.sh`, and seeing the output.
However, there is more ergonomic way to develop in HOL Light.

As an editor, I recommend the [vscode-hol-light](https://github.com/monadius/vscode-hol-light) plugin ([marketplace](https://marketplace.visualstudio.com/items?itemName=monadius.hol-light-simple)).
After installing it, you will want to:

1. Configure `hol-light.path` to your HOL Light directory. If you built HOL Light by yourself, this will be simply the cloned directory. If you downloaded & installed HOL Light from OPAM, it will be `<your home dir>/.opam/<ocaml version>/lib/hol_light`.
3. Associate `.ml` file extension with the HOL Light language, if you are planning to use the `.ml` extension for your HOL Light programs too.
Note that this will disable using the original OCaml VSCode plugin for the files. The default extension is `.hl`.

After this configuration, run `hol.sh` using `HOL Light: New HOL Light REPL Session` command in VSCode.
After the script is loaded, you can send one statement (or selected statement) to `hol.sh` and develop code interactively.

The README.md file as well as description in its Marketplace webpage
has more information.

### Using HOL Light Server to improve experience

Simply using the `hol.sh` in VSCode after following the above instructions has a few missing features.
First, it cannot identify whether the statement sent to `hol.sh` failed or not.
Second, it lacks error message coloring and sometimes has a broken format on its input.

You can enable these features by using a command 'Start Server' in vscode-hol-light.
This command will quickly launch HOL Light Server on the currently loaded `hol.sh`, and start
interaction mode via this server.
This does not need separately downloading the server from your side because vscode-hol-light already has it.

### Remotely connecting to `hol.sh`

The true power of HOL Light Server is that it enable you to remotely access to an already running `hol.sh`.
It removes inconvenience of restarting `hol.sh` after network connection is down.
This is very convenient if you are working remotly from a server and using SSH connection in VSCode.

In order to use this feature, clone this repo in your HOL Light directory: https://github.com/monadius/hol_server
and compile it using `make`. After this, run these statements on `hol.sh`. This will bind port 30000
to the server.

```
#directory "+threads";;
#load "unix.cma";;
#load "threads.cma";;
#directory "hol_server";;
#load "server2.cmo";;
Server2.start 30000;;
```

Now `vscode-hol-light` can connect to this server with port 30000.


## 3. Checkpointing

To avoid the loading time of `hol.sh`, you can use a checkpointing tool that will store
the loaded process as a binary.
DMTCP is recommended, and README of HOL Light has an instruction.

Once `dmtcp_restart_script.sh` is created, you can run the script to reload `hol.sh` without waiting.
You can create multiple instances of loaded HOL Light processes by starting the script with distinct
ports `-p <port number>`.

## 4. Compiling HOL Light proofs

Set the `HOLLIGHT_USE_MODULE` environment variable to 1 and recompile HOL Light using `make`.
This will create `hol_lib.cma`.
Please refer to the 'COMPILING HOL LIGHT' section of [README](https://github.com/jrh13/hol-light/blob/master/README).

```
# To compile the core module of HOL Light and use, add hol_light_module
opam install hol_light hol_light_module
```
