import sys

# If line at idx starts with '(*', return index after matching '*)'.
def skip_comment(line, idx):
    if line[idx:idx+2] != "(*":
        return idx

    depth = 0
    n = len(line)
    while idx < n:
        if idx + 2 <= n and line[idx:idx+2] == "(*":
            depth += 1
            idx += 2
        elif idx + 2 <= n and line[idx:idx+2] == "*)":
            assert depth > 0
            depth -= 1
            idx += 2
            if depth == 0:
                return idx
        else:
            idx += 1
    return idx

# Split line l into statements.
# One statement contains exactly one string separated by ';;'.
# If l is not closed, return None.
def tokenize_stmts(l):
  idx = 0
  prev_stmt_start = 0
  n = len(l)
  stmts = []
  while idx < n:
      if idx + 2 <= n and l[idx:idx+2] == "(*":
          idx = skip_comment(l, idx)
          continue
      elif idx + 2 <= n and l[idx:idx+2] == ";;":
          stmts.append(l[prev_stmt_start:idx + 2])
          idx = idx + 2
          prev_stmt_start = idx
      else:
          idx = idx + 1

  last_stmt = l[prev_stmt_start:].strip()
  if last_stmt != "":
      return None

  return stmts


# Returns: a list of (indentation level, string (=statement, either comment or command))
def parse_statements(raw_lines):
    results = []

    i = 0
    while i < len(raw_lines):
        l = raw_lines[i]
        if len(l.strip()) == 0:
            i = i + 1
            continue

        indent = 0
        while l[indent] == ' ':
            indent = indent + 1

        assert indent % 2 == 0, f"Indentation is wrong: '{l}' <- not multiple of two."
        l = l[indent:]

        while True:
            stmts = tokenize_stmts(l)
            if stmts == None:
                i = i + 1
                assert i < len(raw_lines), f"Lines does not end: '{l}'"
                l = l + raw_lines[i]
                continue
            for stmt in stmts:
                results.append((indent // 2, stmt))
            break

        i = i + 1

    return results

def get_beginning_comment (stmt):
    idx = skip_comment(stmt, 0)
    return stmt[0:idx]

def is_subgoal_comment(cmt):
    if len(cmt) < 3:
        return False
    if not cmt[0:3].startswith("(**"):
        return False
    cmt = cmt[3:].strip()
    if not cmt.startswith("SUBGOAL"):
        return False
    return cmt.endswith("**)")

# Returns: a list of proof tree nodes
# A proof tree node is: (main statement:string, [subtrees]:proof-tree-node list)
def make_proof_tree(stmts, matched_indent):
    assert(len(stmts) > 0)
    indent, stmt = stmts[0]
    assert indent == matched_indent, \
        f"The current statement has indentation level {indent}, which isn't {matched_indent}!"
    stmts.pop(0)
    proof_trees = [(stmt, [])]

    while len(stmts) > 0:
        indent, stmt = stmts[0]
        if indent > matched_indent:
            assert is_subgoal_comment(get_beginning_comment(stmt)), \
                f"A new subgoal must start with '(** SUBGOAL ... **)', but got '{stmt}'"
            proof_trees[-1][1].append(
                make_proof_tree(stmts, indent))
        elif is_subgoal_comment(get_beginning_comment(stmt)) or indent < matched_indent:
            # Immediately return
            return proof_trees
        else:
            proof_trees.append((stmt, []))
            stmts.pop(0)

    return proof_trees


def erase_e(stmt):
    assert ";;" in stmt, ("Does not have ';;': " + stmt)
    idx = 0
    n = len(stmt)
    e_start_idx = None
    e_end_idx = None
    stmt_e_stripped = ""

    while idx < n:
        if idx + 2 <= n and stmt[idx:idx+2] == "(*":
            idx = skip_comment(stmt, idx)
        elif idx + 2 <= n and stmt[idx:idx+2] == "e(":
            assert e_start_idx == None, ("Contains two e(): " + stmt)
            stmt_e_stripped += stmt[0:idx]
            idx = idx + 2
            e_start_idx = idx
        elif idx + 3 <= n and stmt[idx:idx+3] == ");;":
            assert e_start_idx != None, ("e hasn't started but ended with ');;': " + stmt)
            stmt_e_stripped += stmt[e_start_idx:idx]
            idx = idx + 3
            e_end_idx = idx
        else:
            idx = idx + 1

    return stmt_e_stripped + stmt[e_end_idx:]

def proof_tree_to_str(proof_tree, indent):
    space = " " * (indent * 2)

    def to_str(idx):
        stmt, subtrees = proof_tree[idx]
        stmt = erase_e(stmt)
        s = space + stmt
        if subtrees != []:
            s = s + " THENL [\n"
            for i in range(0, len(subtrees)):
                subtree = subtrees[i]
                if i > 0:
                    s = s + "\n"
                s = s + proof_tree_to_str(subtree, indent + 1)
                if i < len(subtrees) - 1:
                    s = s + ";\n"
                else:
                    s = s + "\n"
            s = s + space + "]"
        return s

    code = to_str(0)
    for idx in range(1, len(proof_tree)):
        code = code + " THEN\n"
        code = code + to_str(idx)

    return code


f = open(sys.argv[1], "r")
raw_lines = list(f.readlines())

statements = parse_statements(raw_lines)
proof_tree = make_proof_tree(statements, statements[0][0])
print("(* Converted by thenify.py *)")
print(proof_tree_to_str(proof_tree, 0))
