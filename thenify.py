import sys

print(sys.argv[1])

f = open(sys.argv[1], "r")
# A list of (indentation level, is it a new start?, is it a comment? actual line)
lines = []
is_first = True

for l in f.readlines():
    if len(l.strip()) == 0:
        continue

    idx = 0
    subtactic_start = is_first
    while l[idx] == ' ':
        idx = idx + 1
    if l[idx] == '-' and l[idx + 1] == ' ':
        subtactic_start = True
        idx += 2
    assert idx % 2 == 0, f"Indentation is wrong: '{f}' <- not multiple of two."
    l = l[idx:].strip()
    is_comment = l[0:2] == "(*" and l[-2:] == "*)"
    assert (is_comment or (l.startswith("e(") and l.endswith(");;"))), \
        f"This line isn't 'e(..)' form: '{l}'"
    if not is_comment:
        l = l[len("e("):-len(");;")]
    lines.append((idx / 2, subtactic_start, is_comment, l))
    is_first = False

def thenify(lines):
    assert(len(lines) > 0)
    indent, new_start, is_comment, line0 = lines[0]
    assert(new_start)
    lines.pop(0)
    tactics = [(is_comment, line0)]

    while len(lines) > 0:
        next_indent, next_new_start, next_is_comment, next_line = lines[0]
        if next_new_start:
            if indent >= next_indent:
                break
            assert indent + 1 == next_indent, f"indent + 1 = {indent} + 1 != next_indent = {next_indent}; line: {next_line}"
            new_tactics = thenify(lines)
            tactics.append(new_tactics)
        else:
            assert indent == next_indent
            lines.pop(0)
            tactics.append((next_is_comment, next_line))

    return tactics

tactics = thenify(lines)
def tostr(tactics, indent):
    space = " " * (indent * 2)
    is_comment, tactic_str = tactics[0]
    s = space + tactic_str
    idx = 1
    def all_comments(tactics_subseq):
      return all(map(lambda itm: itm[0], tactics_subseq))

    while idx < len(tactics):
        if isinstance(tactics[idx], list):
            break

        if not is_comment and not all_comments(tactics[idx:]):
            s = s + " THEN\n"
        else:
            s = s + "\n"
        next_is_comment, next_tactic_str = tactics[idx]
        s = s + space + next_tactic_str
        is_comment = next_is_comment
        idx += 1
    if idx != len(tactics):
        s = s + " THENL [\n"
        ss = map(lambda l: tostr(l, indent + 1), tactics[idx:])
        s = s + ";\n".join(ss)
        s = s + "]"
    return s

print(tostr(tactics, 1))
