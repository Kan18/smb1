"""Rewrite the end states of `NAME_call` theorems from `sym_summary NAME end state: …` log lines.

usage: apply_end_states.py FILE.lean BUILD_LOG
For each logged summary NAME, the theorem `NAME_call` in FILE gets the logged end state in its
`((CPU.runTo stop (j + m)).run ⟨…⟩).2` and an existential prefix `∃ j p' …` naming exactly the
fields the summary leaves undefined (`a'`, `x'`, `y'`, `s'`, `c'`).
"""
import re, sys

path, log = sys.argv[1], sys.argv[2]
text = open(log, encoding="utf-8").read()
# A message may wrap; join each logged end state up to its closing `⟩`.
ends = {}
for m in re.finditer(r"sym_summary (\w+) end state: (⟨⟨.*?⟩, .*?⟩)\s*$", text, re.S | re.M):
    ends[m.group(1)] = " ".join(m.group(2).split())
src = open(path, encoding="utf-8").read()
for name, st in ends.items():
    i = src.find(f"theorem {name}_call")
    if i < 0:
        continue
    j = src.index(":= by", i)
    stmt = src[i:j]
    a = stmt.index("((CPU.runTo stop (j + m)).run ") + len("((CPU.runTo stop (j + m)).run ")
    b = stmt.index(").2 ∧", a)
    exist = ["j", "p'"] + [v for v in ["a'", "x'", "y'", "s'", "c'"] if v in st.replace("p'", "")]
    stmt2 = stmt[:a] + st + stmt[b:]
    stmt2 = re.sub(r"∃ j[^,]*,", "∃ " + " ".join(exist) + ",", stmt2, count=1)
    src = src[:i] + stmt2 + src[j:]
    print("updated", name)
open(path, "w", encoding="utf-8").write(src)
