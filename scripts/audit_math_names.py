"""Tally long \\mathrm{...} names that survive into the rendered math, ranked by frequency.
Helps target the notation glossary at the worst offenders."""
import re, glob, collections, sys

cnt = collections.Counter()
pat = re.compile(r"\\mathrm\{([^{}]+)\}")
files = glob.glob("website/src/pages/browser/*.md") + glob.glob("website/src/pages/statements/*.md")
for f in files:
    txt = open(f, encoding="utf-8").read()
    for m in pat.findall(txt):
        cnt[m] += 1

longs = {k: v for k, v in cnt.items() if len(k.replace("\\_", "_")) >= 3}
print("distinct mathrm tokens:", len(cnt), " long(>=3):", len(longs),
      " total long occurrences:", sum(longs.values()))
top = int(sys.argv[1]) if len(sys.argv) > 1 else 60
print("--- top %d long names by frequency ---" % top)
for k, v in sorted(longs.items(), key=lambda x: -x[1])[:top]:
    print("%4d  %s" % (v, k.replace("\\_", "_")))
