"""Deterministic analysis [D] + version-controlled curation [C] + render + diff.

Honesty: [L] Lean fact · [P] Lean-checked prober · [D] deterministic post-processing ·
[C:rule] curation rule · [AI] AI judgment (never emitted here — the skill adds those).
"""
import json
import re
from datetime import datetime, timezone

from . import probe


# ---------- analysis [D] (merges extractor [L] + prober [P]) ----------
def analyze(ex, pr, cfg):
    prmap = {t["name"]: t for t in pr}
    order = [t["name"] for t in ex]
    # all conclusion pretty-prints in the spine (for "covered by a spine conclusion")
    concl_pps = {t["concl"]["pp"] for t in ex if t.get("present") and t.get("concl")}
    # count each hypothesis type across the spine (shared/dup detection)
    type_count = {}
    for t in ex:
        if not t.get("present"):
            continue
        for b in t["binders"]:
            if b["kind"] == "prop":
                type_count[b["type"]] = type_count.get(b["type"], 0) + 1
            for p in b.get("packedProps", []):
                type_count[p["type"]] = type_count.get(p["type"], 0) + 1

    allowed = set(cfg["project"]["allowed_axioms"])
    out = []
    for t in ex:
        d = dict(t)
        if not t.get("present"):
            out.append(d)
            continue
        axs = t.get("axioms", [])
        d["axiom_free_literal"] = (len(axs) == 0)
        d["policy_clean"] = all(a in allowed for a in axs)
        d["nonstandard_axioms"] = [a for a in axs if a not in allowed]
        prt = prmap.get(t["name"], {})
        d["falseProvable"] = bool(prt.get("falseProvable", False))
        disch = {h["name"]: h for h in prt.get("hyps", [])}
        unused = set(t.get("proofUnusedBinders", []))

        # annotate each Prop binder with a derived status
        for b in d["binders"]:
            if b["kind"] != "prop":
                continue
            h = disch.get(b["name"], {})
            b["dischargeable"] = bool(h.get("dischargeable", False))  # [P]
            b["shared"] = type_count.get(b["type"], 0) > 1            # [D]
            covered = b["type"] in concl_pps                          # [D] approx (pp match)
            if b["type"] == "True":
                b["status"] = "trivial_true"
            elif b["dischargeable"]:
                b["status"] = "auto_dischargeable"   # removable
            elif b["name"] in unused:
                b["status"] = "proof_unused"         # removable (proof never uses it)
            elif covered:
                b["status"] = "covered_by_spine"     # not-new
            else:
                b["status"] = "surface"              # genuine assumption surface (by this analysis)
        out.append(d)
    return out


def _surface_items(t):
    """The genuine assumption surface of one theorem: surface Prop binders + ALL packed Props
    (packed assumptions are never auto-tested), each as (name, type)."""
    items = []
    for b in t.get("binders", []):
        if b["kind"] == "prop" and b.get("status") == "surface":
            items.append((b["name"], b["type"]))
        for p in b.get("packedProps", []):
            items.append((f"{b['name']}.{p['field']}", p["type"]))
    return items


# ---------- curation [C] (versioned TOML rules) ----------
def apply_curation(merged, cfg):
    rules = cfg.get("category_rules", [])
    def label_for(name, typ):
        for i, r in enumerate(rules):
            nre, tre = r.get("name_regex"), r.get("type_regex")
            if nre and not re.search(nre, name):
                continue
            if tre and not re.search(tre, typ):
                continue
            return {"category": r.get("category", "?"),
                    "label": r.get("label", r.get("category", "?")),
                    "rule": r.get("id", f"rule#{i}")}
        return None
    for t in merged:
        if not t.get("present"):
            continue
        for b in t.get("binders", []):
            if b["kind"] == "prop":
                b["curation"] = label_for(b["name"], b["type"])
            for p in b.get("packedProps", []):
                p["curation"] = label_for(f"{b['name']}.{p['field']}", p["type"])
    return merged


# ---------- render ----------
def _meta(cfg):
    return {"now": datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
            "git": probe.git_rev(),
            "title": cfg["track"]["title"], "subtitle": cfg["track"].get("subtitle", ""),
            "id": cfg["track"]["id"]}


def _fence(s):
    return "```\n" + s.rstrip() + "\n```"


def render_markdown(merged, cfg):
    m = _meta(cfg)
    present = [t for t in merged if t.get("present")]
    missing = [t for t in merged if not t.get("present")]
    proj_ax = sorted({a for t in present for a in t.get("nonstandard_axioms", [])})
    all_policy_clean = all(t.get("policy_clean") for t in present) and not missing
    all_literal_free = all(t.get("axiom_free_literal") for t in present)
    capstones = [t for t in present if t.get("role") == "capstone"] or present[:1]

    L = [f"# Track state — {m['title']}", f"*{m['subtitle']}*",
         f"\n_Generated {m['now']} · git `{m['git']}` · {len(merged)} theorems · "
         f"tool lean_track_ · provenance: [L]=Lean fact [P]=Lean-checked prober [D]=derived [C]=curation_\n"]

    # axioms
    L += ["## Axiom status  [L]",
          f"- Project-specific (non-standard) axioms: **{len(proj_ax)}**"
          + ("" if not proj_ax else f" — {', '.join(proj_ax)}"),
          f"- All policy-clean (axioms ⊆ allowed `{', '.join(cfg['project']['allowed_axioms'])}`): "
          f"**{'YES' if all_policy_clean else 'NO'}**",
          f"- All *literally* axiom-free (no axioms at all): **{'YES' if all_literal_free else 'NO'}**"]
    if missing:
        L.append(f"- ⚠️ Missing from library: {', '.join('`'+t['name']+'`' for t in missing)}")
    if any(t.get("falseProvable") for t in present):
        bad = [t['name'] for t in present if t.get('falseProvable')]
        L.append(f"- 🚨 **VACUITY**: `False` provable from the binders of: {', '.join('`'+b+'`' for b in bad)} "
                 f"(context inconsistent — discharges there are suspect)  [P]")
    L.append("")

    # assumption surface of the capstone(s) — the headline
    L.append("## Assumption surface (capstone)  [P]/[D]")
    for c in capstones:
        items = _surface_items(c)
        # dedup by type
        seen, ded = set(), []
        for nm, ty in items:
            if ty not in seen:
                seen.add(ty); ded.append((nm, ty))
        L.append(f"\n**`{c['name']}`** — {len(items)} surface items "
                 f"({len(ded)} distinct after dedup; conclusion: `{c['concl']['pp'][:90]}`):")
        for nm, ty in ded:
            cur = None
            for b in c["binders"]:
                if b["kind"] == "prop" and b["name"] == nm:
                    cur = b.get("curation")
                for p in b.get("packedProps", []):
                    if f"{b['name']}.{p['field']}" == nm:
                        cur = p.get("curation")
            tag = f" · **{cur['label']}** [C:{cur['rule']}]" if cur else ""
            L.append(f"  - `{nm}` : `{ty}`{tag}")

    # curated piles
    rules = cfg.get("category_rules", [])
    if rules:
        L.append("\n## Curated piles  [C] *(author labels — NOT a Lean fact)*")
        piles = {}
        for t in present:
            for b in t.get("binders", []):
                cur = b.get("curation")
                if b["kind"] == "prop" and cur:
                    piles.setdefault(cur["label"], set()).add(b["type"])
                for p in b.get("packedProps", []):
                    if p.get("curation"):
                        piles.setdefault(p["curation"]["label"], set()).add(p["type"])
        for lab in sorted(piles):
            L.append(f"\n**{lab}** ({len(piles[lab])} distinct)")
            for ty in sorted(piles[lab]):
                L.append(f"  - `{ty}`")
        uncl = sorted({b["type"] for t in present for b in t.get("binders", [])
                       if b["kind"] == "prop" and not b.get("curation") and b.get("status") == "surface"})
        if uncl:
            L.append(f"\n**(uncategorised surface hypotheses — {len(uncl)})** *(no rule matched)*")
            for ty in uncl:
                L.append(f"  - `{ty}`")

    # per-theorem dump
    L.append("\n## Per-theorem facts  [L]/[P]/[D]")
    for t in merged:
        L.append(f"\n### `{t['name']}`" + (f"  ·  *{t['role']}*" if t.get("role") else ""))
        if not t.get("present"):
            L.append("**MISSING FROM LIBRARY.**"); continue
        flags = []
        flags.append("literal-axiom-free" if t["axiom_free_literal"] else
                     ("policy-clean" if t["policy_clean"] else "⚠ axioms: " + ", ".join(t["nonstandard_axioms"])))
        if t["concl"]["isFalse"]:
            flags.append("**no-go (concl = False)**")
        if t.get("falseProvable"):
            flags.append("🚨 vacuous-context")
        if t.get("proofUsesSpine"):
            flags.append("uses-spine: " + ", ".join("`"+x.split('.')[-1]+"`" for x in t["proofUsesSpine"]))
        L.append("- " + " · ".join(flags) + f" · kind={t['kind']}  [L]")
        L.append("- **conclusion:**"); L.append(_fence(t["concl"]["pp"]))
        props = [b for b in t["binders"] if b["kind"] == "prop"]
        data = [b for b in t["binders"] if b["kind"] == "data"]
        L.append(f"- **hypotheses ({len(props)})** — name : status [P]/[D]:")
        if props:
            L.append(_fence("\n".join(
                f"{i+1}. {b['name']} [{b['status']}] : {b['type']}" for i, b in enumerate(props))))
        else:
            L.append("  *(none)*")
        packed = [(b["name"], p) for b in data for p in b.get("packedProps", [])]
        if packed:
            L.append(f"- **packed Prop fields (hidden assumptions inside data structures, {len(packed)})  [L]:**")
            L.append(_fence("\n".join(f"{bn}.{p['field']} : {p['type']}" for bn, p in packed)))
        L.append(f"- **data binders ({len(data)}):** "
                 + (", ".join(f"`{b['name']}`" for b in data) if data else "*(none)*"))
    return "\n".join(L) + "\n"


def agent_summary(merged, cfg):
    """Compact JSON the AI skill consumes (so it reads structured facts, not scraped Markdown)."""
    present = [t for t in merged if t.get("present")]
    return {
        "track": cfg["track"]["id"], "title": cfg["track"]["title"],
        "generated": datetime.now(timezone.utc).isoformat(), "git": probe.git_rev(),
        "totals": {
            "theorems": len(merged), "present": len(present),
            "project_axioms": sorted({a for t in present for a in t.get("nonstandard_axioms", [])}),
            "all_policy_clean": all(t.get("policy_clean") for t in present) and len(present) == len(merged),
            "vacuous_contexts": [t["name"] for t in present if t.get("falseProvable")],
        },
        "theorems": [{
            "name": t["name"], "present": t.get("present", False), "role": t.get("role"),
            "kind": t.get("kind"), "axiom_free_literal": t.get("axiom_free_literal"),
            "policy_clean": t.get("policy_clean"), "isFalse": t.get("concl", {}).get("isFalse"),
            "falseProvable": t.get("falseProvable"),
            "n_prop": sum(1 for b in t.get("binders", []) if b.get("kind") == "prop"),
            "n_packed": sum(len(b.get("packedProps", [])) for b in t.get("binders", [])),
            "uses_spine": t.get("proofUsesSpine", []),
            "surface": [{"name": n, "type": ty, "curation": _cur(t, n)} for n, ty in _surface_items(t)],
            "dischargeable": [b["name"] for b in t.get("binders", [])
                              if b.get("kind") == "prop" and b.get("dischargeable")],
        } for t in merged],
    }


def _cur(t, name):
    for b in t.get("binders", []):
        if b["kind"] == "prop" and b["name"] == name:
            return (b.get("curation") or {}).get("label")
        for p in b.get("packedProps", []):
            if f"{b['name']}.{p['field']}" == name:
                return (p.get("curation") or {}).get("label")
    return None


# ---------- diff ----------
def diff(old_summary, new_summary):
    def surf(s):
        return {t["name"]: {x["type"] for x in t.get("surface", [])} for t in s.get("theorems", [])}
    o, n = surf(old_summary), surf(new_summary)
    lines = ["# lean_track diff",
             f"old git {old_summary.get('git')} → new git {new_summary.get('git')}\n"]
    oa, na = set(old_summary["totals"]["project_axioms"]), set(new_summary["totals"]["project_axioms"])
    if na - oa:
        lines.append(f"🚨 NEW project axioms: {sorted(na - oa)}")
    if oa - na:
        lines.append(f"✓ retired project axioms: {sorted(oa - na)}")
    for name in sorted(set(o) | set(n)):
        added = n.get(name, set()) - o.get(name, set())
        removed = o.get(name, set()) - n.get(name, set())
        if added or removed:
            lines.append(f"\n## `{name}`")
            for x in sorted(removed):
                lines.append(f"  - discharged/removed: `{x}`")
            for x in sorted(added):
                lines.append(f"  + new assumption: `{x}`")
    if len(lines) <= 2:
        lines.append("(no change in axioms or assumption surface)")
    return "\n".join(lines) + "\n"
