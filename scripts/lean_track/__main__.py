"""lean_track CLI.

  python -m lean_track report -c tracks/gr.toml [--no-prober] [-o reports/gr]
  python -m lean_track extract -c tracks/gr.toml          # raw Lean facts only
  python -m lean_track latex -c tracks/gr.toml [--string] [-o reports/gr/statements.tex]
  python -m lean_track diff --old A/agent_summary.json --new B/agent_summary.json
"""
import argparse
import json
import pathlib
import sys

from . import latex_tree, latexify, probe, report


def _names_and_roles(cfg):
    names = [t["name"] for t in cfg["theorems"]]
    roles = {t["name"]: t.get("role") for t in cfg["theorems"]}
    return names, roles


def cmd_report(args):
    cfg = probe.load_config(args.config)
    names, roles = _names_and_roles(cfg)
    ex = probe.extract(names, cfg)
    for t in ex:
        t["role"] = roles.get(t["name"])
    pr = [] if args.no_prober else probe.discharge(names, cfg)
    merged = report.apply_curation(report.analyze(ex, pr, cfg), cfg)

    outdir = pathlib.Path(args.out) if args.out else (probe.REPO / "reports" / cfg["track"]["id"])
    outdir.mkdir(parents=True, exist_ok=True)
    (outdir / "facts.curated.json").write_text(json.dumps(merged, indent=2, ensure_ascii=False),
                                               encoding="utf-8")
    summ = report.agent_summary(merged, cfg)
    (outdir / "agent_summary.json").write_text(json.dumps(summ, indent=2, ensure_ascii=False),
                                               encoding="utf-8")
    (outdir / "report.machine.md").write_text(report.render_markdown(merged, cfg), encoding="utf-8")

    tot = summ["totals"]
    surf = sum(len(t["surface"]) for t in summ["theorems"])
    print(f"{cfg['track']['id']}: {tot['present']}/{tot['theorems']} present · "
          f"policy-clean={'Y' if tot['all_policy_clean'] else 'N'} · "
          f"project-axioms {len(tot['project_axioms'])} · surface-items {surf} · "
          f"vacuous {len(tot['vacuous_contexts'])}  →  {outdir.relative_to(probe.REPO)}/")
    return 0 if (tot["all_policy_clean"] and not tot["vacuous_contexts"]) else 1


def cmd_extract(args):
    cfg = probe.load_config(args.config)
    names, _ = _names_and_roles(cfg)
    ex = probe.extract(names, cfg)
    outdir = pathlib.Path(args.out) if args.out else (probe.REPO / "reports" / cfg["track"]["id"])
    outdir.mkdir(parents=True, exist_ok=True)
    (outdir / "facts.raw.json").write_text(json.dumps(ex, indent=2, ensure_ascii=False),
                                           encoding="utf-8")
    print(f"extract → {(outdir / 'facts.raw.json').relative_to(probe.REPO)}")
    return 0


def cmd_latex(args):
    cfg = probe.load_config(args.config)
    names, roles = _names_and_roles(cfg)
    notation = (cfg.get("latex", {}) or {}).get("notation", {})
    use_tree = not args.string          # AST renderer is the default
    if use_tree:                        # render from the delaborated Syntax tree
        data = probe.syntax_trees(names, cfg)
        doc = latex_tree.render_document(data, cfg, notation=notation, roles=roles)
    else:                               # render from the pretty-printed string
        data = probe.extract(names, cfg)
        doc = latexify.render_document(data, cfg, notation=notation, roles=roles)
    out = (pathlib.Path(args.out) if args.out
           else probe.REPO / "reports" / cfg["track"]["id"] / "statements.tex")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(doc, encoding="utf-8")
    present = sum(1 for t in data if t.get("present"))
    mode = "tree" if use_tree else "string"
    try:
        shown = out.resolve().relative_to(probe.REPO)
    except ValueError:
        shown = out
    msg = f"latex ({mode}) → {shown}  ({present}/{len(data)} statements)"
    if latexify._UNMAPPED:
        msg += "  · unmapped glyphs dropped: " + " ".join(sorted(latexify._UNMAPPED))
    print(msg)
    return 0


def cmd_diff(args):
    old = json.loads(pathlib.Path(args.old).read_text(encoding="utf-8"))
    new = json.loads(pathlib.Path(args.new).read_text(encoding="utf-8"))
    sys.stdout.write(report.diff(old, new))
    return 0


def main(argv=None):
    p = argparse.ArgumentParser(prog="lean_track")
    sub = p.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("report"); r.add_argument("-c", "--config", required=True)
    r.add_argument("-o", "--out"); r.add_argument("--no-prober", action="store_true")
    r.set_defaults(fn=cmd_report)
    e = sub.add_parser("extract"); e.add_argument("-c", "--config", required=True)
    e.add_argument("-o", "--out"); e.set_defaults(fn=cmd_extract)
    lx = sub.add_parser("latex"); lx.add_argument("-c", "--config", required=True)
    lx.add_argument("-o", "--out")
    lx.add_argument("--string", action="store_true",
                    help="render from the pretty-printed string (legacy) instead of the "
                         "default delaborated Syntax tree (AST)")
    lx.set_defaults(fn=cmd_latex)
    d = sub.add_parser("diff"); d.add_argument("--old", required=True); d.add_argument("--new", required=True)
    d.set_defaults(fn=cmd_diff)
    args = p.parse_args(argv)
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())
