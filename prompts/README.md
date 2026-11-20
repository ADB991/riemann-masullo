# Role prompts

| Role | File | Works on | Output |
|---|---|---|---|
| Integrator | [`integrator.md`](integrator.md) | the whole repository; one long-running session | merges, issues |
| Scout | [`scout.md`](scout.md) | one issue | a comment listing existing Lean and literature |
| Digester | [`digester.md`](digester.md) | one `section` issue | a pull request of statements with `sorry` |
| Prover | [`prover.md`](prover.md) | one `proof` issue | a pull request that proves or splits it |

Launch scouts, digesters and provers with the launcher, which gives each agent its own worktree,
appends the issue to the prompt, and hands in the result:

```sh
scripts/agent.sh prover 42                 # Codex by default
scripts/agent.sh prover next               # oldest unclaimed proof issue
scripts/agent.sh digester 7 --cli claude
scripts/agent.sh scout 7                   # Claude by default (needs the web)
```

Every agent also reads [`AGENTS.md`](../AGENTS.md), which holds the rules common to all roles.
