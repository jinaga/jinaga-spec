---
name: file-divergence
description: "Turn a divergence between jinaga-spec and jinaga.js, jinaga-server or jinaga.net into an issue draft: search for an existing issue, build the smallest repro, link the theorem, and hold the draft for the user's approval. Use when docs/findings.md gains a new implementation bug, or when the user asks to file what a proof found. Never files without explicit approval."
---

# Filing a divergence

Findings that live only in `docs/findings.md` don't get fixed. Filing twice
wastes the maintainers' time (the fact_id commit-order problem is already
jinaga/jinaga-server#203 and #207). This skill produces drafts; the user decides
what gets filed.

## Steps

1. **Pick the repository.** `jinaga/jinaga.js` for specification code
   (`src/specification/`), `jinaga/jinaga-server` for SQL and the replicator,
   `jinaga/jinaga.net` for the .NET port. If both jinaga.js and jinaga-server
   misbehave, decide which one is the cause (e.g. jinaga.js builds feeds that
   declare a label twice; jinaga-server's SQL throws on them) and file there,
   mentioning the other.

2. **Search before drafting**, open and closed:

   ```bash
   gh issue list -R jinaga/<repo> --state all --search "<function name> <symptom>" --limit 20
   gh pr list -R jinaga/<repo> --state all --search "<function name>" --limit 10
   ```

   In a Claude Code cloud session `gh issue` and `gh pr` fail: the GitHub proxy
   blocks GraphQL. Use the REST search instead, which covers issues and PRs
   (the target repository must be attached to the session, or the proxy
   answers 403):

   ```bash
   gh api -X GET search/issues -f q='repo:jinaga/<repo> <function name> <symptom>' \
     --jq '.items[] | "#\(.number) \(.state) \(if .pull_request then "PR" else "issue" end) \(.title)"'
   ```

   Search by function name and by error text. If a match exists, draft a
   comment that adds the new repro instead of a new issue.

3. **Make the smallest repro.** Start from the vector that exposed it and cut
   matches, conditions and components until it stops failing; keep the last
   one that fails. Give it as Jinaga specification text, and as a script using
   the `jinaga-conformance` skill's `probe.mts` that prints the actual output.

4. **Write the draft** to the scratchpad as `issue-<repo>-<slug>.md`:

   ```markdown
   ## Summary
   <one sentence: what the function does wrong, on which input>

   ## Repro
   <specification text> 
   <command and its actual output>

   ## Expected
   <what it should return, and why: the theorem (name, file) and the vector
   in jinaga-spec that pins it>

   ## Where
   <file:line in the repo, and the smallest change that would fix it, if known>
   ```

   No internal paths, scratchpad paths or session details in the body.

5. **Hand the drafts back to the user** with the search results for each, and
   ask which to file. After they approve one, file it with
   `gh issue create -R jinaga/<repo> --title ... --body-file ...` (in a cloud
   session: `gh api repos/jinaga/<repo>/issues -f title=... -F body=@<file>`), then put
   the issue number into `docs/findings.md` next to the finding.
