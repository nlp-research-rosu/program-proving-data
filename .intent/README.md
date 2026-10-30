# .intent

This folder is written by Intent Check (the `intent` plugin for Claude Code and Codex).
Each source file that was checked has a folder here, named by its path from the repo root:

- `INTENT.md`: the intent of the code, with its assumptions made explicit
- `SPEC.k`: K claims about the code
- `VERIFICATION.k`: the summary functions and predicates those claims rely on
- `REASONING.md`: the symbolic trace behind each claim's status
- `VERDICT.md`: the verdict and any concerns
- `meta.json`: the file hash that was checked, when, and the report link

Do not edit these files by hand; the next check of a file updates its folder.

`NOTES.md` is yours: one bullet per behaviour you have confirmed is intended. It is sent with every check and those behaviours are not raised again. Everything else here is written by Intent Check.

`.sent.log` lists every upload from this repo (paths, sizes, time, where to). It never holds file contents and is not committed.

## Not committing this folder

The folder is meant to be committed. To keep it out of git, add this line to your repo's `.gitignore`:

    .intent/

To stop checks altogether, run `/intent:off` (or set `INTENT_DISABLED=1` or `DO_NOT_TRACK=1`).
