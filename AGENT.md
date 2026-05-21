# AGENT.md

Repository collaboration guide for humans and coding agents working in this repo.

This file is intentionally practical. It explains how to enter the repo, where to look first, how to validate changes, how to prepare a PR, and how to deploy without fighting the current workflow.

## Purpose

- Keep contributors aligned on repo-specific workflow.
- Reduce repeated discovery when continuing prior work.
- Make PRs, validation, and deploy steps predictable.

## First Principles

This document is the repo-facing summary of the local Codex workflow. Contributors should not need `CODEX.md` or local-only handoff files in order to collaborate safely.

Start from these rules:

- Check the current worktree before editing. Do not assume a clean tree.
- Continue in-progress work instead of rediscovering the repo from scratch when obvious local context exists.
- Preserve existing UI structure unless the task explicitly calls for redesign.
- Treat shared Station UI changes as potentially Viewer-affecting until verified otherwise.
- Keep secrets, passwords, tokens, and private credentials out of tracked repo files.

Optional local context:

- Some contributors may have a local `_codex_context/` directory for handoff notes and deploy history.
- That directory is not part of the repo contract and should be treated as local-only supplemental context.
- Do not make repository workflow depend on `_codex_context/` being present.

## Repo Shape

High-level layout:

- `station_edition/`: primary base-station product and runtime.
- `viewer/`: standalone viewer / node-center service.
- `frontend/`: local frontend build tooling; currently used for the shared home Vue bundle.
- `portable_edition/`: intentionally WIP / limited scope in the current workflow.
- `pytools/`: build helpers.
- `tools/`: local helper scripts, including Pi deployment helpers.
- `tests/`: test assets and repo tests.

Key current architecture facts:

- Root `run.py` is a compatibility wrapper.
- Shared Station UI template lives in `station_edition/light_rid/web_server.py`.
- Viewer reuses Station UI structure through `viewer/station_ui.py` and shared CSS/script helpers in `viewer/ui_common.py`.
- The shared home page has a Vue bridge bundle at `/assets/vue/rid-home.js`.

## Working Rules

- Do not restart discovery if there is already in-progress work. Inspect current diffs first, then any available local handoff notes if present.
- Preserve the existing UI structure unless the task explicitly asks for a redesign.
- If changing the shared Station template, assume Viewer may inherit the change and verify both surfaces.
- If changing Viewer-only behavior, avoid deploying it to the Pi unless explicitly requested.
- Treat `tools/pi_tools.py` as a local/private helper. Do not include it in normal review scope unless the task is specifically about deployment tooling or deploy flow.
- Prefer small, additive changes over wide rewrites when patching shared UI or parser logic.

## Current Workflow Notes

Current repo workflow, summarized:

- `station_edition/` is the main product runtime.
- `viewer/` is a separate local-only viewer / node-center service unless explicitly included in deploy scope.
- Root `run.py` is compatibility glue, not the primary implementation surface.
- Shared Station UI template and much of the shared browser logic live in `station_edition/light_rid/web_server.py`.
- Viewer inherits shared UI structure through `viewer/station_ui.py` and `viewer/ui_common.py`.
- The shared home page currently uses a Vue bundle at `station_edition/light_rid/assets/vue/rid-home.js`, built from `frontend/`.

Pi deploy policy versus reality:

- Preferred long-term direction is compiled-artifact deployment.
- Practical day-to-day reality may still require `python tools/pi_tools.py sync` source deployment when compiled deployment is blocked in the active environment.

Practical rule:

- Use the currently validated path for the target environment unless the task explicitly asks to switch deployment mode.
- If changing deployment mode, say so clearly in the PR or handoff.

## Common Validation

Pick the smallest validation set that honestly covers the change. Typical commands:

### Python

```bash
python -m py_compile station_edition\light_rid\web_server.py
python -m py_compile viewer\server.py viewer\station_ui.py viewer\settings_ui.py viewer\nodes_ui.py viewer\ui_common.py
```

### Shared home frontend bundle

```bash
cd frontend
npm run build:rid-home
cd ..
node --check station_edition\light_rid\assets\vue\rid-home.js
```

### Diff hygiene

```bash
git diff --check
```

### Local HTTP smoke

Examples:

- Viewer: `http://127.0.0.1:4700/`
- Viewer settings: `http://127.0.0.1:4700/settings`
- Station default runtime: usually `http://127.0.0.1:4600/` when running locally

If changing browser behavior or shared UI:

- Verify both Station and Viewer when the change is inherited.

## Deploy / Sync

Typical commands:

```bash
python tools/pi_tools.py status
python tools/pi_tools.py logs --lines 120
python tools/pi_tools.py sync
python tools/pi_tools.py binary-sync
```

Current safe deploy loop:

1. Validate locally.
2. Run the currently approved sync path.
3. Run `python tools/pi_tools.py status`.
4. Run `python tools/pi_tools.py logs --lines 100` or similar.
5. Confirm service command line, HTTP/WS startup, and scan interface/channel state.
6. If you maintain local handoff notes, update them after the deploy.

## PR Guidance

A good PR for this repo should include:

- What changed in product terms, not just file terms.
- Whether the change is Station-only, Viewer-only, or shared.
- Any behavior inherited through `station_edition/light_rid/web_server.py`.
- Validation commands actually run.
- Whether Pi sync/deploy was performed.
- Any remaining risk, compatibility assumption, or intentionally deferred item.

Recommended PR structure:

1. Summary
2. Scope
3. Validation
4. Deploy status
5. Risks / follow-ups

If deployment was not run, say so explicitly.

If the work touched local-only helpers or local handoff notes, separate that from product code in the description.

## Handoff Expectations

When ending a non-trivial task, capture enough information for the next contributor to continue safely.

If you maintain local handoff state outside Git, update it when project state changed.

Minimum handoff content:

- files touched
- validation run
- deploy status
- exact runtime/deploy command when relevant
- known unresolved risks or assumptions

## UI-Specific Reminders

- Shared Station template changes often affect Viewer automatically.
- Shared settings styling is extracted by `viewer/ui_common.py` from the Station settings page.
- The current iCloud-style restyle is broad and CSS-heavy in `station_edition/light_rid/web_server.py`; inspect there first if visual regressions appear.
- The Station network binding editor now lives inline as `#network-bind-module` inside the settings capture card and is default-collapsed.

## Do Not Forget

- Check for existing uncommitted work before editing.
- Keep README and README.zh-CN aligned when changing user-facing docs.
- Do not assume Viewer should be deployed with Station changes.
- Prefer continuing the current validated deployment path over inventing a new one mid-task.
