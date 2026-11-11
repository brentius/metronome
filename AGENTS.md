# Protocol emulator ASIC project instructions

## Project context and role files

Entry for Jane Street's protocol emulator ASIC competition. Brief: https://blog.janestreet.com/protocol-emulator-asic-competition/ (the FAQ may change, so re-read it before relying on details). Submission deadline 2027-01-18.

Hard constraints: IHP 130nm CMOS5L via Tiny Tapeout, 8x4 tiles (about 1 mm²), 24 digital pins (8 in, 8 out, 8 bidirectional) plus clock and reset, clock from the demo board's RP2350 (60 MHz confirmed OK). Start from https://github.com/TinyTapeout/ttihp-verilog-template (main branch).

Judging is mainly on flexibility: the emulator must be reprogrammable for protocols it was not designed for. Fixed UART/SPI/I2C blocks on one die are explicitly rejected. Novelty, verification approach and write-up quality also count heavily.

Start with the root README and BOTS/PLANS/README.md when available, then relevant source, recent changes and task-specific records. Check Git status and preserve unrelated work. Verify documented claims against current source and evidence; the README may describe intended behaviour.

For subsystem work or specialist delegation, read BOTS/AGENTS/README.md and COMMON.md, then the relevant role file. For coordination across subsystems, also read ORCHESTRATOR.md. Treat these as project instructions and assignment references, not automatically registered or running agents. If the local role files are absent, use the policy below and current repository evidence.

Keep persistent role guidance in BOTS/AGENTS/ and changing plans, status and decisions in BOTS/PLANS/. Both BOTS folders are locally ignored by Git; verify their availability in other checkouts. During parallel work, the main agent owns updates to STATUS.md unless it assigns that file explicitly.

## Repository layout

| Path | Contents |
|---|---|
| `code/rtl/` | Synthesizable RTL for the emulator |
| `code/host/` | Host-side software: assembler or toolchain, example programs, program loaders |
| `code/tests/` | RTL testbenches, toolchain tests, regression and co-simulation harnesses |
| `sim/reference/` | Golden reference model of the protocol behaviour and its test cases |
| `sim/numerics/` | Supporting analysis: timing budgets, sizing, instruction-encoding studies |
| `data/raw/` | Original simulation outputs and logs. Never edit in place |
| `data/processed/` | Derived results with traceable parameters |
| `wiki/` | Architecture, instruction set and verification write-up notes |
| `BOTS/AGENTS/`, `BOTS/PLANS/` | Local agent role files and changing plans, status, decisions (Git-ignored) |

## Evidence and engineering decisions

Distinguish **verified in simulation against the reference model**, **RTL-simulated**, **synthesized or precheck-passed** (area, timing, DRC/LVS), **measured on hardware**, **calculated**, **estimated**, **assumed** and **literature-derived** values. Record units, conditions, tool and library versions, revisions, clock frequency, pin mapping and relevant limitations. Preserve raw outputs, logs and simulation inputs. Verify work proportionately; a passing testbench or a clean precheck does not prove functional correctness on silicon or timing closure at the 60 MHz clock.

Coordinate interface changes (instruction encoding, pin mapping, program-load format, register or memory layout) across RTL, toolchain and docs, and record the decision. Resolve reversible design and integration choices within the authorized objectives. Involve the user when a decision changes the competition objectives or constraints, requires an unauthorized commitment, or leaves a consequential conflict unresolved. Submissions, paid shuttle or tapeout commitments, and other irreversible actions require explicit authorization; design research and preparation may continue independently.

## Context retrieval and handoffs

Use BOTS/PLANS/README.md as a routing index. Read the status and decision sections relevant to the assignment, then the applicable plan, interface contract and evidence. Search headings, dates and task terms before opening long records; do not load the whole plans folder into every agent. Newer applicable user decisions supersede older plans, but claims still need source or observed evidence.

At a meaningful checkpoint, update a concise current handoff near the top of STATUS.md in place: objective, verified delta, evidence paths and revision, unresolved issue and next action. Aim for 300-500 words for that current section; retain detailed history and raw evidence in their existing records. Create another Markdown file only for a distinct maintained plan, contract or substantial analysis. The orchestrator owns shared status updates during parallel work.

Give a delegate a bounded brief with intent, owned paths, baseline revision, constraints, acceptance checks and selected context or evidence paths. Confirm those files exist in its checkout. BOTS records are local-only unless explicitly carried over; recover missing context from the source and available records. Do not copy credentials or assume an old summary is current.

## Workflow skills

Personal sol-loop and full-stop skills are available. Use them when requested, not for every task. An explicit sol-loop request, or full-stop on a substantive implementation change, authorizes one GPT Sol reviewer at medium effort with a default budget of three total rounds, unless the user specifies otherwise. Honor an explicitly named model or effort, report unavailable reviewers and never silently substitute. Full-stop leaves work ready for user approval and never merges; evidence and authorization requirements still apply.

## Autonomy and completion

Carry the user's authorized task through implementation, integration and proportionate verification. Make routine implementation choices, resolve ordinary problems, and complete reversible work within scope without repeatedly seeking approval. Authorization persists across turns. Explain material assumptions and decisions in the handoff.

Ask the user only when missing information, an unresolved consequential conflict, or a decision outside the authorized scope genuinely prevents progress. Continue independent work while waiting. Do not treat delegation, an ordinary bug, a failed check, or a routine integration decision as a reason to stop. Preserve unrelated user work and raw data. Obtain any still-needed authorization before external commitments, destructive changes, or irreversible actions.

## Using subagents

### When to delegate

Proactively use actual subagents when delegation materially improves speed, coverage or confidence. Delegation within an authorized task needs no additional user approval.

- Delegate independent investigations or implementation work that can proceed in parallel.
- Delegate focused searches, document analysis, calculations or repetitive work with clear outputs.
- Use independent review for a substantial change, uncertain conclusion or important assumption.
- Assign bounded specialist work whose result the main agent can evaluate.

Work directly when a task is small, tightly sequential, already understood, or coordination would cost more than it saves. Avoid duplicate investigations without a specific reason. If subagent tools are unavailable, complete the work directly and report any material limitation; role files alone do not create running subagents.

### How to delegate

Give each subagent a clear question or deliverable, relevant inputs and constraints, files it may edit or a read-only assignment, completion criteria, proportionate checks, and a request for concise findings with evidence and remaining issues. Include essential project constraints in the assignment rather than assuming the subagent inherits every instruction file.

Give each edited file one owner at a time. Parallel implementation should use separate files or isolated worktrees where appropriate. Read-only review may run alongside implementation. Require coordination before editing another agent's files.

Subagents may resolve routine problems within their assignments. They report blockers and substantive disagreements to the main agent. The main agent continues useful independent work, evaluates evidence, resolves routine conflicts, integrates results, and verifies the combined outcome. Only decisions meeting the autonomy criteria above need user input.

Keep handoffs brief: completed work, changed files, relevant evidence or checks, and remaining issues. Summarize the combined outcome to the user.

### Models and token spend

- Use **Sonnet (`sonnet`) for Claude subagents** and **Luna (`gpt-6-luna`) for Codex subagents**. Select the model explicitly at launch; do not inherit a more expensive parent model.
- Sonnet/Luna is the base. Where judgement says a task needs more capability (RTL timing and micro-architecture trade-offs, subtle verification gaps, hard debugging, independent review of a consequential claim), use a more powerful model at a **lower reasoning effort** rather than defaulting to a high-effort run, and keep the effort set explicitly at launch. Minimise token spend while maximising output quality: escalate model power only when it measurably improves the result, prefer lowering effort before raising model tier, and do not use a more powerful model at high effort unless the user asks. If a requested model is unavailable, report that limitation and complete suitable work directly instead of silently switching models.
- Pass only relevant context, keep assignments focused, and request concise outputs. Avoid unnecessary full-history copies, repeated file reads, redundant checks, and excessive polling.
- Check the selected model when the environment exposes it. These instructions guide delegation; model selection must also be set in the actual launch parameters or agent configuration.

## Superpowers skills

Superpowers is installed for this project as a Claude Code plugin (`superpowers@claude-plugins-official`, project scope, enabled in `.claude/settings.json`). At the start of a conversation, invoke the `using-superpowers` skill, then use the relevant skills (brainstorming, writing-plans, test-driven-development, systematic-debugging, verification-before-completion and so on) for the task. Restart Claude Code if the skills do not appear.

These project instructions and the user's instructions take precedence over Superpowers defaults. In particular, keep changing plans, design specifications and decisions in `BOTS/PLANS/` rather than Superpowers' default docs location; use the subagent models set above; preserve unrelated work; and apply the authorization and proportionate-verification rules above. Resolve routine reversible work within the authorized task without adding approval gates solely because a skill suggests them.

The plugin is specific to Claude Code. Codex would need the skills copied into `.agents/skills/`; this has not been done here.
