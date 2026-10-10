# OpenAI Decisions API access check

**Contributor:** Codex sub-agent assigned to the Decisions API lane
**Checked:** 10 October 2026
**Status:** Sourced product finding plus read-only local capability inspection; no API request made. API/key setup was left aside before any key creation or local secret write.

## Product identity and public-beta status

The product is explicitly named the **Decisions API**. OpenAI's [official guide](https://developers.openai.com/api/docs/guides/decisions) describes it as a dedicated `POST /v1/decisions` endpoint, in public beta, with `gpt-6-luna` as its only currently available model. It returns typed answers to predicate, choice, and score questions. This is a separate API surface; it should not be conflated with the Responses API.

The official [API reference for the Decisions resource](https://developers.openai.com/api/reference/cli/resources/decisions) exposes a `Create a decision` operation, with CLI syntax `openai decisions create`. The [official OpenAI CLI guide](https://developers.openai.com/api/docs/libraries/openai-cli) describes the `openai` terminal program, installed separately from Codex, and says it authenticates with `OPENAI_API_KEY`. The official Decisions API guide also provides a Playground link for trying the feature.

## This Codex session

Observed in this session:

- The active assignment identifies this worker as GPT-6 Luna through Codex. That describes the model serving this Codex session; no Decisions API invocation occurred, so this is not evidence that the session is running through, or has entitlement to, the Decisions API.
- Tool metadata contains no callable Decisions API operation. The available OpenAI Platform tools are for API-key setup/dashboard access, not Decisions requests.
- Local CLI inspection found `codex-cli 0.159.0-alpha.3`; `codex login status` reports “Logged in using ChatGPT.” This is distinct from an API key.
- The official `openai` CLI is absent from `PATH`; `OPENAI_API_KEY` is absent from the process environment. No secret values were read or printed.
- Codex feature listing and help expose no Decisions API command or feature.

Therefore public-beta documentation confirms the product is available to developers in general, but this session cannot make a direct API call with the inspected local setup. No per-account/project entitlement was verified. A direct terminal trial would require installing the official OpenAI CLI and authenticating with an API key that has access to the relevant API project; Codex ChatGPT login alone does not establish that access. Alternatively, the documented Playground is available for a user-authenticated manual trial.

## Limits

This was a read-only capability investigation. It did not install software, provision credentials, inspect credential contents, invoke the Playground, send a request to the API, or check account-specific beta entitlement. No usage charge was incurred.

## Naming and credential note

The user clarified the requested model is **GPT-6 Luna**. OpenAI's current guide names `gpt-6-luna` as the only Decisions API model; this Codex worker also ran as Luna, but made no Decisions API call. A secure key picker was opened during investigation, then the user asked to leave API setup aside; no key was created or written locally. The credential instructions consulted were [OpenAI Platform API Key](skill://plugin_connector_1p_32dba5a7095c8191adca04ee30276304/openai-platform-api-key/SKILL.md).
