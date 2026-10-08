# AlphaGenome access setup

Observation: 2026-10-08 01:19 UTC. This guide changes no environment configuration and performs no model request. The operator reports having an AlphaGenome API key. The attached runtime reports no configured secrets, and a presence-only process check reports ALPHAGENOME_API_KEY absent. Possession of a key is not observed runtime access or authorization for every intended use.

## Secure delivery from the phone app

Use the web or desktop configuration flow with the same ChatGPT account/workspace. The phone app can continue cloud tasks after environment preparation.

1. Open Settings > Codex Cloud > Environments. Edit the environment intended for this Research Commons task.
2. Under Environment variables > Manage, configure a personal-value requirement named ALPHAGENOME_API_KEY. The environment must request this key; a vault entry alone is not delivery.
3. Open Settings > Codex Cloud > Personal vault > Add. Select Environment variable, use ALPHAGENOME_API_KEY as Key, enter the credential only in Value, and select the intended environment under Applies to. Save.
4. Save the environment changes. For a reusable setup update, republish and start from that updated environment as required. Existing tasks keep their own saved state; do not assume the active task inherited new configuration. Continue from the saved Commons checkpoint if a new task is necessary.
5. Report only that configuration is complete. Recheck managed readiness and runtime presence without rendering, hashing, returning or committing the credential.

This adapter reads the configured variable normally. A direct environment variable is selected for the official SDK. Network secrets use proxy placeholders and have separate transport/destination requirements; this guide does not assert gRPC compatibility with that delivery mode. A secret configured only on the operator's computer or only for GitHub Actions does not automatically reach this task. Keep credentials out of chat, files, fixtures, receipts and both repositories.

Official setup references, actually inspected on 8 October 2026:

- [Cloud environments: configuration and Personal vault](https://developers.openai.com/codex/environments/cloud-environments)
- [Using Codex Cloud: web/desktop preparation, mobile continuation, existing task state](https://help.openai.com/en/articles/20001545-using-codex-cloud)

## Gates after delivery

Read-only `python3 -m molecular_apps access-check` checks package/key presence and reports pending live access. It does not authenticate a key against AlphaGenome. In the accepted CLI source, this mode constructs the default provider and does not consume the authorization flag; its unconfirmed-authorization blocker must not be interpreted as a rejected credential.

Before real inference: confirm applicable access/terms for this research, install the official SDK in an isolated recorded environment, resolve exact model and tissue/output/strand track metadata, and review a bounded execution protocol. The existing SDK client readiness timeout is not a prediction deadline. No automatic retry or unlimited quota is authorized. A process timeout cannot establish that the remote service cancelled or refunded work.

The first proposed inference uses only the checked public TERT reference. REF/A/B/AB comparisons require four sequence predictions with identical settings; one launcher process does not imply one API request. Metadata calls are additional. Keep hypothetical phase and model-prediction labels. Credentials do not change the pending scientific-validation or G-programme claim boundaries.

At the 01:19 observation above, no SDK installation, live authentication, metadata request or real model inference had run as part of this setup guide.

## Later actual SDK installation

Nolan explicitly authorized SDK installation during this resumed turn. The official SDK is now installed in the isolated runtime `/workspace/alphagenome-runtime-20261008/venv`, outside the project and original production environment. Installation used the Google DeepMind source archive at reviewed Git commit `038d253a5ca2fec46f4874f592d9ec67984cb497`, archive SHA256 `6cbcb76c347427407af9fd1293b7c41f006d641a7deeb5397c00e83df5900585`. The SDK package version is 0.9.0; Python is 3.12.14. The three installed v1 client/model/output source hashes exactly match the reviewed sources.

Actual offline checks: import and API-signature inspection PASS; `pip check` PASS; resolved package inventory recorded. API credentials were excluded from installation and import/dependency-check child processes. No client was created and no model/metadata request ran. The read-only application access check in this venv returned exit4/UNSUPPORTED with only two remaining reported blockers: runtime key absent and access/terms unconfirmed. It does not test authentication or remote reachability.

[Exact installation, dependency/import and access-check receipts](../reports/sdk-install-20261008/INSTALL-RECEIPT.json), logs, package inventory and artifact manifest are preserved privately. Run the application with `/workspace/alphagenome-runtime-20261008/venv/bin/python` to use this installation. The ordinary Python environment is unchanged. Runtime installation is not a reusable cloud-environment publication; a different task must recreate the setup from the saved pins/receipts as needed. The bounded live launcher and live/scientific gates remain separate.

Nolan subsequently deferred the API work to prioritize general G-programme proofs and Lean. Stop new access/inference work until that priority changes. The new standalone launcher draft and its 25 passing synthetic tests are preserved with source review incomplete and live testing pending; they do not alter accepted CLI or production behavior. No credential was supplied to this task and no live call ran.
