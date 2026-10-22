/** Explicit full-context variant: at most1MiB authored source and300s
 * document deadline. The existing protocol, versions, diagnostics and audit
 * acceptance remain unchanged. Native/controller admission is separate. */
/** Source-owned capture variant of online_lean.mjs.
 * Same service, source/deadline/version/barrier/audit checks. Distinct diagnostics
 * are never erased; protocol progress has a separate bounded transport budget.
 * Does not run native Lean, change the original client or bind a Linux writer.
 */
/** Finite client of the existing public Lean web service, never a local compiler.
 * Source: leanprover-community/lean4web server/index.mjs protocol.
 * Keep all runtime observations in RAM until the existing featurectl seals them.
 * This checks a virtual document; it does not create a Lake/object certificate.
 */
import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';

const HOST = 'https://live.lean-lang.org';
const PROJECT = 'mathlib-stable';
const TOOLCHAIN = 'leanprover/lean4:v4.35.0';
const MATHLIB = '56a005855ea17e0b0958f73ec801ae140b0a1679';
const sha = x => createHash('sha256').update(x).digest('hex');
const SENTINEL = 'LEAN_E2E_DOCUMENT_FINISHED_20261021';
const STANDARDS = new Set(['propext', 'Classical.choice', 'Quot.sound']);

async function metadata() {
  const raw = await Promise.all([
    fetch(`${HOST}/api/toolchain/${PROJECT}/lean-toolchain`, { signal: AbortSignal.timeout(15000) }).then(async r => { if (!r.ok) throw Error('TOOLCHAIN_HTTP'); return r.text(); }),
    fetch(`${HOST}/api/manifest/${PROJECT}/lake-manifest.json`, { signal: AbortSignal.timeout(15000) }).then(async r => { if (!r.ok) throw Error('MANIFEST_HTTP'); return r.text(); }),
  ]);
  const manifest = JSON.parse(raw[1]);
  if (raw[0].trim() !== TOOLCHAIN || manifest.packages.find(x => x.name === 'mathlib')?.rev !== MATHLIB) throw Error('HOST_VERSION_CHANGED');
  return { toolchain: raw[0].trim(), manifest_sha256: sha(raw[1]), mathlib_revision: MATHLIB };
}

async function elaborate(source, audits, timeoutMs = 300000) {
  if (Buffer.byteLength(source) > 1048576 || !audits.length || audits.some(x => !/^[A-Za-z_][A-Za-z_0-9'.]*$/.test(x))) throw Error('SOURCE_OR_AUDIT_SCOPE');
  if (source.includes(SENTINEL)) throw Error('RESERVED_SENTINEL');
  const before = await metadata();
  const text = source + '\n' + audits.map(n => `set_option pp.universes true in\nset_option pp.explicit true in\n#check ${n}\n#print axioms ${n}`).join('\n') + `\n#eval "${SENTINEL}"\n`;
  const uri = 'file:///Main.lean';
  const observations = [], diagnosticKeys = new Set();
  let messageBytes = 0, retainedBytes = 0, receivedMessages = 0;
  let progressMessages = 0, duplicateDiagnostics = 0, lastProgress = null;
  let initialized = false, sawSentinel = false;
  const captureStats = () => ({ received_bytes: messageBytes, retained_bytes: retainedBytes,
    received_messages: receivedMessages, progress_messages: progressMessages,
    duplicate_diagnostics: duplicateDiagnostics, last_progress: lastProgress,
    limits: { received_bytes: 32 * 1024 * 1024, retained_bytes: 4 * 1024 * 1024,
      frame_bytes: 4 * 1024 * 1024, retained_observations: 2048 },
    policy: 'Union of every distinct diagnostic; cumulative duplicates coalesced; progress counted with latest state in RAM.' });
  let timer, ws;
  const result = await new Promise((resolve, reject) => {
    let finished = false;
    const finish = (err, value) => {
      if (finished) return;
      finished = true;
      clearTimeout(timer);
      if (ws) ws.close();
      if (err) reject(Object.assign(err, { observations, capture_stats: captureStats() }));
      else resolve({ ...value, capture_stats: captureStats() });
    };
    timer = setTimeout(() => finish(Error('REMOTE_DEADLINE')), timeoutMs);
    ws = new WebSocket(`wss://live.lean-lang.org/websocket/${PROJECT}`);
    const send = value => ws.send(JSON.stringify({ jsonrpc: '2.0', ...value }));
    ws.onopen = () => send({ id: 1, method: 'initialize', params: { processId: null, rootUri: 'file:///', capabilities: { textDocument: { publishDiagnostics: { relatedInformation: true } } }, initializationOptions: { hasWidgets: false }, clientInfo: { name: 'finite-lean-e2e-union-capture', version: '0.2.0' } } });
    ws.onerror = () => finish(Error('WEBSOCKET_TRANSPORT'));
    ws.onclose = () => { if (!finished) finish(Error('REMOTE_CLOSED_BEFORE_COMPLETION')); };
    ws.onmessage = event => {
      try {
        const raw = String(event.data);
        const rawBytes = Buffer.byteLength(raw);
        messageBytes += rawBytes;
        receivedMessages++;
        if (rawBytes > 4 * 1024 * 1024) return finish(Error('REMOTE_FRAME_BOUND'));
        if (messageBytes > 32 * 1024 * 1024) return finish(Error('REMOTE_TRANSPORT_BOUND'));
        const m = JSON.parse(raw);
        if (m.method === '$/lean/fileProgress') {
          progressMessages++;
          const ranges = m.params?.processing ?? [];
          let furthestLine = null;
          for (const r of ranges) {
            const line = r.range?.end?.line;
            if (Number.isInteger(line)) furthestLine = Math.max(furthestLine ?? 0, line);
          }
          lastProgress = { processing_ranges: ranges.length, furthest_end_line: furthestLine };
          return;
        }
        let retained = m;
        if (m.method === 'textDocument/publishDiagnostics') {
          const fresh = (m.params.diagnostics ?? []).filter(d => {
            const key = JSON.stringify([m.params.uri, m.params.version ?? null, d]);
            if (diagnosticKeys.has(key)) { duplicateDiagnostics++; return false; }
            diagnosticKeys.add(key);
            return true;
          });
          retained = fresh.length ? { ...m, params: { ...m.params, diagnostics: fresh } } : null;
        }
        if (retained) {
          const size = Buffer.byteLength(JSON.stringify(retained));
          if (retainedBytes + size > 4 * 1024 * 1024 || observations.length >= 2048)
            return finish(Error('REMOTE_RETAINED_OUTPUT_BOUND'));
          retainedBytes += size;
          observations.push(retained);
        }
        // Server requests have their own ID namespace. A refresh request may
        // also have id=1; it must never be mistaken for our initialize reply.
        if (m.method && Object.hasOwn(m, 'id')) {
          if (['workspace/inlayHint/refresh', 'workspace/semanticTokens/refresh', 'workspace/codeLens/refresh'].includes(m.method)) send({ id: m.id, result: null });
          else if (m.method === 'workspace/configuration') send({ id: m.id, result: (m.params?.items ?? []).map(() => null) });
          else send({ id: m.id, error: { code: -32601, message: 'Unsupported client method' } });
          return;
        }
        if (m.id === 1) {
          if (m.error || !m.result?.capabilities) return finish(Error('INITIALIZE_REJECTED'));
          initialized = true;
          send({ method: 'initialized', params: {} });
          send({ method: 'textDocument/didOpen', params: { textDocument: { uri, languageId: 'lean4', version: 1, text } } });
        }
        if (m.method === 'textDocument/publishDiagnostics' && m.params.uri === uri) {
          for (const d of m.params.diagnostics ?? []) if (d.message?.includes(SENTINEL)) sawSentinel = true;
          // The end sentinel is elaborated after the selected audit commands.
          // A final barrier request then waits on the exact document version.
          if (sawSentinel && initialized) {
            initialized = false;
            send({ id: 2, method: 'textDocument/hover', params: { textDocument: { uri }, position: { line: text.split('\n').length - 2, character: 1 } } });
          }
        }
        if (m.id === 2) {
          if (m.error) return finish(Error('FINAL_DOCUMENT_BARRIER_REJECTED'));
          finish(null, { before, observations, submitted_source_sha256: sha(text), source_sha256: sha(source), source_bytes: Buffer.byteLength(source), audits });
        }
      } catch (e) { finish(e); }
    };
  });
  const after = await metadata();
  if (JSON.stringify(before) !== JSON.stringify(after)) throw Object.assign(Error('HOST_VERSION_DRIFT'), { observations: result.observations });
  const notifications = result.observations.filter(x => x.method === 'textDocument/publishDiagnostics' && x.params.uri === uri);
  // Lean may send incremental updates; retain every diagnostic. Earlier errors
  // are never erased to manufacture success in this single immutable document.
  const ds = notifications.flatMap(x => x.params.diagnostics ?? []);
  const errors = ds.filter(x => x.severity === 1);
  const warnings = ds.filter(x => x.severity === 2);
  const info = ds.map(x => x.message ?? '');
  const auditRows = audits.map(name => {
    const rows = info.filter(x => x.includes(`'${name}'`));
    const clean = rows.some(x => x.includes('does not depend on any axioms') || (() => {
      const a = x.match(/depends on axioms:\s*\[([^\]]*)\]/);
      return a && a[1].split(',').map(x => x.trim()).filter(Boolean).every(x => STANDARDS.has(x));
    })());
    const bad = rows.some(x => /sorryAx|Lean\.ofReduceBool|native_decide|trustMe/.test(x));
    return { name, clean: Boolean(clean) && !bad, messages: rows };
  });
  const unsafeWarnings = warnings.filter(x => /sorry|admit|axiom|unchecked|unsafe/i.test(x.message ?? ''));
  const pass = sawSentinel && !errors.length && !unsafeWarnings.length && auditRows.every(x => x.clean);
  return { ...result, after, errors, warnings, audit_rows: auditRows, status: pass ? 'PASS_REMOTE_LEAN_CHECK' : 'REJECTED_REMOTE_LEAN_CHECK', lake_build: false, local_compiler: false, object_artifact: false, full_package_audit: false, accepted_old_context: false };
}

const [sourcePath, ...audits] = process.argv.slice(2);
const started = new Date().toISOString();
let report;
try {
  if (!sourcePath) throw Error('SOURCE_FILE_REQUIRED');
  report = await elaborate(readFileSync(sourcePath, 'utf8'), audits);
} catch (error) {
  report = { status: 'UNVERIFIED', reason: error.message, observations: error.observations ?? [], capture_stats: error.capture_stats ?? null };
}
report.started_utc = started;
report.finished_utc = new Date().toISOString();
// The parent run_online_lean.py captures this pipe in RAM and seals with real
// OS pipes. Node's spawnSync socket-backed stdio is refused by the codec guard.
// Do not redirect this raw internal stream to any file or a cloud log.
process.stdout.write(JSON.stringify(report));
process.exitCode = report.status === 'PASS_REMOTE_LEAN_CHECK' ? 0 : 2;
