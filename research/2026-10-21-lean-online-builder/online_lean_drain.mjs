/** Finish the existing quiet client after its complete report pipe drains.
 * The original protocol, barriers, versions, audits and decision are unchanged.
 * An unacknowledged WebSocket close cannot keep a finished report alive forever.
 * The parent still captures in RAM and encrypts before first persistence.
 */
await import('./online_lean_quiet.mjs');
await new Promise((resolve, reject) => {
  process.stdout.write('', error => error ? reject(error) : resolve());
});
process.exit(process.exitCode === 0 ? 0 : 2);
