import Lake
open Lake DSL
package physicalPMFCertificateNewContext

target verify _pkg : Unit := do
  Job.async do
    error "SOURCE_ONLY: native encrypt-before-persistence writers remain UNBOUND"
