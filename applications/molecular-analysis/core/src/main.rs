use molecular_haplotype_core::{build_haplotypes,bundle_json,error_json,parse_request,CoreError,MAX_INPUT_BYTES};
use std::io::{self,Read,Write};

fn execute() -> Result<String,CoreError> {
    let mut bytes=Vec::new();
    io::stdin().lock().take((MAX_INPUT_BYTES+1) as u64).read_to_end(&mut bytes)
        .map_err(|_|CoreError::invalid("STDIN","cannot read stdin"))?;
    if bytes.len()>MAX_INPUT_BYTES {return Err(CoreError::resource("stdin request exceeds 8MiB"));}
    let input=std::str::from_utf8(&bytes).map_err(|_|CoreError::invalid("PROTOCOL","stdin must be UTF-8"))?;
    let request=parse_request(input)?;
    Ok(bundle_json(&build_haplotypes(&request.window,&request.variants,&request.phase,request.roi)?))
}
fn main() {
    let result=execute();let refused=result.is_err();
    let record=result.unwrap_or_else(|e|error_json(&e));
    if writeln!(io::stdout().lock(),"{record}").is_err(){std::process::exit(3);}
    if refused{std::process::exit(2);}
}
