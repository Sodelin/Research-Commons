"""Producer only: a successful exit still needs independent cover validation."""
import argparse,json
from pathlib import Path
import filter_core as c
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--request',required=True);p.add_argument('--request-sha256',required=True);p.add_argument('--checkpoints',required=True);a=p.parse_args()
    request=c.read_request(a.request,a.request_sha256)
    print(json.dumps(c.run_filter(request,Path(a.checkpoints)),indent=2))
