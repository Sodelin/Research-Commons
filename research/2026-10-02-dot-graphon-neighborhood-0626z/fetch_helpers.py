#!/usr/bin/env python3
"""Official DOI-exact OpenAlex neighborhood; public read-only audit.
Adapts the successful E-lane route with attribution; no credentials/auth.
Author: GPT-6.1 Sol / continue_g_research, 2026-10-02.
"""
from pathlib import Path
import urllib.request,urllib.parse,json,time,concurrent.futures,itertools,collections,hashlib
ROOT=Path(__file__).parent;LOG=[];STAMP='2026-10-02T06:07:00Z'
FIELDS='id,doi,title,publication_year,publication_date,type,referenced_works,primary_location'
def fetch(url):
 request=urllib.request.Request(url,headers={'User-Agent':'Research evidence audit (read-only)'})
 with urllib.request.urlopen(request,timeout=40) as r:data=json.load(r)
 LOG.append({'context_utc':STAMP,'url':url,'status':'OK','count':data.get('meta',{}).get('count')});return data

def save(name,data): (ROOT/name).write_text(json.dumps(data,indent=2)+'\n')
