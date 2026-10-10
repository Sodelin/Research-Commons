#!/usr/bin/python3
import sys
if len(sys.argv)>1 and sys.argv[1]=='check':
 sys.stdout.buffer.write(b'{"schema":"source_calendar_check_v1","status":"ACCEPT"}\n');sys.exit(0)
sys.stdin.buffer.read();sys.stdout.buffer.write(b'{}\n');sys.exit(0)
