#!/usr/bin/python3
import sys
if sys.argv[1:2] == ['check']:
    sys.stdout.buffer.write(b'{"schema":"source_calendar_check_v1","status":"ACCEPT"}\n')
    sys.exit(0)
sys.stdin.buffer.read()
sys.stdout.buffer.write(b'{"error":"INTERNAL","schema":"source_calendar_result_v1","status":"ERROR"}\n')
sys.exit(1)
