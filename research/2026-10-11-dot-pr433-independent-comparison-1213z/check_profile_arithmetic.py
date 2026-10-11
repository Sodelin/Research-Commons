"""Own exact arithmetic only; no external supplier import or execution."""
from fractions import Fraction
old_local={1:2248,2:896,3:168,4:336,5:392,8:24,9:8}
removed_local={1:336,2:112,4:112,9:8}
new_local={r:n-removed_local.get(r,0) for r,n in old_local.items() if n-removed_local.get(r,0)}
assert new_local=={1:1912,2:784,3:168,4:224,5:392,8:24}
assert sum(r*n for r,n in new_local.items())==7032==9*560+240*8+72
old={1:167976,2:64512,3:12096,4:24192,5:28224,8:7488,9:576,16:3840,32:3840,48:3840}
new={1:142704,2:56448,3:12096,4:16128,5:28224,8:7488,16:3840,32:3840,48:3840}
d={r:n-new.get(r,0) for r,n in old.items() if n-new.get(r,0)}
assert d=={1:25272,2:8064,4:8064,9:576}
assert sum(d.values())==41976
assert sum(r*n for r,n in d.items())==78840==73*(13800-12720)
assert sum(r*n for r,n in new.items())==926064==73*12720-2496
assert 12720+560+16+2==13298
assert 13800+680+9+2-13298==1193
assert Fraction(sum(d.values()),1080)>Fraction(sum(old.values()),13800)
print('PASS: exact local/global profiles, deleted child count 41976 and deleted rank mass 78840')
print('PASS: width 12720, mass 926064, deficit 2496, physical stock 13298')
print('PASS: removed child density exceeds old density; inherited count-linear fallback density decreases')
print('LIMIT: arithmetic of the scoped hand count only; no external source replay or numerical root claimed')
