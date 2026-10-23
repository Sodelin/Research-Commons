import test from 'node:test';import assert from 'node:assert/strict';
import {cachedBody,identity,checkExpected} from '../tools/source-cache.mjs';
test('immutable public body reuse verifies all retained identities and checks new producer pins',()=>{
 const bytes=Buffer.from('Synthetic authored public source\n'),pin=identity(bytes),doc={body:bytes.toString(),...pin};
 assert.deepEqual(cachedBody(doc),bytes);
 assert.equal(cachedBody({...doc,body:'changed bytes'}),null);
 assert.equal(cachedBody({...doc,git_blob:'0'.repeat(40)}),null);
 assert.equal(cachedBody({...doc,bytes:0}),null);
 assert.equal(cachedBody(null),null);
 assert.doesNotThrow(()=>checkExpected({expected_sha256:pin.sha256,expected_bytes:pin.bytes},pin));
 assert.throws(()=>checkExpected({expected_sha256:'0'.repeat(64)},pin),/identity mismatch/);
 assert.throws(()=>checkExpected({expected_git_blob:'0'.repeat(40)},pin),/identity mismatch/);
 assert.throws(()=>checkExpected({expected_bytes:0},pin),/identity mismatch/);
});
