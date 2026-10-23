// Cache only exact, already-published immutable bodies; never cache queries or runtime records.
import {createHash} from 'node:crypto';
export function identity(bytes){return {bytes:bytes.length,sha256:createHash('sha256').update(bytes).digest('hex'),git_blob:createHash('sha1').update(Buffer.from('blob '+bytes.length+'\0')).update(bytes).digest('hex')};}
export function cachedBody(document){
 if(!document||typeof document.body!=='string')return null;
 const bytes=Buffer.from(document.body);if(bytes.length>512*1024)return null;
 const actual=identity(bytes);
 return ['bytes','sha256','git_blob'].every(k=>document[k]===actual[k])?bytes:null;
}
export function checkExpected(ref,actual){
 for(const [expected,key]of [['expected_sha256','sha256'],['expected_git_blob','git_blob'],['expected_bytes','bytes']]){
  if(ref[expected]!==undefined&&ref[expected]!==actual[key])throw Error('Public owned-source identity mismatch');
 }
}
