#!/usr/bin/env python3
"""Restore exact original certificate tables using only Python's standard library."""
from pathlib import Path
import gzip, hashlib, json, shutil, tempfile
ROOT = Path(__file__).resolve().parents[1]
def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''): h.update(chunk)
    return h.hexdigest()
def restore():
    for entry in json.loads((ROOT / 'certificates/manifest.json').read_text()):
        output = ROOT / entry['output']
        if output.exists():
            if output.stat().st_size != entry['bytes'] or digest(output) != entry['sha256']:
                raise RuntimeError(f'Refusing to overwrite differing existing file: {output}')
            print('ALREADY VERIFIED', entry['output'], flush=True)
            continue
        output.parent.mkdir(parents=True, exist_ok=True)
        temporary = output.with_name(output.name + '.restore-tmp')
        try:
            with tempfile.TemporaryFile() as compressed:
                for part in entry['parts']:
                    source = ROOT / part['path']
                    if digest(source) != part['sha256']:
                        raise RuntimeError(f'Compressed part hash mismatch: {source}')
                    with source.open('rb') as f: shutil.copyfileobj(f, compressed)
                compressed.seek(0)
                with gzip.GzipFile(fileobj=compressed, mode='rb') as stream, temporary.open('wb') as out:
                    shutil.copyfileobj(stream, out)
            if temporary.stat().st_size != entry['bytes'] or digest(temporary) != entry['sha256']:
                raise RuntimeError(f'Restored table mismatch: {output}')
            temporary.replace(output)
            print('RESTORED AND VERIFIED', entry['output'], flush=True)
        finally:
            temporary.unlink(missing_ok=True)
if __name__ == '__main__': restore()
