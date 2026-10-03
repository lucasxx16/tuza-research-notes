"""Hash staged Git blobs (canonical newlines); integrity is not correctness."""
import hashlib
import json
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[1]
output = 'results/artifact_sha256.json'
files = subprocess.check_output(['git','ls-files','-z'],cwd=root).decode().split('\0')
manifest = {name:hashlib.sha256(subprocess.check_output(['git','show',':'+name],cwd=root)).hexdigest()
            for name in sorted(files) if name and name != output}
(root/output).write_text(json.dumps(manifest,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print('Hashed',len(manifest),'tracked artifacts; manifest excludes itself.')
