"""Audit tracked files and optional reachable history without printing matched values."""
import argparse
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RULES = {
    "credential": rb"(?:gh[pousr]_[A-Za-z0-9]{30,}|github_pat_[A-Za-z0-9_]{30,}|sk-[A-Za-z0-9_-]{30,}|AKIA[A-Z0-9]{16})",
    "private-key": rb"-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----",
    "personal-path": rb"(?:[A-Za-z]:[\\/]+Users[\\/]+[^\s\"\r\n]+|/(?:Users|home)/[^\s\"\r\n]+)",
    "session-id": rb"session-[0-9a-f]{8}(?:-[0-9a-f]{4}){3}-[0-9a-f]{12}",
    "private-endpoint": rb"https?://(?:localhost|127\.0\.0\.1|10\.\d+\.\d+\.\d+|192\.168\.\d+\.\d+)(?=[:/\s])",
}
INTERNAL = re.compile(
    r"(?:^|/)(?:session|models|history|accepted|hpc_sessions[^/]*|runtime[^/]*)\.json$"
    r"|(?:^|/)(?:task[^/]*|parent_corrections|parent_audit|CORRECTIONS_E|acceptance_review)\.txt$"
    r"|(?:^|/)\.env(?:\..+)?$|\.(?:pem|key|p12|pfx)$"
)


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def audit(label, path, data, findings):
    if INTERNAL.search(path) and not path.endswith(".env.example"):
        findings.add((label, path, "internal-file", 0))
    for category, pattern in RULES.items():
        for match in re.finditer(pattern, data):
            line = data.count(b"\n", 0, match.start()) + 1
            findings.add((label, path, category, line))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--history", action="store_true", help="Also inspect all reachable commits")
    args = parser.parse_args()
    findings = set()
    files = [p for p in git("ls-files", "-z").decode().split("\0") if p]
    for path in files:
        full = ROOT / path
        if full.is_file():
            audit("working-tree", path, full.read_bytes(), findings)
    commits = []
    seen = set()
    if args.history:
        commits = git("rev-list", "--all").decode().split()
        for commit in commits:
            for item in git("ls-tree", "-rz", commit).split(b"\0"):
                if not item:
                    continue
                meta, raw_path = item.split(b"\t", 1)
                _, kind, oid = meta.split()
                if kind != b"blob":
                    continue
                path = raw_path.decode()
                key = (oid, path)
                if key in seen:
                    continue
                seen.add(key)
                audit(commit[:12], path, git("cat-file", "blob", oid.decode()), findings)
    for label, path, category, line in sorted(findings):
        print(f"FAIL {label} {path}:{line} [{category}]")
    print(f"Audited {len(files)} tracked paths and {len(commits)} reachable commits; findings: {len(findings)}")
    return 1 if findings else 0


if __name__ == "__main__":
    raise SystemExit(main())
