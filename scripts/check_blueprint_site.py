#!/usr/bin/env python3
"""Check the packaged Blueprint site's content hashes and local asset links."""
from pathlib import Path
from html.parser import HTMLParser
from urllib.parse import urljoin, urlparse, unquote
import hashlib
import base64
import json

ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT / 'blueprint'


class Links(HTMLParser):
    def __init__(self):
        super().__init__()
        self.base = None
        self.urls = []

    def handle_starttag(self, tag, attributes):
        attrs = dict(attributes)
        if tag == 'base':
            self.base = attrs.get('href')
        for attr in ['src', 'href']:
            if attrs.get(attr) and tag != 'base':
                self.urls.append((tag, attr, attrs[attr], attrs.get('integrity')))


def main():
    errors = []
    manifest_path = SITE / 'site-manifest.json'
    if not manifest_path.is_file():
        print(json.dumps({'ok': False, 'errors': ['Missing blueprint/site-manifest.json']}))
        return 1
    manifest = json.loads(manifest_path.read_text())
    expected_source = hashlib.sha256((ROOT / 'audit/sources.sha256').read_bytes()).hexdigest()
    if manifest['sourceManifestSHA256'] != expected_source:
        errors.append('Site source manifest differs from the project source manifest')
    actual_files = {str(p.relative_to(SITE)) for p in SITE.rglob('*') if p.is_file()}
    if actual_files != set(manifest['files']) | {'site-manifest.json'}:
        errors.append('Site file inventory differs from its manifest')
    for rel, expected in manifest['files'].items():
        path = SITE / rel
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            errors.append('Site content changed: ' + rel)
    pages = list(SITE.rglob('*.html'))
    local_links = 0
    for path in pages:
        parser = Links()
        parser.feed(path.read_text())
        page_url = 'http://site.invalid/blueprint/' + path.relative_to(SITE).as_posix()
        base = urljoin(page_url, parser.base) if parser.base else page_url
        for tag, attr, url, integrity in parser.urls:
            resolved = urlparse(urljoin(base, url))
            if resolved.scheme not in ('http', 'https'):
                continue
            if resolved.netloc != 'site.invalid':
                if tag in ('script', 'link', 'img', 'iframe'):
                    errors.append('Remote runtime asset: ' + url)
                continue
            local_links += 1
            target = ROOT / unquote(resolved.path).lstrip('/')
            if target.is_dir():
                target = target / 'index.html'
            if not target.is_file():
                errors.append(str(path.relative_to(SITE)) + ' -> ' + url)
            elif integrity:
                matches = False
                for token in integrity.split():
                    algorithm, _, expected = token.partition('-')
                    if algorithm in ('sha256', 'sha384', 'sha512'):
                        actual = base64.b64encode(hashlib.new(algorithm, target.read_bytes()).digest()).decode()
                        matches = matches or actual == expected
                if not matches:
                    errors.append('Asset integrity mismatch: ' + url)
    graph_script = SITE / '-verso-data/Commands/graph.mjs'
    if 'https://cdn.jsdelivr.net/' in graph_script.read_text():
        errors.append('Dependency graph still loads a remote runtime library')
    summary = {'ok': not errors, 'pages': len(pages), 'files': len(actual_files),
               'localLinksChecked': local_links, 'errors': sorted(set(errors))}
    print(json.dumps(summary, ensure_ascii=False, indent=2))
    return int(bool(errors))


if __name__ == '__main__':
    raise SystemExit(main())
