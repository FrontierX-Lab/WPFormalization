#!/usr/bin/env python3
"""Package `lake exe vbp build` output as the reader-facing blueprint/ site."""
from pathlib import Path
import argparse
import base64
import hashlib
import json
import re
import shutil
import tempfile
import tarfile
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
MARKED_URL = 'https://cdn.jsdelivr.net/npm/marked@11.1.1/marked.min.js'
MARKED_LOCAL = '-verso-data/vendor/marked/marked.umd.js'
PACKAGES = {
    'marked': ('11.1.1', ['lib/marked.umd.js', 'LICENSE.md']),
    'd3': ('7.9.0', ['dist/d3.min.js', 'LICENSE']),
    'd3-graphviz': ('5.6.0', ['build/d3-graphviz.min.js', 'LICENSE']),
}
ASSET_URLS = {
    MARKED_URL: MARKED_LOCAL,
    'https://cdn.jsdelivr.net/npm/d3@7.9.0/dist/d3.min.js': '-verso-data/vendor/d3/d3.min.js',
    'https://cdn.jsdelivr.net/npm/d3-graphviz@5.6.0/build/d3-graphviz.min.js': '-verso-data/vendor/d3-graphviz/d3-graphviz.min.js',
}


def reader_text(text):
    # Remove build-process narration without changing mathematical content or Lean names.
    text = re.sub(r'<div class="bp_build_metadata"[^>]*>.*?</div>', '', text, flags=re.S)
    text = text.replace('As of the R35 audit, stage one', 'Stage one')
    return text.replace('R35 implementation:', 'Formalization:')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--site-dir', type=Path, default=ROOT / '_out/site/html-multi')
    parser.add_argument('--vendor-dir', type=Path, help='Optional local directories for pinned JavaScript distributions')
    args = parser.parse_args()
    source = args.site_dir.resolve()
    destination = ROOT / 'blueprint'
    if not (source / 'index.html').is_file():
        parser.error('Generate the site with lake exe vbp build first.')
    if source == destination or destination in source.parents:
        parser.error('The generated input must be separate from blueprint/.')
    # This release's frozen source manifest is the reference for its exported site.
    for line in (ROOT / 'audit/sources.sha256').read_text().splitlines():
        expected, path = line.split('  ', 1)
        if hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != expected:
            parser.error('Frozen source changed: ' + path)
    with tempfile.TemporaryDirectory(prefix='wp-blueprint-export-') as temp:
        staged = Path(temp) / 'blueprint'
        shutil.copytree(source, staged)
        for name, (version, entries) in PACKAGES.items():
            vendor = staged / '-verso-data/vendor' / name
            vendor.mkdir(parents=True, exist_ok=True)
            candidates = [destination / '-verso-data/vendor' / name]
            if args.vendor_dir:
                candidates.insert(0, args.vendor_dir / name)
            assets = next((directory for directory in candidates
                           if all((directory / Path(entry).name).is_file() for entry in entries)), None)
            if assets:
                for entry in entries:
                    shutil.copy2(assets / Path(entry).name, vendor / Path(entry).name)
            else:
                package_url = f'https://registry.npmjs.org/{name}/-/{name}-{version}.tgz'
                with urllib.request.urlopen(package_url, timeout=30) as response:
                    # Read only the distribution and license, skipping the package's other builds.
                    pending = {'package/' + entry for entry in entries}
                    with tarfile.open(fileobj=response, mode='r|gz') as package:
                        for member in package:
                            if member.name in pending:
                                (vendor / Path(member.name).name).write_bytes(package.extractfile(member).read())
                                pending.remove(member.name)
                            if not pending:
                                break
                    if pending:
                        parser.error('Missing package assets: ' + ', '.join(sorted(pending)))
        marked_sri = 'sha384-' + base64.b64encode(hashlib.sha384((staged / MARKED_LOCAL).read_bytes()).digest()).decode()
        for path in staged.rglob('*'):
            if path.is_file() and path.suffix in ('.html', '.json', '.js', '.mjs'):
                text = path.read_text()
                # Generated JSON strings use escaped newlines; decode only their string values.
                if path.suffix == '.json':
                    def clean(value):
                        if isinstance(value, str):
                            return reader_text(value)
                        if isinstance(value, list):
                            return [clean(item) for item in value]
                        if isinstance(value, dict):
                            return {key: clean(item) for key, item in value.items()}
                        return value
                    text = json.dumps(clean(json.loads(text)), ensure_ascii=False, separators=(',', ':'))
                else:
                    text = reader_text(text)
                for remote, local in ASSET_URLS.items():
                    text = text.replace(remote, local)
                if path.suffix == '.html':
                    text = re.sub(r'<script\b[^>]*src="' + re.escape(MARKED_LOCAL) + r'"[^>]*>',
                                  lambda match: re.sub(r'integrity="[^"]*"', 'integrity="' + marked_sri + '"', match[0]), text)
                path.write_text(text)
        (staged / '.nojekyll').touch()
        inventory = {str(p.relative_to(staged)): hashlib.sha256(p.read_bytes()).hexdigest()
                     for p in sorted(staged.rglob('*')) if p.is_file()}
        record = {'sourceManifestSHA256': hashlib.sha256((ROOT / 'audit/sources.sha256').read_bytes()).hexdigest(),
                  'files': inventory}
        (staged / 'site-manifest.json').write_text(json.dumps(record, ensure_ascii=False, indent=2) + '\n')
        if destination.exists():
            # Only replace a previous generated export, never an unrecognized user directory.
            if not (destination / 'site-manifest.json').is_file():
                parser.error('blueprint/ exists but is not a recognized generated export.')
            old_files = sorted(str(p.relative_to(destination)) for p in destination.rglob('*') if p.is_file())
            print('Replacing generated blueprint/ files:', json.dumps(old_files), flush=True)
            shutil.rmtree(destination)
        shutil.copytree(staged, destination)
        print(json.dumps({'site': str(destination), 'files': len(inventory) + 1,
                          'bytes': sum(p.stat().st_size for p in destination.rglob('*') if p.is_file())}))


if __name__ == '__main__':
    main()
