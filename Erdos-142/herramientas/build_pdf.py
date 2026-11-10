#!/usr/bin/env python3
"""Convierte NOTA.md (Markdown estilo GitHub con bloques ```math) a HTML+MathML y luego a PDF con Chromium."""
import re, subprocess, sys, pathlib
src = pathlib.Path(sys.argv[1]).resolve(); out_pdf = pathlib.Path(sys.argv[2]).resolve()
work = (pathlib.Path(sys.argv[3]) if len(sys.argv) > 3 else out_pdf.parent).resolve()
txt = src.read_text(encoding="utf-8")
# bloques ```math ... ```  ->  $$ ... $$
txt = re.sub(r"```math\n(.*?)\n```", lambda m: "$$\n" + m.group(1) + "\n$$", txt, flags=re.S)
txt = txt.replace(r"\lt", "<").replace(r"\gt", ">")
txt = txt.replace(r"\lbrace", r"\{").replace(r"\rbrace", r"\}")
txt = re.sub(r"\\tag\{[^}]*\}", "", txt)
md = work / "_nota_pandoc.md"; md.write_text(txt, encoding="utf-8")
html = work / "_nota.html"
css = """
<style>
body{font-family:'DejaVu Serif',Georgia,serif;max-width:46em;margin:2em auto;line-height:1.45;font-size:11pt;color:#111}
h1{font-size:1.6em} h2{font-size:1.25em;margin-top:1.6em;border-bottom:1px solid #999;padding-bottom:.15em} h3{font-size:1.08em}
blockquote{border-left:3px solid #888;margin:1em 0;padding:.2em 1em;background:#f4f4f4;color:#111}
code{font-size:.9em} table{border-collapse:collapse;font-size:.92em} td,th{border:1px solid #999;padding:.25em .5em;vertical-align:top}
math{font-size:1.02em}
</style>
"""
(work / "_hdr.html").write_text(css, encoding="utf-8")
subprocess.run(["pandoc", str(md), "-f", "markdown+tex_math_dollars-yaml_metadata_block", "-t", "html5", "--mathml", "-s",
                "--metadata", "title=Problema 142 de Erdős", "--metadata", "lang=es", "-H", str(work / "_hdr.html"), "-o", str(html)], check=True)
js = f"""
const {{ chromium }} = require('playwright');
(async () => {{
  const b = await chromium.launch(); const p = await b.newPage();
  await p.goto('file://{html}'); 
  await p.pdf({{ path: '{out_pdf}', format: 'A4', margin: {{top:'18mm',bottom:'18mm',left:'16mm',right:'16mm'}}, printBackground: true }});
  await p.screenshot({{ path: '{work}/_shot.png', fullPage: false }});
  await b.close();
}})();
"""
(work / "_print.js").write_text(js)
subprocess.run(["node", str(work / "_print.js")], check=True)
print("OK", out_pdf)
