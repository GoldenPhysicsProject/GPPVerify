import os, glob

webdir = "blueprint/src/web"
inject = (
    '<link rel="stylesheet" href="styles/mobile-fix.css" />\n'
    '<script>document.addEventListener("DOMContentLoaded",function(){'
    'var t=document.getElementById("toc-toggle"),'
    'n=document.querySelector("nav.toc");'
    'if(t&&n){t.addEventListener("click",function(){n.classList.toggle("active");});}'
    '});</script>\n'
)

files = glob.glob(os.path.join(webdir, "*.html"))
count = 0
for path in files:
    with open(path, "r") as f:
        html = f.read()
    if "mobile-fix.css" not in html:
        html = html.replace("</head>", inject + "</head>", 1)
        with open(path, "w") as f:
            f.write(html)
        count += 1

print(f"Patched {count}/{len(files)} HTML files")
