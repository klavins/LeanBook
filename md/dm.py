import sys
import re

#
# Converts to lean to markdown by converting comment blocks to markdown and code to markdown code blocks. 
# 
# Usage:
#  
#   python3 dm.py my_lean_file.ean > my_lean_file.md
#
# The resulting markdown file can be viewed with your favorite viewer.
#

f = open(sys.argv[1], "r", encoding='utf-8')

data = f.read()

copyright = """
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>
"""

print(copyright)

print("<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>")

print("<span style='color: lightgray; font-size: 10pt'>"
      + "<a href='https://github.com/klavins/LeanBook/blob/main/main/" + sys.argv[1] + "'>"
      + "Code</a> for this chapter</span>")

comment = r'(?s:(/-.*?-/))'

for str in re.split(comment, data)[1:]:
    if len(str) > 1 and str[0] == '/' and str[1] == '-':
        markdown = str[2:len(str)-2]
        print(markdown)
    else:
        code = str.lstrip().rstrip()
        if len(code) > 0:
            print("```lean")   # there is no lean highlighter with my chrome plugin
            print(code)
            print('```')

print("\n<div style='height=50px'>&nbsp;</div><hr>\nCopyright © 2025 Eric Klavins")
