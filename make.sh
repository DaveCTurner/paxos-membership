#!/bin/bash

ID=`git show-ref --head | grep HEAD | head -c8`
DATE=`date +'%_d %B %Y'`

cat > inc.tex <<EOF
\\def\\gitid{$ID}
\\def\\pubdate{$DATE}
EOF

latex jitter-free-membership
latex jitter-free-membership
