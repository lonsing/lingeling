#!/bin/sh

LC_TIME="en_US"
export LC_TIME

die () {
   echo "*** mkconfig.sh: $*" 1>&2
   exit 1
}

[ -f makefile ] || die "can not find 'makefile'"

cat<<EOF
/*************************************************************/
/* Automatically generated by './mkconfig.sh': do note edit! */
/*************************************************************/
EOF

echo "#define LGL_OS \"`uname -srmn`\""
echo "#define LGL_COMPILED \"`date`\""
#CUTHERE
echo "#define LGL_RELEASED \"`date`\""
echo "#define LGL_VERSION \"`cat VERSION`\""
echo "#define LGL_ID \"`./getgitid`\""
