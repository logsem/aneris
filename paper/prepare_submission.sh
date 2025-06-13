#! /bin/bash

# this is a script that automatically prepares the supplementary material to be submitted with the Lawyer paper.
# This is intended to be used by the paper authors, not by the end user/reviewers!
# !!! This script doesn't change the Rocq sources, so they must already be anonymized

TRILLIUM_GIT_URL=git@github.com:logsem/trillium.git
TRILLIUM_BRANCH=opam_package
LAWYER_GIT_URL=git@github.com:logsem/aneris.git
LAWYER_BRANCH=lawyer_paper

WORKING_DIR=lawyer_suppl

cleanup_current_dir () {
   for arg in "$@" .git .gitignore .gitmodules .github; do
       rm -rf $arg
   done
}


### script body

rm -rf $WORKING_DIR
mkdir $WORKING_DIR
cd $WORKING_DIR

git clone -b $TRILLIUM_BRANCH --single-branch $TRILLIUM_GIT_URL trillium
git clone -b $LAWYER_BRANCH --single-branch $LAWYER_GIT_URL lawyer

cd trillium
cleanup_current_dir
cd ..

mv lawyer/paper/README.md .
cd lawyer
cleanup_current_dir paper
cd ..

zip -r lawyer_suppl.zip trillium lawyer README.md
echo "Supplementary material is built in $(realpath lawyer_suppl.zip)"
