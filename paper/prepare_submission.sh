#! /bin/bash

# this is a script that automatically prepares the submission of the Lawyer paper: the main paper and supplementary material.
# This is intended to be used by the paper authors, not by the end user/reviewers!
# !!! This script doesn't change the Rocq sources, so they must already be anonymized

PAPER_GIT_URL=git@github.com:logsem/wmm-liveness-notes.git
PAPER_BRANCH=main
TRILLIUM_GIT_URL=git@github.com:logsem/trillium.git
TRILLIUM_BRANCH=opam_package
LAWYER_GIT_URL=git@github.com:logsem/aneris.git
LAWYER_BRANCH=lawyer_paper
LAWYER_OOPSLA26_PATH=lawyer_oopsla26

WORKING_DIR_NAME=submission
COMMITS_LOG=commits.log

cleanup_current_dir () {
   for arg in "$@" .git .gitignore .gitmodules .github; do
       rm -rf $arg
   done
}


# ### script body

# recreate working dir
WORKING_DIR=$(realpath $WORKING_DIR_NAME)
rm -rf $WORKING_DIR
mkdir $WORKING_DIR
touch $WORKING_DIR/$COMMITS_LOG

# prepare paper
cd $WORKING_DIR
git clone -b $PAPER_BRANCH --single-branch $PAPER_GIT_URL paper
cd paper/$LAWYER_OOPSLA26_PATH
echo "Paper commit:" >> $WORKING_DIR/$COMMITS_LOG
git log -1 >> $WORKING_DIR/$COMMITS_LOG
make clean
make no-appendix
cp paper.pdf $WORKING_DIR/paper.pdf

# echo "Supplementary material is built in $(realpath $WORKING_DIR/paper.pdf)"
# echo EXITING EARLY
# exit 0

# prepare supplementary material

## 1) prepare Rocq development
cd $WORKING_DIR
git clone -b $TRILLIUM_BRANCH --single-branch $TRILLIUM_GIT_URL trillium
git clone -b $LAWYER_BRANCH --single-branch $LAWYER_GIT_URL lawyer

cd trillium
echo "Trillium commit:" >> $WORKING_DIR/$COMMITS_LOG
git log -1 >> $WORKING_DIR/$COMMITS_LOG
cleanup_current_dir
cd $WORKING_DIR

mv lawyer/paper/README.md .
cd lawyer
echo "Lawyer commit:" >> $WORKING_DIR/$COMMITS_LOG
git log -1 >> $WORKING_DIR/$COMMITS_LOG
cleanup_current_dir paper README.md
cd $WORKING_DIR

## 2) prepare paper with appendix
cd paper/$LAWYER_OOPSLA26_PATH
make clean
make
cp paper.pdf $WORKING_DIR/paper-appendix.pdf

## 3) complete supplementary material
cd $WORKING_DIR
zip -r lawyer_suppl.zip trillium lawyer README.md paper-appendix.pdf

echo "Submission material is built in $WORKING_DIR"
cat $WORKING_DIR/$COMMITS_LOG
