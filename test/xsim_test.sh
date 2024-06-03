#!/bin/zsh
# input: $target_name $src_dir $tb_dir $test_dir $include_dir $file_paths
target_name=$1
src_dir=$2
tb_dir=$3
test_dir=$4
include_dir=$5
file_paths=${@:6}

function print_yellow(){
    echo -e "\033[33m$1\033[0m"
}

PARSE_TOOL=xvlog
ELAB_TOOL=xelab
SIM_TOOL=xsim

PARSE_OPTION="-sv --sourcelibext sv -i $include_dir --sourcelibdir $src_dir"
ELAB_OPTION="--relax --debug all"
SIM_OPTION="--tclbatch $tb_dir/xsim_test.tcl"

# move to test directory
mkdir -p $test_dir
cd $test_dir
print_yellow "current_dir: $(pwd)"

print_yellow "$PARSE_TOOL $PARSE_OPTION $file_paths"
eval "$PARSE_TOOL $PARSE_OPTION $file_paths"

print_yellow "$ELAB_TOOL $ELAB_OPTION $target_name -s $target_name\n"
eval "$ELAB_TOOL $ELAB_OPTION $target_name -s $target_name"

print_yellow "$SIM_TOOL $SIM_OPTION -wdb $target_name.wdb $target_name\n"
echo -e "\033[32m"
eval "$SIM_TOOL $SIM_OPTION -wdb $target_name.wdb $target_name"
echo -e "\033[0m"

