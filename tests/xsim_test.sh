#!/bin/zsh
# input: $target_name $src_dir $tb_dir $test_dir $include_dir $file_paths
target_name=$1
src_dir=$2
tb_dir=$3
test_dir=$4
include_dir=$5
test_include_dir=$6
file_paths=${@:7}

function print_yellow(){
    echo -e "\033[33m$1\033[0m"
}
function print_red(){
    echo -e "\033[31m$1\033[0m"
}

PARSE_TOOL=xvlog
ELAB_TOOL=xelab
SIM_TOOL=xsim

PARSE_OPTION="-sv --sourcelibext sv -i $include_dir -i $test_include_dir --sourcelibdir $src_dir"
ELAB_OPTION="--relax --debug all -v 0"
# if you want to use vivado gui, add -gui option, and not use tclbatch option because it runs all simulation and immediately close the gui.
SIM_OPTION="--tclbatch $tb_dir/xsim_test.tcl"
# SIM_OPTION="-g"

# move to test directory
mkdir -p $test_dir
cd $test_dir
print_yellow "current_dir: $(pwd)"

print_yellow "$PARSE_TOOL $PARSE_OPTION $file_paths"
eval "$PARSE_TOOL $PARSE_OPTION $file_paths"

if [ $? -ne 0 ]; then
    print_red "Error: $PARSE_TOOL failed"
    exit 1
fi

print_yellow "$ELAB_TOOL $ELAB_OPTION $target_name -s $target_name\n"
eval "$ELAB_TOOL $ELAB_OPTION $target_name -s $target_name"

if [ $? -ne 0 ]; then
    print_red "Error: $ELAB_TOOL failed"
    exit 1
fi

print_yellow "$SIM_TOOL $SIM_OPTION -wdb $target_name.wdb $target_name\n"
eval "$SIM_TOOL $SIM_OPTION -wdb $target_name.wdb $target_name"
if [ $? -ne 0 ]; then
    print_red "Error: $SIM_TOOL failed"
    exit 1
fi

