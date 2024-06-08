#!/bin/zsh
this_dir=$(cd $(dirname $0); pwd)
# テンプレートを利用して、テスト用のファイルを生成する
template_tb_file="$this_dir/template/tb_template.sv"

# テスト用のファイルを生成する
# srcファイルの数だけテストファイルを生成する
# ex) src/and_gate.sv -> tests/tb_and_gate.sv
# ex) src/utils/counter.sv -> tests/utils/tb_counter.sv

# srcファイルのリストを取得
# src_files=$(find src -name "*.sv")
src_file="$this_dir/../src/utils/flit_queue.sv"
module_name=$(basename $src_file | sed -e "s/\.sv//")

for src_file in $src_files; do
    # テストファイル名を生成
    test_file=$(echo $src_file | sed -e "s/src/tests/" -e "s/$module_name\.sv/tb_$module_name.sv/")

    # もし存在しなければテストファイルを生成
    if [ -e $test_file ]; then
        echo "$test_file already exists"
        continue
    fi
    echo "generate $test_file"
    mkdir -p $(dirname $test_file)
    cp $template_tb_file $test_file

    # テストファイルの中身を書き換える
    # TEMPLATE -> テストファイル名
    sed -i -e "s/TEMPLATE/$module_name/g" $test_file
done
