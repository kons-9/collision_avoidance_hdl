# 形状自在ネットワークインターフェースドキュメント
コントローラがトップレベルのインターフェースです。

noc -> network interface -> router -> uart

## noc
とりあえず、システムにあった直接的なインターフェースを定義する。

### 送信側
- 送信中のビットフラグ、CLK、データバス

### 受信側
- 受信中のビットフラグ、CLK、データバス

## network interface 
- データをフリットに変換する

- data to flit

## router
- packet to flit

## uart
