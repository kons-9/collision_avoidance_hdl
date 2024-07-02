# router structure
## introduction
TODO: とりあえず今はシングルサイクルで実装しているが、パイプライン化を行う。
routerはボトルネックになることが想定されるため、パイプライン化が重要。
現在は4段階のパイプライン構造を想定している。
そのため、構造を理解することが重要。

## structure
### first stage(D)
heartbeatの生成、flitのdecodeを行う
### second stage(R)
routing tableの参照、system flitのdecodeを行う
### third stage(C)
neighborの確認、parent, this_nodeの更新、system flitのgenerateを行う
### fourth stage(U)
routing table updateの処理を行う
### fifth stage(T)
checksumの計算、flitのencodeを行う
