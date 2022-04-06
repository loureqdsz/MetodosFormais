//for meio detalhado, com apenas uma invariant
method Main () {
    var a := new nat[5];
    //inicializar todas as posições com 0
    var i := 0;
    //invariant - quem decrease é a distancia entre a e i
    for i := 0 to a.Length
      invariant forall j :: 0 <= j < i ==> a[j]==0
    {
        a[i] := 0;
    }
    assert a[3] == 0;
}