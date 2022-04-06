// for bem definido, muito detalhado. Com duas invariants
method Main () {
    var a := new nat[5];
    //inicializar todas as posições com 0
    var i := 0;
    //invariant - quem decrease é a distancia entre a e i
    while i < a.Length
      invariant 0 <= i <= a.Length
      invariant forall j :: 0 <= j < i ==> a[j]==0
    {
        a[i] := 0;
        i := i + 1;
    }
    assert a[3] == 0;
}