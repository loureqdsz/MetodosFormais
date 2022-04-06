//os verificadores preferem essa forma de especificação, ela é mais facil de ser provada
function SomaAte (a:array<nat>, i:nat):nat
  requires i <= a.Length
  reads a
{
    if i == 0
    then 0
    else a[i-1] + SomaAte(a, i-1)
}

//quebra XX e é mais complicada de ser provada
function SomaAteV2 (a:array<nat>, i:nat, s:nat):nat
//ALGORITMO MERDA QUE COMPLICA A PROVA FEITA PELO DAFNY
  requires i <= a.Length
  reads a
  decreases a.Length - i
{
    if i==a.Length
    then s
    else SomaAteV2(a, i+1, s+a[i])
}

method Somatorio (a:array<nat>) returns (s:nat)
  //o que S terá no fim do somatório?
  //Podemos utilizar a primeira função para o somatorio  
  ensures s == SomaAte(a, a.Length)
{
    s := 0;
    for i := 0 to a.Length
      invariant s == SomaAte(a,i)
    {
        s := s + a[i];
    }

}

method SomatorioV2 (a:array<nat>) returns (s:nat)
  //FALHA POR CAUSA DO ALGORITMO EM SI
  //o que S terá no fim do somatório?
  //Podemos utilizar a segunda função para o somatorio
  ensures s == SomaAteV2(a, 0, 0)
{
    s := 0;
    for i := a.Length downto 0
      invariant 0 < i < a.Length
    {
        s := s + a[i-1];
    }

}

method Main () {
    var a:= new nat[3];
    a[0]:=1;
    a[1]:=2;
    a[2]:=3;
    var s := Somatorio(a);
}