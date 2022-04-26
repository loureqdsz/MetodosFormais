class {:autocontracts} FilaNatLimitada
{
    // Abstração
    ghost const TamanhoMaximo:nat;
    ghost var Conteudo:seq<nat>;
    // Implementação
    var a:array<nat>;
    const max:nat;
    var cauda:nat;

    predicate Valid()
    {
        max > 0 &&
        a.Length == max &&
        0 <= cauda <= max &&
        TamanhoMaximo == max && 
        Conteudo == a[..cauda]
    }

    constructor (m:nat)
      requires m > 0
      ensures TamanhoMaximo == m
      ensures Conteudo == []
    {
        a := new nat[m];
        max := m;
        cauda := 0;
        TamanhoMaximo := m;
        Conteudo := [];
    }
    

    method Enfileira (e:nat)
      requires |Conteudo| < TamanhoMaximo
      ensures Conteudo == old(Conteudo) + [e]
    {
        a[cauda] := e;
        cauda := cauda + 1;
        Conteudo := Conteudo + [e];
    }
    
    method Desenfileira () returns (e:nat)
      requires |Conteudo| > 0
      ensures e == old(Conteudo[0])
      ensures Conteudo == old(Conteudo)[1..]
    {
        e := a[0];
        cauda := cauda - 1;
        forall i | 0 <= i < cauda
        {
            a[i] := a[i+1];
        }  
        Conteudo := a[..cauda];
    }
}