class {:autocontracts} Celula
{
    var dado:int;
    constructor ()
      ensures dado == 0;
    {
        dado := 0;
    }
}

class {:autocontracts} Contador
{
    var incs:Celula;
    var desc:Celula;
    ghost var valor:int;

    predicate Valid()
    {
        incs != desc &&
        incs.dado >= 0 && 
        desc.dado >= 0 &&
        valor == incs.dado - desc.dado
    }

    constructor()
      ensures valor == 0
    {
        incs := new Celula();
        desc := new Celula();
        valor := 0;
    }

    method Incrementa()
      ensures valor == old(valor) + 1
    {
        incs.dado := incs.dado + 1;
        valor := valor + 1;
    }
}