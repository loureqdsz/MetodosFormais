class Celula
{
    var dado:int;
    constructor ()
      ensures dado == 0;
    {
        dado := 0;
    }
}

class Contador
{
    var incs:Celula;
    var desc:Celula;
    ghost var valor:int;
    // frames dinâmicos
    ghost var Repr:set<object>;

    predicate Valid()
      reads this, Repr
    {
        this in Repr && 
        incs in Repr && 
        desc in Repr && 
        incs != desc &&
        incs.dado >= 0 && 
        desc.dado >= 0 &&
        valor == incs.dado - desc.dado
    }

    constructor()
      ensures Valid()
      ensures valor == 0
      ensures fresh(Repr - {this})
    {
        incs := new Celula();
        desc := new Celula();
        valor := 0;
        Repr := {this, incs, desc};
    }

    method Incrementa()
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures valor == old(valor) + 1
      ensures fresh(Repr - old(Repr))
    {
        incs.dado := incs.dado + 1;
        valor := valor + 1;
    }
}