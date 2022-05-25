/* 5088530 */

#include "../include/cola.h"
#include "../include/cadena.h"

struct _rep_cola {
    TCadena elems;
    nat cantElems;
};

TCola crearCola() {
    TCola c = new _rep_cola;
    c->elems = crearCadena();
    c->cantElems = 0;
    return c;
}

void liberarCola(TCola c) {
    while (c->elems != NULL) {
        c->elems = removerPrimero(c->elems);
    }
    delete c;
}

nat cantidadEnCola(TCola c) {
    return c->cantElems;
}

TCola encolar(TInfo info, TCola c) {
    c->elems = insertarAlFinal(natInfo(info),realInfo(info),c->elems);
    c->cantElems = c->cantElems + 1;
    return c;
}

TInfo frente(TCola c) {
    return primeroEnCadena(c->elems);
}

TCola desencolar(TCola c) {
    c->elems = removerPrimero(c->elems);
    c->cantElems = c->cantElems - 1;
    return c;
}
