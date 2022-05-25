/* 5088530 */

#include "../include/pila.h"
#include "../include/cadena.h"

struct _rep_pila {
    TCadena elems;
    nat cantElems;
};

TPila crearPila() {
    TPila p = new _rep_pila;
    p->elems = crearCadena();
    p->cantElems = 0;
    return p;
}

void liberarPila(TPila p) {
    while (p->elems != NULL) {
        p->elems = removerPrimero(p->elems);
    }
    delete p;
}

nat cantidadEnPila(TPila p) {
    return p->cantElems;
}

TPila apilar(TInfo info, TPila p) {
    p->elems = insertarAlInicio(natInfo(info),realInfo(info),p->elems);
    p->cantElems = p->cantElems + 1;
    return p;
}

TInfo cima(TPila p) {
    return primeroEnCadena(p->elems);
}

TPila desapilar(TPila p) {
    p->elems = removerPrimero(p->elems);
    p->cantElems = p->cantElems - 1;
    return p; 
}
