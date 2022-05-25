/* 5088530 */

#include "../include/abb.h"

struct _rep_abb {
    TInfo info;
    _rep_abb *izq, *der;
};

TAbb crearAbb() {
    TAbb abb = NULL;
    return abb; 
}

void liberarAbb(TAbb abb) {
    if (!esVacioAbb(abb)) {
        TAbb aux = abb;
        liberarAbb(derecho(abb));
        liberarAbb(izquierdo(abb));
        liberarInfo(aux->info);
        delete aux;
    }
}

bool esVacioAbb(TAbb abb) {
    return (abb == NULL);
}

TAbb buscarSubarbol(nat clave, TAbb abb) {
    if (!esVacioAbb(abb)) {
        if (natInfo(abb->info) == clave) {
            return abb;
        } else {
            if (clave < natInfo(abb->info)) {
                return buscarSubarbol(clave,izquierdo(abb));
            } else {
                return buscarSubarbol(clave,derecho(abb));
            }
        }
    } else {
        return NULL;
    }
}

TInfo raiz(TAbb abb) {
    return abb->info;
}

TAbb izquierdo(TAbb abb) {
    return abb->izq;
}

TAbb derecho(TAbb abb) {
    return abb->der;
}

TInfo menorEnAbb(TAbb abb) {
    if (izquierdo(abb) != NULL) {
        return menorEnAbb(izquierdo(abb));
    } else {
        return abb->info;
    }
}

TInfo mayorEnAbb(TAbb abb) {
    if (derecho(abb) != NULL) {
        return mayorEnAbb(derecho(abb));
    } else {
        return abb->info;
    }
}

TAbb consAbb(TInfo dato, TAbb izq, TAbb der) {
    TAbb nuevo = new _rep_abb;
    nuevo->info = dato;
    nuevo->izq = izq;
    nuevo->der = der;
    return nuevo;
}

TAbb insertarEnAbb(TInfo dato, TAbb abb) { 
    if (esVacioAbb(abb)) {
        abb = new _rep_abb;
        abb->info = dato;
        abb->izq = abb->der = NULL;
    } else {
        if (natInfo(dato) < natInfo(abb->info)) {
            abb->izq = insertarEnAbb(dato,abb->izq);
        } else if (natInfo(dato) > natInfo(abb->info)) {
            abb->der = insertarEnAbb(dato,abb->der);
        }
    }
    return abb;
}

TAbb removerDeAbb(nat clave, TAbb abb) {
    if (clave < natInfo(abb->info))
        abb->izq = removerDeAbb(clave,abb->izq);
    else if (clave > natInfo(abb->info))
        abb->der = removerDeAbb(clave,abb->der);
    else {
        if (clave == natInfo(abb->info) && esVacioAbb(izquierdo(abb)) && esVacioAbb(derecho(abb))) {
            TAbb borrar = abb;
            abb = NULL;
            liberarInfo(borrar->info);
            delete borrar;
        } else if (clave == natInfo(abb->info) && !esVacioAbb(izquierdo(abb)) && esVacioAbb(derecho(abb))) {
            TAbb borrar = abb;
            abb = izquierdo(abb);
            liberarInfo(borrar->info);
            delete borrar;
        } else if (clave == natInfo(abb->info) && esVacioAbb(izquierdo(abb)) && !esVacioAbb(derecho(abb))) {
            TAbb borrar = abb;
            abb = derecho(abb);
            liberarInfo(borrar->info);
            delete borrar;
        } else if (clave == natInfo(abb->info) && !esVacioAbb(izquierdo(abb)) && !esVacioAbb(derecho(abb))) {
            liberarInfo(abb->info);
            TInfo infoMayorIzq = copiaInfo(mayorEnAbb(izquierdo(abb)));
            abb->info = infoMayorIzq;
            abb->izq = removerDeAbb(natInfo(abb->info),abb->izq);
        }
    }
    return abb;
}

TAbb copiaAbb(TAbb abb) {
    if (!esVacioAbb(abb)) {
        TAbb abbNuevo = new _rep_abb;
        abbNuevo->info = crearInfo(natInfo(abb->info),realInfo(abb->info));
        abbNuevo->izq = copiaAbb(izquierdo(abb));
        abbNuevo->der = copiaAbb(derecho(abb));
        return abbNuevo;
    } else {
        return NULL;
    }
}