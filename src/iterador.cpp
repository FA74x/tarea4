/* 5088530 */ // sustituiir con los 7 dígitos de la cédula

#include "../include/iterador.h"

struct _rep_iterador {
  struct nodo *primero;
  struct nodo *ultimo;
  struct nodo *actual;
};

struct nodo {
  nat info;
  nodo *siguiente;
};

typedef nodo *pnodo;

TIterador crearIterador() {
  TIterador iter = new _rep_iterador;
  iter->primero = NULL;
  iter->ultimo = NULL;
  iter->actual = NULL;
  return iter;
}

void liberarIterador(TIterador iter) {
  if (iter->primero != NULL) {
    iter->actual = iter->primero;
    nodo *aux = iter->actual;
    do {
      iter->actual = iter->actual->siguiente;
      delete aux;
      aux = iter->actual;
    } while (iter->actual != NULL);
  }
  delete iter;
}

bool estaDefinidaActual(TIterador iter) {
  return (iter->actual != NULL);
}

void agregarAIterador(nat elem, TIterador const iter) {
  if (iter->primero == NULL) {
    nodo *nuevo = new nodo;
    nuevo->info = elem;
    nuevo->siguiente = NULL;
    iter->primero = nuevo;
    iter->ultimo = nuevo;
  }
  else {
    nodo *nuevo = new nodo;
    nuevo->info = elem;
    nuevo->siguiente = NULL;
    iter->ultimo->siguiente = nuevo;
    iter->ultimo = nuevo;
  }
}

void reiniciarIterador(TIterador const iter) {
  iter->actual = iter->primero;
}

void avanzarIterador(TIterador const iter) {
  if (estaDefinidaActual(iter)) {
    iter->actual = iter->actual->siguiente;
  }
}

nat actualEnIterador(TIterador iter) {
  return iter->actual->info;
}