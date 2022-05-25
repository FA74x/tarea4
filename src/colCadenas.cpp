/* 5088530 */

#include "../include/colCadenas.h"

struct _rep_colCadenas {
  nat tamanio;
  TCadena *c;
};

TColCadenas crearColCadenas(nat tamanio) {
  TColCadenas col = new _rep_colCadenas;
  col->c = new TCadena[tamanio];
  col->tamanio = tamanio;
  for (nat i = 0; i < tamanio; i++) {
    col->c[i] = crearCadena();
  }
  return col;
}

void liberarColCadenas(TColCadenas col) {
  nat tamanio = col->tamanio;
  for (nat i = 0; i < tamanio; i++)
    liberarCadena(col->c[i]);
  delete[] col->c;
  delete col;
}


nat tamanioColCadenas(TColCadenas col) {
  return col->tamanio;
}

TCadena cadenaDeColCadenas(nat pos, TColCadenas col) {
  return col->c[pos];
}

nat cantidadColCadenas(nat pos, TColCadenas col) {
  return cantidadEnCadena(col->c[pos]);
}

bool estaEnColCadenas(nat natural, nat pos, TColCadenas col) {
    return estaEnCadena(natural,col->c[pos]);
}

TColCadenas insertarEnColCadenas(nat natural, double real, nat pos, TColCadenas col) {
  col->c[pos] = insertarAlInicio(natural,real,col->c[pos]);
  return col;
}

TInfo infoEnColCadenas(nat natural, nat pos, TColCadenas col) {
  return infoCadena(natural,col->c[pos]);
}

TColCadenas removerDeColCadenas(nat natural, nat pos, TColCadenas col) {
  col->c[pos] = removerDeCadena(natural,col->c[pos]);
  return col;
}
