/* 5088530 */

#include "../include/aplicaciones.h"
#include "../include/cadena.h"
#include <math.h>
#include <string.h>

typedef unsigned int uint;

bool estaOrdenada(TCadena cad) {
  bool ordenada = true;
  if (cad != NULL) {
    TCadena aux = cad;
    while (cadenaSiguiente(aux) != cad && ordenada) {
      if (natInfo(primeroEnCadena(aux)) >= natInfo(primeroEnCadena(cadenaSiguiente(aux)))) {
        ordenada = false;
      }
      aux = cadenaSiguiente(aux);
    }
  }
  return ordenada;
}

TCadena mezclaCadenas(TCadena cad1, TCadena cad2) {
  TCadena nueva = crearCadena();
  if (cad1 != NULL && cad2 != NULL) {
    nat i = 0;
    nat j = 0;
    nat cantCad1 = cantidadEnCadena(cad1);
    nat cantCad2 = cantidadEnCadena(cad2);
    while (i < cantCad1 || j < cantCad2) {
      if (natInfo(primeroEnCadena(cad1)) == natInfo(primeroEnCadena(cad2))) {
        nueva = insertarAlFinal(natInfo(primeroEnCadena(cad1)),realInfo(primeroEnCadena(cad1)),nueva);
        cad1 = cadenaSiguiente(cad1);
        cad2 = cadenaSiguiente(cad2);
        i = i + 1;
        j = j + 1;
      } else if (natInfo(primeroEnCadena(cad1)) < natInfo(primeroEnCadena(cad2))) {
        if (i < cantCad1) {
          nueva = insertarAlFinal(natInfo(primeroEnCadena(cad1)),realInfo(primeroEnCadena(cad1)),nueva);
          cad1 = cadenaSiguiente(cad1);
          i = i + 1;
        } else {
          nueva = insertarAlFinal(natInfo(primeroEnCadena(cad2)),realInfo(primeroEnCadena(cad2)),nueva);
          cad2 = cadenaSiguiente(cad2);
          j = j + 1;
        }
      } else {
        if (j < cantCad2) {
          nueva = insertarAlFinal(natInfo(primeroEnCadena(cad2)),realInfo(primeroEnCadena(cad2)),nueva);
          cad2 = cadenaSiguiente(cad2);
          j = j + 1;
        } else {
          nueva = insertarAlFinal(natInfo(primeroEnCadena(cad1)),realInfo(primeroEnCadena(cad1)),nueva);
          cad1 = cadenaSiguiente(cad1);
          i = i + 1;
        }
      }
    }
  } else if (cad2 == NULL) {
    nueva = copiaCadena(cad1);
  } else {
    nueva = copiaCadena(cad2);
  }
  return nueva;
}

TAbb crearBalanceadoAux(TInfo *arreglo, TAbb &abb, int comienzo, int final) {
  if (comienzo < final) {
    int medio = ((comienzo + final) / 2);
    TInfo info = copiaInfo(arreglo[medio]);
    abb = consAbb(info,crearBalanceadoAux(arreglo,abb,comienzo,medio - 1),abb = crearBalanceadoAux(arreglo,abb,medio + 1,final));
  } else if (comienzo == final) {
    TInfo info = copiaInfo(arreglo[final]);
    abb = consAbb(info,NULL,NULL);
  } else {
    return NULL;
  }
  return abb;
}

TAbb crearBalanceado(TInfo *arreglo, nat n) {
  TAbb abb = crearAbb();
  int m = n;
  abb = crearBalanceadoAux(arreglo,abb,0,m-1);
  return abb;
}

TAbb unionAbbs(TAbb abb1, TAbb abb2) {
  TCadena arrAbb1 = linealizacion(abb1);
  TCadena arrAbb2 = linealizacion(abb2);
  TCadena cad = mezclaCadenas(arrAbb1,arrAbb2);
  int n = cantidadEnCadena(cad);
  TInfo *arreglo = new TInfo[n];
  for (int i = 0; i < n; i++) {
    arreglo[i] = primeroEnCadena(cad);
    cad = cadenaSiguiente(cad);
  }
  TAbb abbNuevo = crearBalanceado(arreglo,n);
  liberarCadena(arrAbb1);
  liberarCadena(arrAbb2);
  liberarCadena(cad);
  delete[] arreglo;
  return abbNuevo;
}

TCola ordenadaPorModulo(nat p, TCadena cad) {
  TCola c = crearCola();
  if (cad != NULL) {
    TCadena *arreglo = new TCadena[p];
    for (nat i = 0; i < p; i++) 
      arreglo[i] = crearCadena();
    TCadena aux = cad;
      do {
        int resto = natInfo(primeroEnCadena(aux)) % p;
        arreglo[resto] = insertarAlFinal(natInfo(primeroEnCadena(aux)),realInfo(primeroEnCadena(aux)),arreglo[resto]);
        aux = cadenaSiguiente(aux);
      } while (aux != cad);
    for (nat i = 0; i < p; i++) {
      while (arreglo[i] != NULL) {
        c = encolar(primeroEnCadena(arreglo[i]),c);
        arreglo[i] = removerPrimero(arreglo[i]);
      }
    }
  delete[] arreglo;
  }
  return c;
}

TPila menoresQueElResto(TCadena cad, nat cantidad) {
  TPila p = crearPila();
  for (nat i = 0; i < cantidad; i++) {
    if (cantidadEnPila(p) != 0 && natInfo(primeroEnCadena(cad)) <= natInfo(cima(p))) {
      while (cantidadEnPila(p) != 0 && natInfo(cima(p)) >= natInfo(primeroEnCadena(cad)))
        p = desapilar(p);
    }
    if (cantidadEnPila(p) == 0 || i == cantidad - 1) {
      p = apilar(primeroEnCadena(cad),p);
    } else if (natInfo(primeroEnCadena(cad)) > natInfo(cima(p))){
      p = apilar(primeroEnCadena(cad),p);
    }
    cad = cadenaSiguiente(cad);
  }
  return p;
}

TCadena linealizacionAux(TAbb abb, TCadena cad) {
  if (!esVacioAbb(abb)) {
    cad = linealizacionAux(izquierdo(abb),cad);
    cad = insertarAlFinal(natInfo(raiz(abb)),realInfo(raiz(abb)),cad);
    cad = linealizacionAux(derecho(abb),cad);
  }
  return cad;
}

TCadena linealizacion(TAbb abb) {
  TCadena cad = crearCadena();
  cad = linealizacionAux(abb,cad);
  return cad;
}

static void imprimirAbbAux(TAbb abb, uint nivel) {
  if (!esVacioAbb(abb)) {
    imprimirAbbAux(derecho(abb),nivel+1);
    for (uint i = 0; i < nivel; i++) {printf("-");}
    imprimirInfo(raiz(abb));
    printf("\n");
    imprimirAbbAux(izquierdo(abb),nivel+1);
  }
}

void imprimirAbb(TAbb abb) {
  uint nivel = 0;
  imprimirAbbAux(abb,nivel);  
}

static uint alturaAbb(TAbb abb) {
    if (esVacioAbb(abb)) {
      return 0;
    }
    else {
      return 1 + (fmax(alturaAbb(izquierdo(abb)),alturaAbb(derecho(abb))));
    }
}

static bool esPerfectoAux(TAbb abb, uint altura, uint nivel = 0) {
  if (abb == NULL) {
    return true;
  }
  if (izquierdo(abb) == NULL && derecho(abb) == NULL) {
    return (altura == nivel + 1);
  }
  if (izquierdo(abb) == NULL || derecho(abb) == NULL) {
    return false;
  }
  return esPerfectoAux(izquierdo(abb),altura,nivel + 1) && esPerfectoAux(derecho(abb),altura,nivel + 1);
}

bool esPerfecto(TAbb abb) {
  uint altura = alturaAbb(abb);
  return esPerfectoAux(abb,altura);
}

TAbb menores(double limite, TAbb abb) {
  TAbb a_izq, a_der, res;
  if (esVacioAbb(abb)) {
    res = NULL;
  } else {
    a_izq = menores(limite,izquierdo(abb));
    a_der = menores(limite,derecho(abb));
    if (realInfo(raiz(abb)) < limite) {
      TInfo info = copiaInfo(raiz(abb));
      res = consAbb(info,a_izq,a_der);
    } else if (a_izq == NULL) {
      res = a_der;
    } else if (a_der == NULL) {
      res = a_izq;
    } else {
      TInfo mayor;
      mayor = copiaInfo((mayorEnAbb(a_izq)));
      a_izq = removerDeAbb(natInfo(mayor),a_izq);
      res = consAbb(mayor,a_izq,a_der);
    }
  }
  return res;
}

static TIterador caminoAscendenteAux(nat clave, nat &k, TAbb abb, TIterador it) {
  if (k != 0 && clave == natInfo(raiz(abb))) {
    agregarAIterador(natInfo(raiz(abb)),it);
    k = k - 1;
  } else if (clave < natInfo(raiz(abb))) {
    caminoAscendenteAux(clave,k,izquierdo(abb),it);
    if (k != 0) {
      agregarAIterador(natInfo(raiz(abb)),it);
      k = k - 1;
    }
  } else if (clave > natInfo(raiz(abb))) {
    caminoAscendenteAux(clave,k,derecho(abb),it);
    if (k != 0) {
      agregarAIterador(natInfo(raiz(abb)),it);
      k = k - 1;
    }
  }
  return it;
}

TIterador caminoAscendente(nat clave, nat k, TAbb abb) {
  TIterador it = crearIterador();
  it = caminoAscendenteAux(clave,k,abb,it);
  return it;
}

static void imprimirPalabrasCortasAux(nat k, nat m, TPalabras palabras, ArregloChars arr) {
  if (m <= k && letra(palabras) == '\0') {
    arr[m] = letra(palabras);
    printf("%s\n",arr);
  } else if (m <= k && letra(palabras) != '\0') {
    arr[m] = letra(palabras);
    imprimirPalabrasCortasAux(k,m+1,subarboles(palabras),arr);
  } if (m <= k && siguientes(palabras) != NULL) {
    imprimirPalabrasCortasAux(k,m,siguientes(palabras),arr);
  }
}

void imprimirPalabrasCortas(nat k, TPalabras palabras) {
  TPalabras aux = subarboles(palabras);
  nat m = 0;
  ArregloChars arr = new char[k+1];
  imprimirPalabrasCortasAux(k,m,aux,arr);
  delete[] arr;
}

static TPalabras buscarFinPrefijoAux(int i, int largo, ArregloChars prefijo, TPalabras palabras) {
  if (i < largo && prefijo[i] == letra(palabras)) {
    return buscarFinPrefijoAux(i+1,largo,prefijo,subarboles(palabras));
  } else if (i <= largo && prefijo[i] != letra(palabras) && siguientes(palabras) == NULL) {
    return NULL;
  } else if (i == largo && prefijo[i] == letra(palabras)) {
    return palabras;
  } else {
    return buscarFinPrefijoAux(i,largo,prefijo,siguientes(palabras));
  }
}

TPalabras buscarFinPrefijo(ArregloChars prefijo, TPalabras palabras) {
  int largo = strlen(prefijo);
  int i = 0;
  TPalabras aux = subarboles(palabras);
  return buscarFinPrefijoAux(i,largo-1,prefijo,aux);
}

void reversoDeIteradorAux(TIterador iter, TIterador nuevo) {
  if (estaDefinidaActual(iter)) {
    nat n = actualEnIterador(iter);
    avanzarIterador(iter);
    reversoDeIteradorAux(iter,nuevo);
    agregarAIterador(n,nuevo);
  }
}

TIterador reversoDeIterador(TIterador iter) {
  reiniciarIterador(iter);
  TIterador nuevo = crearIterador();
  reversoDeIteradorAux(iter,nuevo);
  return nuevo;
}