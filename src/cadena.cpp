/* 5088530 */ 

#include "../include/cadena.h"

struct _rep_cadena {
	TInfo info;
	TCadena siguiente;
	TCadena anterior;
}; 


TCadena crearCadena() {
	TCadena cad = NULL;
	return cad;
}

void liberarCadena(TCadena cad) {
	if (cad != NULL) {
		TCadena aux = cad->siguiente;
		TCadena borrar;
		while (aux != cad) {
			borrar = aux;
			aux = aux->siguiente;
			liberarInfo(borrar->info);
			delete borrar;
		}
		liberarInfo(cad->info);
		delete cad;
	}
}

nat cantidadEnCadena(TCadena cad) {
	nat cont = 0;
	TCadena aux = cad;
	if (aux != NULL) {
		do {
			aux = aux-> siguiente;
			cont++;
		} while (aux != cad);
	}
	return cont;
}

bool estaEnCadena(nat natural, TCadena cad) {
	if (cad != NULL) {
		if (natInfo(cad->info) == natural)
			return true;
		else {
			TCadena aux = cad;
			do {
				aux = aux->siguiente;
			} while (natInfo(aux->info) != natural && aux != cad);
			return (natInfo(aux->info) == natural);
		}
	} else {
		return false;
	}
}

TCadena insertarAlInicio(nat natural, double real, TCadena cad) {
	if (cad == NULL) {
		TCadena nuevo = new _rep_cadena;
		nuevo->info = crearInfo(natural,real);
		nuevo->siguiente = nuevo;
		nuevo->anterior = nuevo;
		return nuevo;
	}
	else {
		TCadena nuevo = new _rep_cadena;
		nuevo->info = crearInfo(natural,real);
		nuevo->siguiente = cad;
		nuevo->anterior = cad->anterior;
		cad->anterior->siguiente = nuevo;
		cad->anterior = nuevo;
		return nuevo;	
	}
}

TInfo infoCadena(nat natural, TCadena cad) {
	TCadena aux = cad;
	while (natInfo(aux->info) != natural){
		aux = aux-> siguiente;
	}
	return aux->info;
}

TInfo primeroEnCadena(TCadena cad) {
  return cad->info;
}

TCadena cadenaSiguiente(TCadena cad) {
	if (cad == NULL || cad->siguiente == NULL) {
		return cad;
	}
	else {
		return cad->siguiente;
	}
}

TCadena removerDeCadena(nat natural, TCadena cad) {
	TCadena borrar = cad;
	while (natural != natInfo(borrar->info))
		borrar = borrar->siguiente;
	if (borrar == cad)
		cad = cad->siguiente;
	if (cad->siguiente == cad)
		cad = NULL;
	TCadena siguiente = borrar->siguiente;
	TCadena anterior = borrar->anterior;
	anterior->siguiente = siguiente;
	siguiente->anterior = anterior;
	liberarInfo(borrar->info);
	delete borrar;
	return cad;
}

TCadena insertarAlFinal(nat natural, double real, TCadena cad) {
	if (cad == NULL) {
		cad = new _rep_cadena;
		cad->info = crearInfo(natural,real);
		cad->siguiente = cad->anterior = cad;
	} 
	else {
		TCadena nuevo = new _rep_cadena;
		nuevo->info = crearInfo(natural,real);
		nuevo->anterior = cad->anterior;
		nuevo->siguiente = cad;
		cad->anterior->siguiente = nuevo;
		cad->anterior = nuevo;
	}
	return cad;
}

TCadena removerPrimero(TCadena cad) {
	if (cad->siguiente != cad) {
		TCadena borrar = cad;
		cad->anterior->siguiente = cad->siguiente;
		cad->siguiente->anterior = cad->anterior;
		cad = cad->siguiente;
		liberarInfo(borrar->info);
		delete borrar;
	} else {
		liberarInfo(cad->info);
		delete cad;
		cad = NULL;
	}
	return cad;
}

void imprimirCadena(TCadena cad) {
	if (cad != NULL) {
		TCadena aux = cad;
		do {
			printf("(%u,%.2f)",natInfo(aux->info),realInfo(aux->info));
			aux = aux->siguiente;
		} while (aux != cad);
	}
	printf("\n");
}

TCadena copiaCadena(TCadena cad) {
	TCadena nueva = crearCadena();
	if (cad != NULL) {
		TCadena aux = cad;
		do {
			nueva = insertarAlFinal(natInfo(aux->info),realInfo(aux->info),nueva);
			aux = aux->siguiente;
		} while (aux != cad);
	}
	return nueva;
}

