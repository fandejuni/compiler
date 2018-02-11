/* arbres binaires de recherche */

struct ABR {
  int valeur;
  struct ABR *gauche, *droite;
};

int contient(struct ABR *a, int x) {
    contient(a->gauche, x);
}

int main() {
 return 0;
}

