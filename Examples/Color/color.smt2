; Nombre de couleurs
(define-const k Int 4)

; Nombre de sommets
(define-const n Int 16)

; Coloration des sommets
(declare-const colors (Array Int Int))

; Définir un graphe avec des arêtes (i, j)
(declare-const edges (Array Int (Array Int Bool)))

; Fonction pour ajouter une arête au graphe
(define-fun add-edge ((i Int) (j Int)) Bool
    (and (= (select (select edges i) j) true)
         (= (select (select edges j) i) true)))

; Ajouter les arêtes dans le graphe
(assert (and (add-edge 0 1) (add-edge 1 2) (add-edge 2 3) (add-edge 3 0)
             (add-edge 0 4) (add-edge 1 5) (add-edge 2 6) (add-edge 3 7)
             (add-edge 4 5) (add-edge 5 6) (add-edge 6 7) (add-edge 7 4)
             (add-edge 4 8) (add-edge 5 9) (add-edge 6 10) (add-edge 7 11)
             (add-edge 8 9) (add-edge 9 10) (add-edge 10 11) (add-edge 11 8)
             (add-edge 8 12) (add-edge 9 13) (add-edge 10 14) (add-edge 11 15)
             (add-edge 12 13) (add-edge 13 14) (add-edge 14 15) (add-edge 15 12)))

; Contraintes de coloration
(assert (forall ((i Int) (j Int))
    (=> (select (select edges i) j)
        (not (= (select colors i) (select colors j))))))

; Les couleurs doivent être comprises entre 1 et k
(assert (forall ((i Int))
    (=> (and (<= i n) (>= i 0))
        (and (<= (select colors i) k) (>= (select colors i) 1)))))

; Recherche d'une solution
(check-sat)

; Afficher les couleurs pour chaque sommet
(get-value ((select colors 1)))
(get-value ((select colors 2)))
(get-value ((select colors 3)))
(get-value ((select colors 4)))
(get-value ((select colors 5)))
(get-value ((select colors 6)))
(get-value ((select colors 7)))
(get-value ((select colors 8)))
(get-value ((select colors 9)))
(get-value ((select colors 10)))
(get-value ((select colors 11)))
(get-value ((select colors 12)))
(get-value ((select colors 13)))
(get-value ((select colors 14)))
(get-value ((select colors 15)))
(get-value ((select colors 16)))
