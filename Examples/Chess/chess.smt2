; Définir la logique
(set-logic QF_LIA)

; Paramètres du problème
(define-const n Int 4) ; Taille de l'échiquier
(define-const num_kings Int 2) ; Nombre de rois
(define-const num_knights Int 2) ; Nombre de cavaliers
(define-const num_rooks Int 2) ; Nombre de tours
(define-const num_queens Int 2) ; Nombre de reines
(define-const num_bishops Int 2) ; Nombre de fous

; Fonctions d'aide pour les coordonnées
(define-fun coord ((x Int) (y Int)) Int (+ (* n x) y))
(define-fun x ((c Int)) Int (div c n))
(define-fun y ((c Int)) Int (mod c n))

; Fonction pour vérifier si les pièces s'attaquent
(define-fun attack ((c1 Int) (c2 Int) (dx Int) (dy Int)) Bool
    (and (= (abs (- (x c1) (x c2))) dx)
         (= (abs (- (y c1) (y c2))) dy)))

; Attaques de rois, cavaliers et tours
(define-fun king_attack ((c1 Int) (c2 Int)) Bool (attack c1 c2 1 1))
(define-fun knight_attack ((c1 Int) (c2 Int)) Bool
    (or (attack c1 c2 1 2) (attack c1 c2 2 1)))
(define-fun rook_attack ((c1 Int) (c2 Int)) Bool
    (or (= (x c1) (x c2)) (= (y c1) (y c2))))
(define-fun queen_attack ((c1 Int) (c2 Int)) Bool
    (or (rook_attack c1 c2) (attack c1 c2 1 1)))
(define-fun bishop_attack ((c1 Int) (c2 Int)) Bool (attack c1 c2 1 1))

; Positions des pièces
(declare-const king1_pos Int)
(declare-const king2_pos Int)
(declare-const knight1_pos Int)
(declare-const knight2_pos Int)
(declare-const rook1_pos Int)
(declare-const rook2_pos Int)
(declare-const queen1_pos Int)
(declare-const queen2_pos Int)
(declare-const bishop1_pos Int)
(declare-const bishop2_pos Int)

; Les positions doivent être dans les limites de l'échiquier
(assert (and (>= king1_pos 0) (< king1_pos (* n n))))
(assert (and (>= king2_pos 0) (< king2_pos (* n n))))
(assert (and (>= knight1_pos 0) (< knight1_pos (* n n))))
(assert (and (>= knight2_pos 0) (< knight2_pos (* n n))))
(assert (and (>= rook1_pos 0) (< rook1_pos (* n n))))
(assert (and (>= rook2_pos 0) (< rook2_pos (* n n))))
(assert (and (>= queen1_pos 0) (< queen1_pos (* n n))))
(assert (and (>= queen2_pos 0) (< queen2_pos (* n n))))
(assert (and (>= bishop1_pos 0) (< bishop1_pos (* n n))))
(assert (and (>= bishop2_pos 0) (< bishop2_pos (* n n))))

; Les positions des pièces doivent être différentes
(assert (distinct king1_pos king2_pos knight1_pos knight2_pos rook1_pos rook2_pos
    queen1_pos queen2_pos bishop1_pos bishop2_pos))

; Les rois ne doivent pas s'attaquer mutuellement
(assert (not (king_attack king1_pos king2_pos)))

; Les cavaliers ne doivent pas s'attaquer mutuellement
(assert (not (knight_attack knight1_pos knight2_pos)))

; Les tours ne doivent pas s'attaquer mutuellement
(assert (not (rook_attack rook1_pos rook2_pos)))

; Les reines ne doivent pas s'attaquer mutuellement
(assert (not (queen_attack queen1_pos queen2_pos)))

; Les fous ne doivent pas s'attaquer mutuellement
(assert (not (bishop_attack bishop1_pos bishop2_pos)))
; Les rois et les cavaliers ne doivent pas s'attaquer mutuellement
(assert (not (king_attack king1_pos knight1_pos)))
(assert (not (king_attack king1_pos knight2_pos)))
(assert (not (king_attack king2_pos knight1_pos)))
(assert (not (king_attack king2_pos knight2_pos)))

; Les rois et les tours ne doivent pas s'attaquer mutuellement
(assert (not (rook_attack king1_pos rook1_pos)))
(assert (not (rook_attack king1_pos rook2_pos)))
(assert (not (rook_attack king2_pos rook1_pos)))
(assert (not (rook_attack king2_pos rook2_pos)))

; Les rois et les reines ne doivent pas s'attaquer mutuellement
(assert (not (queen_attack king1_pos queen1_pos)))
(assert (not (queen_attack king1_pos queen2_pos)))
(assert (not (queen_attack king2_pos queen1_pos)))
(assert (not (queen_attack king2_pos queen2_pos)))

; Les rois et les fous ne doivent pas s'attaquer mutuellement
(assert (not (bishop_attack king1_pos bishop1_pos)))
(assert (not (bishop_attack king1_pos bishop2_pos)))
(assert (not (bishop_attack king2_pos bishop1_pos)))
(assert (not (bishop_attack king2_pos bishop2_pos)))

; Les cavaliers et les tours ne doivent pas s'attaquer mutuellement
(assert (not (rook_attack knight1_pos rook1_pos)))
(assert (not (rook_attack knight1_pos rook2_pos)))
(assert (not (rook_attack knight2_pos rook1_pos)))
(assert (not (rook_attack knight2_pos rook2_pos)))

; Les cavaliers et les reines ne doivent pas s'attaquer mutuellement
(assert (not (queen_attack knight1_pos queen1_pos)))
(assert (not (queen_attack knight1_pos queen2_pos)))
(assert (not (queen_attack knight2_pos queen1_pos)))
(assert (not (queen_attack knight2_pos queen2_pos)))

; Les cavaliers et les fous ne doivent pas s'attaquer mutuellement
(assert (not (bishop_attack knight1_pos bishop1_pos)))
(assert (not (bishop_attack knight1_pos bishop2_pos)))
(assert (not (bishop_attack knight2_pos bishop1_pos)))
(assert (not (bishop_attack knight2_pos bishop2_pos)))

; Les tours et les reines ne doivent pas s'attaquer mutuellement
(assert (not (queen_attack rook1_pos queen1_pos)))
(assert (not (queen_attack rook1_pos queen2_pos)))
(assert (not (queen_attack rook2_pos queen1_pos)))
(assert (not (queen_attack rook2_pos queen2_pos)))

; Les tours et les fous ne doivent pas s'attaquer mutuellement
(assert (not (bishop_attack rook1_pos bishop1_pos)))
(assert (not (bishop_attack rook1_pos bishop2_pos)))
(assert (not (bishop_attack rook2_pos bishop1_pos)))
(assert (not (bishop_attack rook2_pos bishop2_pos)))

; Les reines et les fous ne doivent pas s'attaquer mutuellement
(assert (not (bishop_attack queen1_pos bishop1_pos)))
(assert (not (bishop_attack queen1_pos bishop2_pos)))
(assert (not (bishop_attack queen2_pos bishop1_pos)))
(assert (not (bishop_attack queen2_pos bishop2_pos)))

; Recherche d'une solution
(check-sat)
(get-value (king1_pos king2_pos knight1_pos knight2_pos rook1_pos rook2_pos queen1_pos queen2_pos bishop1_pos bishop2_pos))