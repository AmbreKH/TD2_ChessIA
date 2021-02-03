/*
 *	DEFS.H
 *	Tom Kerrigan's Simple Chess Program (TSCP)
 *
 *	Copyright 1997 Tom Kerrigan
 */


#define BOOL			int
#define TRUE			1
#define FALSE			0

#define GEN_STACK		1120
#define MAX_PLY			32
#define HIST_STACK		400

#define LIGHT			0
#define DARK			1

#define PAWN			0
#define KNIGHT			1
#define BISHOP			2
#define ROOK			3
#define QUEEN			4
#define KING			5

#define EMPTY			6

#define PIECE_DEAD		-1

 /* all squares */
#define A8				0
#define B8				1
#define C8				2
#define D8				3
#define E8				4
#define F8				5
#define G8				6
#define H8				7
#define A7				8
#define B7				9
#define C7				10
#define D7				11
#define E7				12
#define F7				13
#define G7				14
#define H7				15
#define A6				16
#define B6				17
#define C6				18
#define D6				19
#define E6				20
#define F6				21
#define G6				22
#define H6				23
#define A5				24
#define B5				25
#define C5				26
#define D5				27
#define E5				28
#define F5				29
#define G5				30
#define H5				31
#define A4				32
#define B4				33
#define C4				34
#define D4				35
#define E4				36
#define F4				37
#define G4				38
#define H4				39
#define A3				40
#define B3				41
#define C3				42
#define D3				43
#define E3				44
#define F3				45
#define G3				46
#define H3				47
#define A2				48
#define B2				49
#define C2				50
#define D2				51
#define E2				52
#define F2				53
#define G2				54
#define H2				55
#define A1				56
#define B1				57
#define C1				58
#define D1				59
#define E1				60
#define F1				61
#define G1				62
#define H1				63

#define ROW(x)			(x >> 3)
#define COL(x)			(x & 7)

#define IS_WHITE(x)		(x >= 17) // informe si une case du plateau est remplie par une piece blanche
#define IS_BLACK(x)		(x < 17 && x > 0) // informe si une case du plateau est remplie par une piece noire
#define IS_EMPTY(x)		(x == EMPTY) // informe si une case du plateau est vide
#define COLOR(x)		(pospiece[x] == PIECE_DEAD ? EMPTY : (IS_WHITE(x) ? LIGHT : DARK ) ) // permet de remplacer color[i] par COLOR(board[i])
//#define COLOR_IDX(x)	(IS_WHITE(x) ? 0 : 1) // renvoi un indice entre 0 et 1 selon la couleur de la piece sur la case : blanc -> 0, noir -> 1


/* This is the basic description of a move. promote is what
   piece to promote the pawn to, if the move is a pawn
   promotion. bits is a bitfield that describes the move,
   with the following bits:

   1	capture
   2	castle
   4	en passant capture
   8	pushing a pawn 2 squares
   16	pawn move
   32	promote

   It's union'ed with an integer so two moves can easily
   be compared with each other. */

typedef struct {
	char from;
	char to;
	char promote;
	char bits;
} move_bytes;

typedef union {
	move_bytes b;
	int u;
} move;

/* an element of the move stack. it's just a move with a
   score, so it can be sorted by the search functions. */
typedef struct {
	move m;
	int score;
} gen_t;

/* an element of the history stack, with the information
   necessary to take a move back. */
typedef struct {
	move m;
	int capture;
	int captureBoard;
	int castle;
	int ep;
	int fifty;
	int hash;
} hist_t;
