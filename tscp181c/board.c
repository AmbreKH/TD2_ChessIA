/*
 *	BOARD.C
 *	Tom Kerrigan's Simple Chess Program (TSCP)
 *
 *	Copyright 1997 Tom Kerrigan
 */


#include <stdlib.h>
#include "defs.h"
#include "data.h"
#include "protos.h"
#include "assert.h"


/* init_board() sets the board to the initial game state. */

void init_board()
{
	int i;

	for (i = 0; i < 64; ++i) {
		color[i] = init_color[i];
		piece[i] = init_piece[i];
	}
	syncBoard();

	side = LIGHT;
	xside = DARK;
	castle = 15;
	ep = -1;
	fifty = 0;
	ply = 0;
	hply = 0;
	set_hash();  /* init_hash() must be called before this function */
	first_move[0] = 0;

	assert(checkBoard());
}

void syncBoard() 
{
	memset(board, 0, sizeof(board));

	for (int i = 0; i <= 32; i++) {
		pospiece[i] = PIECE_DEAD;
	}

	int lightIdx = 2;
	int darkIdx = 18;

	for (int i = 0; i < 64; i++) {
		if (color[i] != EMPTY) { // On trouve une pièce sur l'échiquier
			// MAJ des tableaux pospiece et board
			if (piece[i] == KING)
			{
				// le roi est toujours rangé en 1ère position
				if (color[i] == LIGHT)
				{
					pospiece[1] = i;
					//piece_type[1] = KING;
					board[i] = 1;
				}
				else
				{
					pospiece[17] = i;
					//piece_type[17] = KING;
					board[i] = 17;
				}
			}
			else
			{
				if (color[i] == LIGHT)
				{
					pospiece[lightIdx] = i;
					//piece_type[lightIdx] = piece[i];
					board[i] = lightIdx;
					lightIdx++;
				}
				else
				{
					pospiece[darkIdx] = i;
					//piece_type[darkIdx] = piece[i];
					board[i] = darkIdx;
					darkIdx++;
				}
			}
		}
	}
}

int checkBoard()
{ // Cette fonction peut être plus ou moins longue, dépendamment de vos besoins en matière de debug
	for (int i = 0; i < 64; ++i)
	{
		if (piece[i] != EMPTY && board[i] == 0)
			return 0;
		if (piece[i] == EMPTY && board[i])
			return 0;
		if (color[i] == LIGHT && (board[i] > 16 || board[i] == 0))
			return 0;
		if (color[i] == DARK && board[i] < 17)
			return 0;
		if (board[i] && pospiece[board[i]] != i)
			return 0;
	}
	for (int i = 1; i <= 32; ++i)
	{
		if (pospiece[i] != PIECE_DEAD && board[pospiece[i]] != i)
			return 0;
		if (pospiece[i] != PIECE_DEAD && piece[pospiece[i]] == EMPTY)
			return 0;
		if (pospiece[i] != PIECE_DEAD && (color[pospiece[i]] == LIGHT && i > 16 || color[pospiece[i]] == DARK && i < 17))
			return 0;
	}
	return 1;
}

void initAttackTables()
{
	memset(canAttack, (char)0, sizeof(canAttack));

	// on ne gère pas la pawn via ces tables, car le déplacement du pion dépend de la couleur qui doit jouer
	int allPiecesButPawn[] = {KNIGHT, BISHOP, ROOK, QUEEN, KING};

	for (int i = 0; i < sizeof(allPiecesButPawn) / sizeof(allPiecesButPawn[0]); i++)
	{
		for (int from = 0; from < 64; from++)
		{
			for (int j = 0; j < offsets[allPiecesButPawn[i]]; ++j)
				for (int n = from;;) {
					n = mailbox[mailbox64[n] + offset[allPiecesButPawn[i]][j]];
					if (n == -1)
						break;
					canAttack[i][from][n] = TRUE;
					if (!slide[allPiecesButPawn[i]])
						break;
				}
		}
	}
}

/* init_hash() initializes the random numbers used by set_hash(). */

void init_hash()
{
	int i, j, k;

	srand(0);
	for (i = 0; i < 2; ++i)
		for (j = 0; j < 6; ++j)
			for (k = 0; k < 64; ++k)
				hash_piece[i][j][k] = hash_rand();
	hash_side = hash_rand();
	for (i = 0; i < 64; ++i)
		hash_ep[i] = hash_rand();
}


/* hash_rand() XORs some shifted random numbers together to make sure
   we have good coverage of all 32 bits. (rand() returns 16-bit numbers
   on some systems.) */

int hash_rand()
{
	int i;
	int r = 0;

	for (i = 0; i < 32; ++i)
		r ^= rand() << i;
	return r;
}


/* set_hash() uses the Zobrist method of generating a unique number (hash)
   for the current chess position. Of course, there are many more chess
   positions than there are 32 bit numbers, so the numbers generated are
   not really unique, but they're unique enough for our purposes (to detect
   repetitions of the position). 
   The way it works is to XOR random numbers that correspond to features of
   the position, e.g., if there's a black knight on B8, hash is XORed with
   hash_piece[BLACK][KNIGHT][B8]. All of the pieces are XORed together,
   hash_side is XORed if it's black's move, and the en passant square is
   XORed if there is one. (A chess technicality is that one position can't
   be a repetition of another if the en passant state is different.) */

void set_hash()
{
	int i;

	hash = 0;	
	for (i = 0; i < 64; ++i)
		if (color[i] != EMPTY)
			hash ^= hash_piece[color[i]][piece[i]][i];
	if (side == DARK)
		hash ^= hash_side;
	if (ep != -1)
		hash ^= hash_ep[ep];
}


/* in_check() returns TRUE if side s is in check and FALSE
   otherwise. It just scans the board to find side s's king
   and calls attack() to see if it's being attacked. */

BOOL in_check(int s)
{
	int k = s == LIGHT ? 1 : 17;
	return attack(pospiece[k], s ^ 1);
}


/* attack() returns TRUE if square sq is being attacked by side
   s and FALSE otherwise. */

BOOL attack(int sq, int s)
{
	// indices of first piece to iterate in pospiece
	int start = s == LIGHT ? 1 : 17;

	int i, j, n, localPiece;

	for (int idx = start; idx < start + 16; ++idx)
	{
		if (pospiece[idx] == PIECE_DEAD)
			continue;

		i = pospiece[idx];
		if (color[i] == s) {
			if (piece[i] == PAWN) {
				if (s == LIGHT) {
					if (COL(i) != 0 && i - 9 == sq)
						return TRUE;
					if (COL(i) != 7 && i - 7 == sq)
						return TRUE;
				}
				else {
					if (COL(i) != 0 && i + 7 == sq)
						return TRUE;
					if (COL(i) != 7 && i + 9 == sq)
						return TRUE;
				}
			}
			else
			{
				if (canAttack[piece[i]][i][sq])
				{
					if (!slide[piece[pospiece[i]]]) // inutile de vérifier pour les pièces qui ne slident pas
						return TRUE;
					for (j = 0; j < offsets[piece[i]]; ++j)
						for (n = i;;) {
							n = mailbox[mailbox64[n] + offset[piece[i]][j]];
							if (n == -1)
								break;
							if (n == sq)
								return TRUE;
							if (color[n] != EMPTY)
								break;
							if (!slide[piece[i]])
								break;
						}
				}
			}
		}
	}
	return FALSE;
}


/* gen() generates pseudo-legal moves for the current position.
   It scans the board to find friendly pieces and then determines
   what squares they attack. When it finds a piece/square
   combination, it calls gen_push to put the move on the "move
   stack." */

void gen()
{
	int i, j, n;
	int start = side == LIGHT ? 1 : 17;

	/* so far, we have no moves for the current ply */
	first_move[ply + 1] = first_move[ply];

	for (int idx = start; idx < start + 16; ++idx)
	{
		i = pospiece[idx];
		if (color[i] == side) {
			if (piece[i] == PAWN) {
				if (side == LIGHT) {
					if (COL(i) != 0 && color[i - 9] == DARK)
						gen_push(i, i - 9, 17);
					if (COL(i) != 7 && color[i - 7] == DARK)
						gen_push(i, i - 7, 17);
					if (color[i - 8] == EMPTY) {
						gen_push(i, i - 8, 16);
						if (i >= 48 && color[i - 16] == EMPTY)
							gen_push(i, i - 16, 24);
					}
				}
				else {
					if (COL(i) != 0 && color[i + 7] == LIGHT)
						gen_push(i, i + 7, 17);
					if (COL(i) != 7 && color[i + 9] == LIGHT)
						gen_push(i, i + 9, 17);
					if (color[i + 8] == EMPTY) {
						gen_push(i, i + 8, 16);
						if (i <= 15 && color[i + 16] == EMPTY)
							gen_push(i, i + 16, 24);
					}
				}
			}
			else
				for (j = 0; j < offsets[piece[i]]; ++j)
					for (n = i;;) {
						n = mailbox[mailbox64[n] + offset[piece[i]][j]];
						if (n == -1)
							break;
						if (color[n] != EMPTY) {
							if (color[n] == xside)
								gen_push(i, n, 1);
							break;
						}
						gen_push(i, n, 0);
						if (!slide[piece[i]])
							break;
					}
		}
	}

	/* generate castle moves */
	if (side == LIGHT) {
		if (castle & 1)
			gen_push(E1, G1, 2);
		if (castle & 2)
			gen_push(E1, C1, 2);
	}
	else {
		if (castle & 4)
			gen_push(E8, G8, 2);
		if (castle & 8)
			gen_push(E8, C8, 2);
	}

	/* generate en passant moves */
	if (ep != -1) {
		if (side == LIGHT) {
			if (COL(ep) != 0 && color[ep + 7] == LIGHT && piece[ep + 7] == PAWN)
				gen_push(ep + 7, ep, 21);
			if (COL(ep) != 7 && color[ep + 9] == LIGHT && piece[ep + 9] == PAWN)
				gen_push(ep + 9, ep, 21);
		}
		else {
			if (COL(ep) != 0 && color[ep - 9] == DARK && piece[ep - 9] == PAWN)
				gen_push(ep - 9, ep, 21);
			if (COL(ep) != 7 && color[ep - 7] == DARK && piece[ep - 7] == PAWN)
				gen_push(ep - 7, ep, 21);
		}
	}
} // gen()


/* gen_caps() is basically a copy of gen() that's modified to
   only generate capture and promote moves. It's used by the
   quiescence search. */

void gen_caps()
{
	int i, j, n;
	int start = side == LIGHT ? 1 : 17;


	first_move[ply + 1] = first_move[ply];
	for (int idx = start; idx < start + 16; ++idx)
	{
		i = pospiece[idx];
		if (color[i] == side) {
			if (piece[i] == PAWN) {
				if (side == LIGHT) {
					if (COL(i) != 0 && color[i - 9] == DARK)
						gen_push(i, i - 9, 17);
					if (COL(i) != 7 && color[i - 7] == DARK)
						gen_push(i, i - 7, 17);
					if (i <= 15 && color[i - 8] == EMPTY)
						gen_push(i, i - 8, 16);
				}
				if (side == DARK) {
					if (COL(i) != 0 && color[i + 7] == LIGHT)
						gen_push(i, i + 7, 17);
					if (COL(i) != 7 && color[i + 9] == LIGHT)
						gen_push(i, i + 9, 17);
					if (i >= 48 && color[i + 8] == EMPTY)
						gen_push(i, i + 8, 16);
				}
			}
			else
				for (j = 0; j < offsets[piece[i]]; ++j)
					for (n = i;;) {
						n = mailbox[mailbox64[n] + offset[piece[i]][j]];
						if (n == -1)
							break;
						if (color[n] != EMPTY) {
							if (color[n] == xside)
								gen_push(i, n, 1);
							break;
						}
						if (!slide[piece[i]])
							break;
					}
		}
	}
	if (ep != -1) {
		if (side == LIGHT) {
			if (COL(ep) != 0 && color[ep + 7] == LIGHT && piece[ep + 7] == PAWN)
				gen_push(ep + 7, ep, 21);
			if (COL(ep) != 7 && color[ep + 9] == LIGHT && piece[ep + 9] == PAWN)
				gen_push(ep + 9, ep, 21);
		}
		else {
			if (COL(ep) != 0 && color[ep - 9] == DARK && piece[ep - 9] == PAWN)
				gen_push(ep - 9, ep, 21);
			if (COL(ep) != 7 && color[ep - 7] == DARK && piece[ep - 7] == PAWN)
				gen_push(ep - 7, ep, 21);
		}
	}
} // gen_caps


/* gen_push() puts a move on the move stack, unless it's a
   pawn promotion that needs to be handled by gen_promote().
   It also assigns a score to the move for alpha-beta move
   ordering. If the move is a capture, it uses MVV/LVA
   (Most Valuable Victim/Least Valuable Attacker). Otherwise,
   it uses the move's history heuristic value. Note that
   1,000,000 is added to a capture move's score, so it
   always gets ordered above a "normal" move. */

void gen_push(int from, int to, int bits)
{
	gen_t* g;

	if (bits & 16) {
		if (side == LIGHT) {
			if (to <= H8) {
				gen_promote(from, to, bits);
				return;
			}
		}
		else {
			if (to >= A1) {
				gen_promote(from, to, bits);
				return;
			}
		}
	}
	g = &gen_dat[first_move[ply + 1]++];
	g->m.b.from = (char)from;
	g->m.b.to = (char)to;
	g->m.b.promote = 0;
	g->m.b.bits = (char)bits;
	if (color[to] != EMPTY)
		g->score = 1000000 + (piece[to] * 10) - piece[from];
	else
		g->score = history[from][to];
}


/* gen_promote() is just like gen_push(), only it puts 4 moves
   on the move stack, one for each possible promotion piece */

void gen_promote(int from, int to, int bits)
{
	int i;
	gen_t *g;
	
	for (i = KNIGHT; i <= QUEEN; ++i) {
		g = &gen_dat[first_move[ply + 1]++];
		g->m.b.from = (char)from;
		g->m.b.to = (char)to;
		g->m.b.promote = (char)i;
		g->m.b.bits = (char)(bits | 32);
		g->score = 1000000 + (i * 10);
	}
}


/* makemove() makes a move. If the move is illegal, it
   undoes whatever it did and returns FALSE. Otherwise, it
   returns TRUE. */

BOOL makemove(move_bytes m)
{
	assert(checkBoard());
	/* test to see if a castle move is legal and move the rook
	   (the king is moved with the usual move code later) */
	if (m.bits & 2) {
		int from, to;

		if (in_check(side))
			return FALSE;
		switch (m.to) {
			case 62:
				if (color[F1] != EMPTY || color[G1] != EMPTY ||
						attack(F1, xside) || attack(G1, xside))
					return FALSE;
				from = H1;
				to = F1;
				break;
			case 58:
				if (color[B1] != EMPTY || color[C1] != EMPTY || color[D1] != EMPTY ||
						attack(C1, xside) || attack(D1, xside))
					return FALSE;
				from = A1;
				to = D1;
				break;
			case 6:
				if (color[F8] != EMPTY || color[G8] != EMPTY ||
						attack(F8, xside) || attack(G8, xside))
					return FALSE;
				from = H8;
				to = F8;
				break;
			case 2:
				if (color[B8] != EMPTY || color[C8] != EMPTY || color[D8] != EMPTY ||
						attack(C8, xside) || attack(D8, xside))
					return FALSE;
				from = A8;
				to = D8;
				break;
			default:  /* shouldn't get here */
				from = -1;
				to = -1;
				break;
		}
		color[to] = color[from];
		piece[to] = piece[from];
		color[from] = EMPTY;
		piece[from] = EMPTY;

		assert(from >= 0 && from < 64 && to >= 0 && to < 64);
		assert(board[from] > 0 && board[from] <= 32);
		pospiece[board[from]] = to;
		board[to] = board[from];
		board[from] = 0;
	}

	/* back up information so we can take the move back later. */
	hist_dat[hply].m.b = m;
	hist_dat[hply].capture = piece[(int)m.to];
	hist_dat[hply].captureBoard = board[(int)m.to];
	hist_dat[hply].castle = castle;
	hist_dat[hply].ep = ep;
	hist_dat[hply].fifty = fifty;
	hist_dat[hply].hash = hash;

	/* update the castle, en passant, and
	   fifty-move-draw variables */
	castle &= castle_mask[(int)m.from] & castle_mask[(int)m.to];
	if (m.bits & 8) {
		if (side == LIGHT)
			ep = m.to + 8;
		else
			ep = m.to - 8;
	}
	else
		ep = -1;
	if (m.bits & 17)
		fifty = 0;
	else
		++fifty;

	assert(checkBoard());

	/* move the piece */
	color[(int)m.to] = side;
	if (m.bits & 32)
		piece[(int)m.to] = m.promote;
	else
		piece[(int)m.to] = piece[(int)m.from];
	color[(int)m.from] = EMPTY;
	piece[(int)m.from] = EMPTY;

	assert((int)m.from >= 0 && (int)m.from < 64 && (int)m.to >= 0 && (int)m.to < 64);
	assert(board[(int)m.from] > 0 && board[(int)m.from] <= 32);
	if (board[(int)m.to] != 0)
		pospiece[board[(int)m.to]] = PIECE_DEAD;
	pospiece[board[(int)m.from]] = (int)m.to;
	board[(int)m.to] = board[(int)m.from];
	board[(int)m.from] = 0;

	assert(checkBoard());

	/* erase the pawn if this is an en passant move */
	if (m.bits & 4) {
		if (side == LIGHT) {
			color[m.to + 8] = EMPTY;
			piece[m.to + 8] = EMPTY;
			assert(m.to + 8 >= 0 && m.to + 8 < 64);
			assert(board[m.to + 8] != 0);
			pospiece[board[m.to + 8]] = PIECE_DEAD;
			board[m.to + 8] = 0;
			hist_dat[hply].captureBoard = board[m.to + 8];
		}
		else {
			color[m.to - 8] = EMPTY;
			piece[m.to - 8] = EMPTY;
			assert(m.to - 8 >= 0 && m.to - 8 < 64);
			assert(board[m.to - 8] != 0);
			pospiece[board[m.to - 8]] = PIECE_DEAD;
			board[m.to - 8] = 0;
			hist_dat[hply].captureBoard = board[m.to - 8];
		}
	}

	// incrémentations des variables qui servent à l'historique et à connaître le pli en cours
	++ply;
	++hply;

	/* switch sides and test for legality (if we can capture
	   the other guy's king, it's an illegal position and
	   we need to take the move back) */
	side ^= 1;
	xside ^= 1;
	if (in_check(xside)) {
		takeback();
		return FALSE;
	}
	set_hash();

	assert(checkBoard());
	return TRUE;
}


/* takeback() is very similar to makemove(), only backwards :)  */

void takeback()
{

	assert(checkBoard());
	move_bytes m;

	side ^= 1;
	xside ^= 1;
	--ply;
	--hply;
	m = hist_dat[hply].m.b;
	castle = hist_dat[hply].castle;
	ep = hist_dat[hply].ep;
	fifty = hist_dat[hply].fifty;
	hash = hist_dat[hply].hash;
	color[(int)m.from] = side;

	board[(int)m.from] = board[(int)m.to];
	pospiece[board[(int)m.from]] = (int)m.from;

	if (m.bits & 32)
	{
		piece[(int)m.from] = PAWN;
	}
	else
	{
		piece[(int)m.from] = piece[(int)m.to];
	}
	if (hist_dat[hply].capture == EMPTY)
	{
		color[(int)m.to] = EMPTY;
		piece[(int)m.to] = EMPTY;
		board[(int)m.to] = 0;
	}
	else
	{
		color[(int)m.to] = xside;
		piece[(int)m.to] = hist_dat[hply].capture;
		board[(int)m.to] = hist_dat[hply].captureBoard;
		pospiece[board[(int)m.to]] = (int)m.to;
	}
	if (m.bits & 2) {
		int from, to;

		switch(m.to) {
			case 62:
				from = F1;
				to = H1;
				break;
			case 58:
				from = D1;
				to = A1;
				break;
			case 6:
				from = F8;
				to = H8;
				break;
			case 2:
				from = D8;
				to = A8;
				break;
			default:  /* shouldn't get here */
				from = -1;
				to = -1;
				break;
		}
		color[to] = side;
		piece[to] = ROOK;
		color[from] = EMPTY;
		piece[from] = EMPTY;

		board[to] = board[from];
		board[from] = 0;
		pospiece[board[to]] = to;
	}
	if (m.bits & 4) {
		if (side == LIGHT) {
			color[m.to + 8] = xside;
			piece[m.to + 8] = PAWN;
			board[m.to + 8] = hist_dat[hply].captureBoard;
			pospiece[board[m.to + 8]] = m.to + 8;
		}
		else {
			color[m.to - 8] = xside;
			piece[m.to - 8] = PAWN;
			board[m.to - 8] = hist_dat[hply].captureBoard;
			pospiece[board[m.to + 8]] = m.to - 8;
		}
	}

	assert(checkBoard());
}
