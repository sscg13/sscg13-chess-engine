#include <iostream>
#include <fstream>
#include <cstdlib>
#include <time.h>
#include <bit>
#include <random>
#include <string>
#include <chrono>
using U64 = uint64_t;
using namespace std;


void printbitboard(U64 bitboard) {
    U64 other = byteswap(bitboard);
    for (int i = 0; i < 64; i++) {
        cout << (other%2);
        other = other >> 1;
        if (i == (i|7)) {
            cout << endl;
        }
    }
}
U64 FileA = 0x0101010101010101;
U64 FileB = FileA << 1;
U64 FileC = FileA << 2;
U64 FileD = FileA << 3;
U64 FileE = FileA << 4;
U64 FileF = FileA << 5;
U64 FileG = FileA << 6;
U64 FileH = FileA << 7;
U64 Rank1 = 0xFF;
U64 Rank2 = Rank1 << 8;
U64 Rank3 = Rank1 << 16;
U64 Rank4 = Rank1 << 24;
U64 Rank5 = Rank1 << 32;
U64 Rank6 = Rank1 << 40;
U64 Rank7 = Rank1 << 48;
U64 Rank8 = Rank1 << 56;
U64 Bitboards[8];
//White, Black, Pawn, Knight, Bishop, Rook, Queen, King
U64 AntiDiags[15] = {1ULL, 0x0000000000000102, 0x0000000000010204, 0x0000000001020408, 0x0000000102040810,
0x0000010204081020, 0x0001020408102040, 0x0102040810204080, 0x0204081020408000, 0x0408102040800000,
0x0810204080000000, 0x1020408000000000, 0x2040800000000000, 0x4080000000000000, 0x8000000000000000};
U64 Diags[15] = {0x0100000000000000, 0x0201000000000000,0x0402010000000000, 0x0804020100000000, 0x1008040201000000,
0x2010080402010000, 0x4020100804020100, 0x8040201008040201, 0x0080402010080402, 0x0000804020100804,
0x0000008040201008, 0x0000000080402010, 0x0000000000804020, 0x0000000000008040, 0x0000000000000080};
U64 Files[8] = {FileA, FileB, FileC, FileD, FileE, FileF, FileG, FileH};
U64 Ranks[8] = {Rank1, Rank2, Rank3, Rank4, Rank5, Rank6, Rank7, Rank8};
U64 KingAttacks[64];
U64 PawnAttacks[2][64];
U64 KnightAttacks[64];
U64 RankMask[64];
U64 FileMask[64];
U64 DiagMask[64];
U64 AntiMask[64];
U64 RankAttacks[512];
U64 hashes[8][64];
U64 epfilehash[8];
U64 colorhash = 0xE344F58E0F3B26E5;
U64 castlinghash[16];
U64 zobrist[1024];
int history[1024];
int gamelength = 0;
int last = 0;
int root = 0;
int moves[64][256];
int movescore[64][256];
int maxdepth = 32;
int killers[32][2];
int position = 0;
int evalm[2] = {0, 0};
int evale[2] = {0, 0};
int nodecount = 0;
int bestmove = 0;
U64 zobristhash = 0ULL;
int movetime = 0;
string proto = "uci";
bool gosent = false;
bool stopsearch = false;
//1 bit color, 7 bits halfmove, 6 bits ep, 4 bits castling KQkq
//6 bits from square, 6 bits to square, 1 bit color, 3 bits piece moved, 1 bit castling, 1 bit double pawn push,
//1 bit en passant, 1 bit promotion, 2 bits promoted piece, 1 bit capture, 3 bits piece captured
//26 bits total for now?
int movecount;
bool useNNUE = false;
const int nnuesize = 512;
short int nnuelayer1[768][nnuesize];
short int layer1bias[nnuesize];
int ourlayer2[nnuesize];
int theirlayer2[nnuesize];
short int whitehidden[nnuesize];
short int blackhidden[nnuesize];
int finalbias;
int evalscale = 400;
int evalQA = 255;
int evalQB = 64;
auto start = chrono::steady_clock::now();
int materialm[6] = {82, 337, 365, 477, 1025, 20000};
int materiale[6] = {94, 281, 297, 512, 936, 20000};
int pstm[6][64] = {{0,0,0,0,0,0,0,0,-35,-1,-20,-23,-15,24,38,-22,-26,-4,-4,-10,3,3,33,-12,-27,-2,-5,12,17,6,10,-25,
-14,13,6,21,23,12,17,-23,-6,7,26,31,65,56,25,-20,98,134,61,95,68,126,34,-11,0,0,0,0,0,0,0,0},
{-105,-21,-58,-33,-17,-28,-19,-23,-29,-53,-12,-3,-1,18,-14,-19,-23,-9,12,10,19,17,25,-16,-13,4,16,13,28,19,21,-8,
-9,17,19,53,37,69,18,22,-47,60,37,65,84,129,73,44,-73,-41,72,36,23,62,7,-17,-167,-89,-34,-49,61,-97,-15,-107},
{-33,-3,-14,-21,-13,-12,-39,-21,4,15,16,0,7,21,33,1,0,15,15,15,14,27,18,10,-6,13,13,26,34,12,10,4,
-4,5,19,50,37,37,7,-2,-16,37,43,40,35,50,37,-2,-26,16,-18,-13,30,59,18,-47,-29,4,-82,-37,-25,-42,7,-8},
{-19,-13,1,17,16,7,-37,-26,-44,-16,-20,-9,-1,11,-6,-71,-45,-25,-16,-17,3,0,-5,-33,-36,-26,-12,-1,9,-7,6,-23,
-24,-11,7,26,24,35,-8,-20,-5,19,26,36,17,45,61,16,27,32,58,62,80,67,26,44,32,42,32,51,63,9,31,43},
{-1,-18,-9,10,-15,-25,-31,-50,-35,-8,11,2,8,15,-3,1,-14,2,-11,-2,-5,2,14,5,-9,-26,-9,-10,-2,-4,3,-3,
-27,-27,-16,-16,-1,17,-2,1,-13,-17,7,8,29,56,47,57,-24,-39,-5,1,-16,57,28,54,-28,0,29,12,59,44,43,45},
{-15,36,12,-54,8,-28,34,14,1,7,-8,-64,-43,-16,9,8,-14,-14,-22,-46,-44,-30,-15,-27,-49,-1,-27,-39,-46,-44,-33,-51,
-17,-20,-12,-27,-30,-25,-14,-36,-9,24,2,-16,-20,6,22,-22,29,-1,-20,-7,-8,-4,-38,-29,-65,23,16,-15,-56,-34,2,13}};
int pste[6][64] = {{0,0,0,0,0,0,0,0,13,8,8,10,13,0,2,-7,4,7,-6,1,0,-5,-1,-8,13,9,-3,-7,-7,-8,3,-1,
32,24,13,5,-2,4,17,17,94,100,85,67,56,53,82,84,178,173,158,134,147,132,165,187,0,0,0,0,0,0,0,0},
{-29,-51,-23,-15,-22,-18,-50,-64,-42,-20,-10,-5,-2,-20,-23,-44,-23,-3,-1,15,10,-3,-20,-22,-18,-6,16,25,16,17,4,-18,
-17,3,22,22,22,11,8,-18,-24,-20,10,9,-1,-9,-19,-41,-25,-8,-25,-2,-9,-25,-24,-52,-58,-38,-13,-28,-31,-27,-63,-99},
{-23,-9,-23,-5,-9,-16,-5,-17,-14,-18,-7,-1,4,-9,-15,-27,-12,-3,8,10,13,3,-7,-15,-6,3,13,19,7,10,-3,-9,
-3,9,12,9,14,10,3,2,2,-8,0,-1,-2,6,0,4,-8,-4,7,-12,-3,-13,-4,-14,-14,-21,-11,-8,-7,-9,-17,-24},
{-9,2,3,-1,-5,-13,4,-20,-6,-6,0,2,-9,-9,-11,-3,-4,0,-5,-1,-7,-12,-8,-16,3,5,8,4,-5,-6,-8,-11,
4,3,13,1,2,1,-1,2,7,7,7,5,4,-3,-5,-3,11,13,13,11,-3,3,8,3,13,10,18,15,12,12,8,5},
{-33,-28,-22,-43,-5,-32,-20,-41,-22,-23,-30,-16,-16,-23,-36,-32,-16,-27,15,6,9,17,10,5,-18,28,19,47,31,34,39,23,
3,22,24,45,57,40,57,36,-20,6,9,49,47,35,19,9,-17,20,32,41,58,25,30,0,-9,22,22,27,27,19,10,20},
{-53,-34,-21,-11,-28,-14,-24,-43,-27,-11,4,13,14,4,-5,-17,-19,-3,11,21,23,16,7,-9,-18,-4,21,24,27,23,9,-11,
-8,22,24,27,26,33,26,3,10,17,23,15,20,45,44,13,-12,17,14,17,17,38,23,11,-74,-35,-18,-18,-11,15,4,-17}};
int castlechange[64] = {13, 15, 15, 15, 12, 15, 15, 14, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
15, 15, 15, 15,15, 15, 15, 15, 15, 15, 15, 15,15, 15, 15, 15, 15, 15, 15, 15,15, 15, 15, 15, 15, 15, 15, 15,7, 15, 15, 15,  3, 15, 15, 11};
int lmr_reductions[32][256];
int historytable[2][6][64];
int startpiece[16] = {3, 1, 2, 4, 5, 2, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0};
int phase[6] = {0, 1, 1, 2, 4, 0};
int gamephase[2] = {0, 0};
struct TTentry {
    U64 key;
    int score;
    int depth;
    int age;
    int nodetype;
    int hashmove;
};
int TTsize = 1349651;
TTentry TT[1349651];
struct abinfo {
    int hashmove;
    int eval;
    bool incheck;
};
abinfo searchstack[64];
int screlu(short int x) {
    return pow(max(min((int)x, 255), 0), 2);
}
U64 shift_w(U64 bitboard) {
    return (bitboard & ~FileA) >> 1;
}
U64 shift_n(U64 bitboard) {
    return bitboard << 8;
}
U64 shift_s(U64 bitboard) {
    return bitboard >> 8;
}
U64 shift_e(U64 bitboard) {
    return (bitboard & ~FileH) << 1;
}
void initializeleaperattacks() {
    for (int i = 0; i < 64; i++) {
        U64 square = 1ULL << i;
        PawnAttacks[0][i] = ((square & ~FileA) << 7) | ((square & ~FileH) << 9);
        PawnAttacks[1][i] = ((square & ~FileA) >> 9) | ((square & ~FileH) >> 7);
        U64 horizontal = square | shift_w(square) | shift_e(square);
        U64 full = horizontal | shift_n(horizontal) | shift_s(horizontal);
        KingAttacks[i] = full & ~square;
        U64 knightattack = ((square & ~FileA) << 15);
        knightattack |= ((square & ~FileA) >> 17);
        knightattack |= ((square & ~FileH) << 17);
        knightattack |= ((square & ~FileH) >> 15);
        knightattack |= ((square & ~FileG & ~FileH) << 10);
        knightattack |= ((square & ~FileG & ~FileH) >> 6);
        knightattack |= ((square & ~FileA & ~FileB) << 6);
        knightattack |= ((square & ~FileA & ~FileB) >> 10);
        KnightAttacks[i] = knightattack;
    }
}
void initializemasks() {
    for (int i = 0; i < 8; i++) {
        for (int j = 0; j < 8; j++) {
            RankMask[8*i+j] = Ranks[i];
            FileMask[8*i+j] = Files[j];
            AntiMask[8*i+j] = AntiDiags[i+j];
            DiagMask[8*i+j] = Diags[j+7-i];
        }
    }
}
void initializerankattacks() {
    for (U64 i = 0ULL; i < 0x000000000040; i++) {
        U64 occupied = i << 1;
        for (int j = 0; j < 8; j++) {
            U64 attacks = 0ULL;
            if (j > 0) {
                int k = j-1;
                while (k >= 0) {
                    attacks |= (1ULL << k);
                    if ((1ULL << k) & occupied) {
                        k = 0;
                    }
                    k--;
                }
            }
            if (j < 7) {
                int k = j+1;
                while (k <= 7) {
                    attacks |= (1ULL << k);
                    if ((1ULL << k) & occupied) {
                        k = 7;
                    }
                    k++;
                }
            }
            RankAttacks[8*i+j] = attacks;
        }
    }
}
U64 PawnMoves(U64 occupied, int square, int color) {
    int row = square&56;
    U64 step1;
    if (color == 0) {
        step1 = (1ULL << (square+8))&(~occupied);
    }
    else {
        step1 = (1ULL << (square-8))&(~occupied);
    }
    if ((row != 8 && color == 0)||(row!=48 && color == 1)) {
        return step1;
    }
    U64 step2;
    if (color == 0) {
        step2 = (step1<<8)&(~occupied);
    }
    else {
        step2 = (step1>>8)&(~occupied);
    }
    return step1|step2;
}
U64 DiagAttacks(U64 occupied, int square) {
    U64 forwards = occupied & DiagMask[square];
    U64 backwards = byteswap(forwards);
    forwards = forwards - 2*(1ULL << square);
    backwards = backwards - 2*(1ULL << (56^square));
    backwards = byteswap(backwards);
    return (forwards^backwards) & DiagMask[square];
}
U64 AntiAttacks(U64 occupied, int square) {
    U64 forwards = occupied & AntiMask[square];
    U64 backwards = byteswap(forwards);
    forwards = forwards - 2*(1ULL << square);
    backwards = backwards - 2*(1ULL << (56^square));
    backwards = byteswap(backwards);
    return (forwards^backwards) & AntiMask[square];
}
U64 FileAttacks(U64 occupied, int square) {
    U64 forwards = occupied & FileMask[square];
    U64 backwards = byteswap(forwards);
    forwards = forwards - 2*(1ULL << square);
    backwards = backwards - 2*(1ULL << (56^square));
    backwards = byteswap(backwards);
    return (forwards^backwards) & FileMask[square];
}
U64 GetRankAttacks(U64 occupied, int square) {
    int row = square & 56;
    int file = square & 7;
    int relevant = (occupied >> (row+1)) & 63;
    return (RankAttacks[8*relevant+file] << row);
}
void initializezobrist() {
    mt19937_64 mt(20346892);
    for (int i = 0; i < 8; i++) {
        for (int j = 0; j < 64; j++) {
            hashes[i][j] = mt();
        }
        epfilehash[i] = mt();
    }
    for (int i = 0; i < 16; i++) {
        castlinghash[i] = mt();
    }
}
U64 scratchzobrist() {
    U64 scratch = 0ULL;
    for (int i = 0; i < 8; i++) {
        for (int j = 0; j < 64; j++) {
            if (Bitboards[i]&(1ULL << j)) {
                scratch^=hashes[i][j];
            }
        }
    }
    if (position & 1) {
        scratch^=colorhash;
    }
    if (position & 0x00003F00) {
        int file = (position >> 8) & 7;
        scratch^=epfilehash[file];
    }
    int castling = (position >> 14) & 15;
    scratch^=castlinghash[castling];
    return scratch;
}
void initializett() {
    for (int i = 0; i < TTsize; i++) {
        TT[i].key = (U64)i+1ULL;
        TT[i].score = 0;
        TT[i].depth = 0;
        TT[i].age = 0;
        TT[i].nodetype = 0;
        TT[i].hashmove = 0;
    }
}
void updatett(int index, int depth, int score, int nodetype, int hashmove) {
    if (index < TTsize) {
        TT[index].key = zobristhash;
        TT[index].depth = depth;
        TT[index].age = gamelength;
        TT[index].hashmove = hashmove;
        TT[index].nodetype = nodetype;
        TT[index].score = score;
    }
}
void resethistory() {
    for (int i = 0; i < 6; i++) {
        for (int j = 0; j < 64; j++) {
            historytable[0][i][j] /= 2;
            historytable[1][i][j] /= 2;
        }
    }
}
void initializeboard() {
    Bitboards[0] = Rank1 | Rank2;
    Bitboards[1] = Rank7 | Rank8;
    Bitboards[2] = Rank2 | Rank7;
    Bitboards[3] = (Rank1 | Rank8) & (FileB | FileG);
    Bitboards[4] = (Rank1 | Rank8) & (FileC | FileF);
    Bitboards[5] = (Rank1 | Rank8) & (FileA | FileH);
    Bitboards[6] = (Rank1 | Rank8) & FileD;
    Bitboards[7] = (Rank1 | Rank8) & FileE;
    position = 0x0003C000;
    history[0] = position;
    int startmatm = (8*materialm[0]+2*(materialm[1]+materialm[2]+materialm[3])+materialm[4]);
    int startmate = (8*materiale[0]+2*(materiale[1]+materiale[2]+materiale[3])+materiale[4]);
    int startpstm = 0;
    int startpste = 0;
    for (int i = 0; i < 16; i++) {
        startpstm+=pstm[startpiece[i]][i];
        startpste+=pste[startpiece[i]][i];
    }
    for (int i = 0; i < 32; i++) {
        killers[i][0] = 0;
        killers[i][1] = 0;
    }
    evalm[0] = startmatm+startpstm;
    evalm[1] = startmatm+startpstm;
    evale[0] = startmate+startpste;
    evale[1] = startmate+startpste;
    gamephase[0] = 12;
    gamephase[1] = 12;
    gamelength = 0;
    zobrist[0] = scratchzobrist();
}
void initializelmr() {
    for (int i = 0; i < maxdepth; i++) {
        for (int j = 0; j < 256; j++) {
            lmr_reductions[i][j] = (i == 0 || j == 0) ? 0 : floor(0.53+log(i)*log(j)/2.44);
        }
    }
}
int repetitions() {
    int repeats = 0;
    for (int i = gamelength-2; i>=last; i-=2) {
        if (zobrist[i] == zobrist[gamelength]) {
            repeats++;
            if (i >= root) {
                repeats++;
            }
        }
    }
    return repeats;
}
U64 checkers(int color) {
    int kingsquare = popcount((Bitboards[color] & Bitboards[7])-1);
    int opposite = color^1;
    U64 attacks = 0ULL;
    U64 occupied = Bitboards[0] | Bitboards[1];
    attacks |= (KnightAttacks[kingsquare]&Bitboards[3]);
    attacks |= (PawnAttacks[color][kingsquare]&Bitboards[2]);
    attacks |= (DiagAttacks(occupied, kingsquare)&(Bitboards[4]|Bitboards[6]));
    attacks |= (AntiAttacks(occupied, kingsquare)&(Bitboards[4]|Bitboards[6]));
    attacks |= (GetRankAttacks(occupied, kingsquare)&(Bitboards[5]|Bitboards[6]));
    attacks |= (FileAttacks(occupied, kingsquare)&(Bitboards[5]|Bitboards[6]));
    attacks &= Bitboards[opposite];
    return attacks;
}
void makenullmove() {
    gamelength++;
    int halfmove = (position >> 1)&127;
    if (position & 0x00003F00) {
        int file = (position >> 8) & 7;
        zobristhash^=epfilehash[file];
        position^=((position >> 8)&63);
    }
    zobristhash^=colorhash;
    position^=(halfmove << 1);
    halfmove++;
    position^=(halfmove << 1);
    position^=1;
    zobrist[gamelength] = zobristhash;
    history[gamelength] = position;
}
void unmakenullmove() {
    gamelength--;
    position = history[gamelength];
    zobristhash = zobrist[gamelength];
}
void makemove(int notation, bool reversible) {
    //6 bits from square, 6 bits to square, 1 bit color, 3 bits piece moved, 1 bit capture, 3 bits piece captured, 1 bit promotion,
    //2 bits promoted piece, 1 bit castling, 1 bit double pawn push, 1 bit en passant,
    //26 bits total

    //1 bit color, 7 bits halfmove, 6 bits ep, 4 bits castling
    gamelength++;
    if (!reversible) {
        root = gamelength;
    }
    if (position & 0x00003F00) {
        int file = (position >> 8) & 7;
        zobristhash^=epfilehash[file];
    }
    int castling = (position >> 14) & 15;
    zobristhash^=castlinghash[castling];
    int from = notation & 63;
    int to = (notation >> 6) & 63;
    int color = (notation >> 12) & 1;
    int piece = (notation >> 13) & 7;
    Bitboards[color]^=((1ULL << from) | (1ULL << to));
    Bitboards[piece]^=((1ULL << from) | (1ULL << to));
    evalm[color] += pstm[piece-2][(56*color)^to];
    evalm[color] -= pstm[piece-2][(56*color)^from];
    evale[color] += pste[piece-2][(56*color)^to];
    evale[color] -= pste[piece-2][(56*color)^from];
    zobristhash^=(hashes[color][from]^hashes[color][to]);
    zobristhash^=(hashes[piece][from]^hashes[piece][to]);
    int captured = (notation >> 17) & 7;
    int promoted = (notation >> 21) & 3;
    int halfmove = (position >> 1) & 127;
    position^=(halfmove << 1);
    halfmove++;
    position&=0x0003C0FF;
    if (piece==2) {
        halfmove = 0;
        if (!reversible) {
            last = gamelength;
        }
    }
    if (notation & (1 << 16)) {
        Bitboards[color^1]^=(1ULL << to);
        Bitboards[captured]^=(1ULL << to);
        zobristhash^=(hashes[color^1][to]^hashes[captured][to]);
        evalm[color^1]-=materialm[captured-2];
        evale[color^1]-=materiale[captured-2];
        evalm[color^1]-=pstm[captured-2][(56*(color^1))^to];
        evale[color^1]-=pste[captured-2][(56*(color^1))^to];
        gamephase[color^1]-=phase[captured-2];
        halfmove = 0;
        if (!reversible) {
            last = gamelength;
        }
    }
    if (notation & (1 << 20)) {
        Bitboards[2]^=(1ULL << to);
        Bitboards[promoted+3]^=(1ULL << to);
        zobristhash^=(hashes[2][to]^hashes[promoted+3][to]);
        evalm[color]-=(materialm[0]+pstm[0][(56*color)^from]);
        evalm[color]+=(materialm[promoted+1]+pstm[promoted+1][(56*color)^from]);
        evale[color]-=(materiale[0]+pste[0][(56*color)^from]);
        evale[color]+=(materiale[promoted+1]+pste[promoted+1][(56*color)^to]);
        gamephase[color]+=phase[promoted+1];
    }
    else if (notation & (1 << 23)) {
        if (to&4) {
            Bitboards[color]^=((1ULL << (to-1)) | (1ULL << (to+1)));
            Bitboards[5]^=((1ULL << (to-1)) | (1ULL << (to+1)));
            zobristhash^=(hashes[color][to-1]^hashes[color][to+1]);
            zobristhash^=(hashes[5][to-1]^hashes[5][to+1]);
            evalm[color]+=(pstm[4][7^(56*color)]-pstm[4][5^(56*color)]);
            evale[color]+=(pste[4][7^(56*color)]-pste[4][5^(56*color)]);
        }
        else {
            Bitboards[color]^=((1ULL << (to-2)) | (1ULL << (to+1)));
            Bitboards[5]^=((1ULL << (to-2)) | (1ULL << (to+1)));
            zobristhash^=(hashes[color][to-2]^hashes[color][to+1]);
            zobristhash^=(hashes[5][to-2]^hashes[5][to+1]);
            evalm[color]+=(pstm[4][0^(56*color)]-pstm[4][3^(56*color)]);
            evale[color]+=(pste[4][0^(56*color)]-pste[4][3^(56*color)]);
        }
        evalm[color]+=50;
    }
    else if (notation & (1 << 24)) {
        position^=((from+to) << 7);
    }
    else if (notation & (1 << 25)) {
        int shadow;
        if (color==1) {
            shadow = to+8;
        }
        else {
            shadow = to-8;
        }
        Bitboards[2]^=(1ULL << shadow);
        Bitboards[color^1]^=(1ULL << shadow);
        zobristhash^=(hashes[2][shadow]^hashes[color^1][shadow]);
        evalm[color^1]-=(materialm[0]+pstm[0][(56*(color^1))^shadow]);
        evale[color^1]-=(materiale[0]+pste[0][(56*(color^1))^shadow]);
    }
    position&=(0x00003FFF | (castlechange[from] << 14));
    position&=(0x00003FFF | (castlechange[to] << 14));
    position^=1;
    position^=(halfmove << 1);
    zobristhash^=colorhash;
    if (position & 0x00003F00) {
        int file = (position >> 8) & 7;
        zobristhash^=epfilehash[file];
    }
    castling = (position >> 14) & 15;
    zobristhash^=castlinghash[castling];
    history[gamelength] = position;
    zobrist[gamelength] = zobristhash;
    nodecount++;
}
void unmakemove(int notation) {
    gamelength--;
    position = history[gamelength];
    zobristhash = zobrist[gamelength];
    int from = notation & 63;
    int to = (notation >> 6) & 63;
    int color = (notation >> 12) & 1;
    int piece = (notation >> 13) & 7;
    Bitboards[color]^=((1ULL << from) | (1ULL << to));
    Bitboards[piece]^=((1ULL << from) | (1ULL << to));
    evalm[color] += pstm[piece-2][(56*color)^from];
    evalm[color] -= pstm[piece-2][(56*color)^to];
    evale[color] += pste[piece-2][(56*color)^from];
    evale[color] -= pste[piece-2][(56*color)^to];
    int captured = (notation >> 17) & 7;
    int promoted = (notation >> 21) & 3;
    if (notation & (1 << 16)) {
        Bitboards[color^1]^=(1ULL << to);
        Bitboards[captured]^=(1ULL << to);
        evalm[color^1]+=materialm[captured-2];
        evale[color^1]+=materiale[captured-2];
        evalm[color^1]+=pstm[captured-2][(56*(color^1))^to];
        evale[color^1]+=pste[captured-2][(56*(color^1))^to];
        gamephase[color^1]+=phase[captured-2];
    }
    if (notation & (1 << 20)) {
        Bitboards[2]^=(1ULL << to);
        Bitboards[promoted+3]^=(1ULL << to);
        evalm[color]+=(materialm[0]+pstm[0][(56*color)^from]);
        evalm[color]-=(materialm[promoted+1]+pstm[promoted+1][(56*color)^from]);
        evale[color]+=(materiale[0]+pste[0][(56*color)^from]);
        evale[color]-=(materiale[promoted+1]+pste[promoted+1][(56*color)^to]);
        gamephase[color]-=phase[promoted+1];
    }
    else if (notation & (1 << 23)) {
        if (to&4) {
            Bitboards[color]^=((1ULL << (to-1)) | (1ULL << (to+1)));
            Bitboards[5]^=((1ULL << (to-1)) | (1ULL << (to+1)));
            evalm[color]+=(pstm[4][5^(56*color)]-pstm[4][7^(56*color)]);
            evale[color]+=(pste[4][5^(56*color)]-pste[4][7^(56*color)]);
        }
        else {
            Bitboards[color]^=((1ULL << (to-2)) | (1ULL << (to+1)));
            Bitboards[5]^=((1ULL << (to-2)) | (1ULL << (to+1)));
            evalm[color]+=(pstm[4][3^(56*color)]-pstm[4][0^(56*color)]);
            evale[color]+=(pste[4][3^(56*color)]-pste[4][0^(56*color)]);
        }
        evalm[color]-=50;
    }
    else if (notation & (1 << 25)) {
        int shadow;
        if (color) {
            shadow = to+8;
        }
        else {
            shadow = to-8;
        }
        Bitboards[2]^=(1ULL << shadow);
        Bitboards[color^1]^=(1ULL << shadow);
        evalm[color^1]+=(materialm[0]+pstm[0][(56*(color^1))^shadow]);
        evale[color^1]+=(materiale[0]+pste[0][(56*(color^1))^shadow]);
    }
}
int generatemoves(int color, bool capturesonly, int depth) {
    movecount = 0;
    int kingsquare = popcount((Bitboards[color] & Bitboards[7])-1);
    int pinrank = kingsquare&56;
    int pinfile = kingsquare&7;
    int opposite = color^1;
    U64 opponentattacks = 0ULL;
    U64 pinnedpieces = 0ULL;
    U64 checkmask = 0ULL;
    U64 preoccupied = Bitboards[0] | Bitboards[1];
    U64 kingDiag = DiagAttacks(preoccupied, kingsquare);
    U64 kingAnti = AntiAttacks(preoccupied, kingsquare);
    U64 kingRank = GetRankAttacks(preoccupied, kingsquare);
    U64 kingFile = FileAttacks(preoccupied, kingsquare);
    U64 occupied = preoccupied^(1ULL << kingsquare);
    U64 opponentpawns = Bitboards[opposite]&Bitboards[2];
    U64 opponentknights = Bitboards[opposite]&Bitboards[3];
    U64 opponentbishops = Bitboards[opposite]&Bitboards[4];
    U64 opponentrooks = Bitboards[opposite]&Bitboards[5];
    U64 opponentqueens = Bitboards[opposite]&Bitboards[6];
    int pawncount = popcount(opponentpawns);
    int knightcount = popcount(opponentknights);
    int bishopcount = popcount(opponentbishops);
    int rookcount = popcount(opponentrooks);
    int queencount = popcount(opponentqueens);
    U64 ourcaptures = 0ULL;
    U64 ourmoves = 0ULL;
    U64 ourmask = 0ULL;
    for (int i = 0; i < pawncount; i++) {
        int pawnsquare = popcount((opponentpawns & -opponentpawns)-1);
        opponentattacks |= PawnAttacks[opposite][pawnsquare];
        opponentpawns^=(1ULL << pawnsquare);
    }
    for (int i = 0; i < knightcount; i++) {
        int knightsquare = popcount((opponentknights & -opponentknights)-1);
        opponentattacks |= KnightAttacks[knightsquare];
        opponentknights^=(1ULL << knightsquare);
    }
    for (int i = 0; i < bishopcount; i++) {
        int bishopsquare = popcount((opponentbishops & -opponentbishops)-1);
        U64 diag = DiagAttacks(occupied, bishopsquare);
        U64 anti = AntiAttacks(occupied, bishopsquare);
        if (!(diag&(1ULL << kingsquare))) {
            pinnedpieces |= (diag & kingDiag);
        }
        else {
            checkmask |= (DiagAttacks(preoccupied, bishopsquare) & kingDiag);
        }
        if (!(anti&(1ULL << kingsquare))) {
            pinnedpieces |= (anti & kingAnti);
        }
        else {
            checkmask |= (AntiAttacks(preoccupied, bishopsquare) & kingAnti);
        }
        opponentattacks |= (diag | anti);
        opponentbishops^=(1ULL << bishopsquare);
    }
    for (int i = 0; i < rookcount; i++) {
        int rooksquare = popcount((opponentrooks & -opponentrooks)-1);
        U64 r = GetRankAttacks(occupied, rooksquare);
        U64 file = FileAttacks(occupied, rooksquare);
        if (!(r&(1ULL << kingsquare))) {
            pinnedpieces |= (r & kingRank);
        }
        else {
            checkmask |= (GetRankAttacks(preoccupied, rooksquare) & kingRank);
        }
        if (!(file&(1ULL << kingsquare))) {
            pinnedpieces |= (file & kingFile);
        }
        else {
            checkmask |= (FileAttacks(preoccupied, rooksquare) & kingFile);
        }
        opponentattacks |= (r | file);
        opponentrooks^=(1ULL << rooksquare);
    }
    for (int i = 0; i < queencount; i++) {
        int queensquare = popcount((opponentqueens & -opponentqueens)-1);
        U64 diag = DiagAttacks(occupied, queensquare);
        U64 anti = AntiAttacks(occupied, queensquare);
        U64 r = GetRankAttacks(occupied, queensquare);
        U64 file = FileAttacks(occupied, queensquare);
        if (!(diag&(1ULL << kingsquare))) {
            pinnedpieces |= (diag & kingDiag);
        }
        else {
            checkmask |= (DiagAttacks(preoccupied, queensquare) & kingDiag);
        }
        if (!(anti&(1ULL << kingsquare))) {
            pinnedpieces |= (anti & kingAnti);
        }
        else {
            checkmask |= (AntiAttacks(preoccupied, queensquare) & kingAnti);
        }
        if (!(r&(1ULL << kingsquare))) {
            pinnedpieces |= (r & kingRank);
        }
        else {
            checkmask |= (GetRankAttacks(preoccupied, queensquare) & kingRank);
        }
        if (!(file&(1ULL << kingsquare))) {
            pinnedpieces |= (file & kingFile);
        }
        else {
            checkmask |= (FileAttacks(preoccupied, queensquare) & kingFile);
        }
        opponentattacks |= (r | file);
        opponentattacks |= (diag | anti);
        opponentqueens^=(1ULL << queensquare);
    }
    int opponentking = popcount((Bitboards[opposite]&Bitboards[7])-1);
    opponentattacks |= KingAttacks[opponentking];
    ourcaptures = KingAttacks[kingsquare]&((~opponentattacks)&Bitboards[opposite]);
    int capturenumber = popcount(ourcaptures);
    int movenumber;
    for (int i = 0; i < capturenumber; i++) {
        int capturesquare = popcount((ourcaptures & -ourcaptures)-1);
        int notation = kingsquare | (capturesquare << 6);
        notation |= (color << 12);
        notation |= (7 << 13);
        int captured = 0;
        for (int j = 2; j < 7; j++) {
            if ((1ULL << capturesquare)&(Bitboards[opposite]&Bitboards[j])) {
                captured = j;
            }
        }
        notation |= (1 << 16);
        notation |= (captured << 17);
        moves[depth][movecount] = notation;
        movescore[depth][movecount] = 3000+10000*captured+historytable[color][5][capturesquare];
        movecount++;
        ourcaptures^=(1ULL << capturesquare);
    }
    if (!capturesonly) {
        ourmoves = KingAttacks[kingsquare]&((~opponentattacks)&(~preoccupied));
        movenumber = popcount(ourmoves);
        for (int i = 0; i < movenumber; i++) {
            int movesquare = popcount((ourmoves & -ourmoves)-1);
            int notation = kingsquare | (movesquare << 6);
            notation |= (color << 12);
            notation |= (7 << 13);
            moves[depth][movecount] = notation;
            movescore[depth][movecount] = historytable[color][5][movesquare];
            movecount++;
            ourmoves^=(1ULL << movesquare);
        }
    }
    U64 checks = checkers(color);
    if (popcount(checks) > 1) {
        return movecount;
    }
    else if (checks) {
        checkmask |= checks;
    }
    else {
        checkmask = ~(0ULL);
    }
    U64 ourpawns = Bitboards[color]&Bitboards[2];
    U64 ourknights = Bitboards[color]&Bitboards[3];
    U64 ourbishops = Bitboards[color]&Bitboards[4];
    U64 ourrooks = Bitboards[color]&Bitboards[5];
    U64 ourqueens = Bitboards[color]&Bitboards[6];
    pawncount = popcount(ourpawns);
    knightcount = popcount(ourknights);
    bishopcount = popcount(ourbishops);
    rookcount = popcount(ourrooks);
    queencount = popcount(ourqueens);
    for (int i = 0; i < pawncount; i++) {
        int pawnsquare = popcount((ourpawns & -ourpawns)-1);
        int epsquare = (position >> 8)&63;
        U64 pinmask = ~(0ULL);
        if (pinnedpieces&(1ULL << pawnsquare)) {
            int pawnrank = pawnsquare&56;
            int pawnfile = pawnsquare&7;
            if (pawnrank == pinrank) {
                pinmask = GetRankAttacks(preoccupied, pawnsquare);
            }
            else if (pawnfile == pinfile) {
                pinmask = FileAttacks(preoccupied, pawnsquare);
            }
            else if ((pawnfile-pinfile)*(pawnrank-pinrank)>0) {
                pinmask = DiagAttacks(preoccupied, pawnsquare);
            }
            else {
                pinmask = AntiAttacks(preoccupied, pawnsquare);
            }
        }
        ourcaptures = PawnAttacks[color][pawnsquare]&(Bitboards[opposite]|(((1ULL<<epsquare)>>1)<<1));
        int eptake;
        if (color == 0) {
            eptake = epsquare-8;
        }
        else {
            eptake = epsquare+8;
        }
        U64 effectivemask = checkmask;
        if (checkmask&(1ULL << eptake)) {
            effectivemask |= (1ULL << epsquare);
        }
        ourcaptures &= (pinmask&effectivemask);
        int capturenumber = popcount(ourcaptures);
        for (int j = 0; j < capturenumber; j++) {
            int capturesquare = popcount((ourcaptures & -ourcaptures)-1);
            int notation = pawnsquare | (capturesquare << 6);
            notation |= (color << 12);
            notation |= (2 << 13);
            int captured = 0;
            bool legal = true;
            for (int j = 2; j < 7; j++) {
                if ((1ULL << capturesquare)&(Bitboards[opposite]&Bitboards[j])) {
                    captured = j;
                }
            }
            if (captured > 0) {
                notation |= (1 << 16);
                notation |= (captured << 17);
            }
            else {
                notation |= (1 << 25);
                if (GetRankAttacks((preoccupied^((1ULL << eptake)|(1ULL << pawnsquare))), kingsquare)&(Bitboards[opposite]&(Bitboards[5]|Bitboards[6]))) {
                    legal = false;
                }
            }
            if (((color==0)&&(capturesquare&56)==56)||((color==1)&&(capturesquare&56)==0)) {
                for (int k = 3; k >= 0; k--) {
                    moves[depth][movecount]=notation|((1 << 20)|(k << 21));
                    movescore[depth][movecount] = (k+6+captured)*10000+historytable[color][0][capturesquare];
                    movecount++;
                }
            }
            else if (legal) {
                moves[depth][movecount] = notation;
                movescore[depth][movecount] = 8000+captured*10000+historytable[color][0][capturesquare];
                movecount++;
            }
            ourcaptures^=(1ULL << capturesquare);
        }
        if (!capturesonly) {
            ourmoves = PawnMoves(preoccupied, pawnsquare, color);
            ourmoves &= (pinmask&checkmask);
            int movenumber = popcount(ourmoves);
            for (int j = 0; j < movenumber; j++) {
                int movesquare = popcount((ourmoves & -ourmoves)-1);
                int notation = pawnsquare | (movesquare << 6);
                notation |= (color << 12);
                notation |= (2 << 13);
                if ((movesquare-pawnsquare==16 && color==0)||(pawnsquare-movesquare==16 && color==1)) {
                    notation |= (1 << 24);
                }
                if (((color==0)&&(movesquare&56)==56)||((color==1)&&(movesquare&56)==0)) {
                    for (int k = 3; k >= 0; k--) {
                        moves[depth][movecount]=notation|((1 << 20)|(k << 21));
                        movescore[depth][movecount] = (k+6)*10000+historytable[color][0][movesquare];
                        movecount++;
                    }
                }
                else {
                    moves[depth][movecount]=notation;
                    movescore[depth][movecount] = historytable[color][0][movesquare];
                    movecount++;
                }
                ourmoves^=(1ULL << movesquare);
            }
        }
        ourpawns^=(1ULL << pawnsquare);
    }
    for (int i = 0; i < knightcount; i++) {
        int knightsquare = popcount((ourknights & -ourknights)-1);
        U64 pinmask = ~(0ULL);
        if (pinnedpieces&(1ULL << knightsquare)) {
            int knightrank = knightsquare&56;
            int knightfile = knightsquare&7;
            if (knightrank == pinrank) {
                pinmask = GetRankAttacks(preoccupied, knightsquare);
            }
            else if (knightfile == pinfile) {
                pinmask = FileAttacks(preoccupied, knightsquare);
            }
            else if ((knightfile-pinfile)*(knightrank-pinrank)>0) {
                pinmask = DiagAttacks(preoccupied, knightsquare);
            }
            else {
                pinmask = AntiAttacks(preoccupied, knightsquare);
            }
        }
        ourmask = KnightAttacks[knightsquare];
        ourmask &= (pinmask&checkmask);
        ourcaptures = ourmask&Bitboards[opposite];
        int capturenumber = popcount(ourcaptures);
        for (int j = 0; j < capturenumber; j++) {
            int capturesquare = popcount((ourcaptures & -ourcaptures)-1);
            int notation = knightsquare | (capturesquare << 6);
            notation |= (color << 12);
            notation |= (3 << 13);
            int captured = 0;
            for (int j = 2; j < 7; j++) {
                if ((1ULL << capturesquare)&(Bitboards[opposite]&Bitboards[j])) {
                    captured = j;
                }
            }
            notation |= (1 << 16);
            notation |= (captured << 17);
            moves[depth][movecount] = notation;
            movescore[depth][movecount] = 7000+captured*10000+historytable[color][1][capturesquare];
            movecount++;
            ourcaptures^=(1ULL << capturesquare);
        }
        if (!capturesonly) {
            ourmoves = ourmask&(~preoccupied);
            int movenumber = popcount(ourmoves);
            for (int j = 0; j < movenumber; j++) {
                int movesquare = popcount((ourmoves & -ourmoves)-1);
                int notation = knightsquare | (movesquare << 6);
                notation |= (color << 12);
                notation |= (3 << 13);
                moves[depth][movecount]=notation;
                movescore[depth][movecount] = historytable[color][1][movesquare];
                movecount++;
                ourmoves^=(1ULL << movesquare);
            }
        }
        ourknights^=(1ULL << knightsquare);
    }
    for (int i = 0; i < bishopcount; i++) {
        int bishopsquare = popcount((ourbishops & -ourbishops)-1);
        U64 pinmask = ~(0ULL);
        if (pinnedpieces&(1ULL << bishopsquare)) {
            int bishoprank = bishopsquare&56;
            int bishopfile = bishopsquare&7;
            if (bishoprank == pinrank) {
                pinmask = GetRankAttacks(preoccupied, bishopsquare);
            }
            else if (bishopfile == pinfile) {
                pinmask = FileAttacks(preoccupied, bishopsquare);
            }
            else if ((bishopfile-pinfile)*(bishoprank-pinrank)>0) {
                pinmask = DiagAttacks(preoccupied, bishopsquare);
            }
            else {
                pinmask = AntiAttacks(preoccupied, bishopsquare);
            }
        }
        ourmask = (DiagAttacks(preoccupied, bishopsquare)|AntiAttacks(preoccupied, bishopsquare));
        ourmask &= (pinmask&checkmask);
        ourcaptures = ourmask&Bitboards[opposite];
        int capturenumber = popcount(ourcaptures);
        for (int j = 0; j < capturenumber; j++) {
            int capturesquare = popcount((ourcaptures & -ourcaptures)-1);
            int notation = bishopsquare | (capturesquare << 6);
            notation |= (color << 12);
            notation |= (4 << 13);
            int captured = 0;
            for (int j = 2; j < 7; j++) {
                if ((1ULL << capturesquare)&(Bitboards[opposite]&Bitboards[j])) {
                    captured = j;
                }
            }
            notation |= (1 << 16);
            notation |= (captured << 17);
            moves[depth][movecount] = notation;
            movescore[depth][movecount] = 6000+captured*10000+historytable[color][2][capturesquare];
            movecount++;
            ourcaptures^=(1ULL << capturesquare);
        }
        if (!capturesonly) {
            ourmoves = ourmask&(~preoccupied);
            int movenumber = popcount(ourmoves);
            for (int j = 0; j < movenumber; j++) {
                int movesquare = popcount((ourmoves & -ourmoves)-1);
                int notation = bishopsquare | (movesquare << 6);
                notation |= (color << 12);
                notation |= (4 << 13);
                moves[depth][movecount]=notation;
                movescore[depth][movecount] = historytable[color][2][movesquare];
                movecount++;
                ourmoves^=(1ULL << movesquare);
            }
        }
        ourbishops^=(1ULL << bishopsquare);
    }
    for (int i = 0; i < rookcount; i++) {
        int rooksquare = popcount((ourrooks & -ourrooks)-1);
        U64 pinmask = ~(0ULL);
        if (pinnedpieces&(1ULL << rooksquare)) {
            int rookrank = rooksquare&56;
            int rookfile = rooksquare&7;
            if (rookrank == pinrank) {
                pinmask = GetRankAttacks(preoccupied, rooksquare);
            }
            else if (rookfile == pinfile) {
                pinmask = FileAttacks(preoccupied, rooksquare);
            }
            else if ((rookfile-pinfile)*(rookrank-pinrank)>0) {
                pinmask = DiagAttacks(preoccupied, rooksquare);
            }
            else {
                pinmask = AntiAttacks(preoccupied, rooksquare);
            }
        }
        ourmask = (GetRankAttacks(preoccupied, rooksquare)|FileAttacks(preoccupied, rooksquare));
        ourmask &= (pinmask&checkmask);
        ourcaptures = ourmask&Bitboards[opposite];
        int capturenumber = popcount(ourcaptures);
        for (int j = 0; j < capturenumber; j++) {
            int capturesquare = popcount((ourcaptures & -ourcaptures)-1);
            int notation = rooksquare | (capturesquare << 6);
            notation |= (color << 12);
            notation |= (5 << 13);
            int captured = 0;
            for (int j = 2; j < 7; j++) {
                if ((1ULL << capturesquare)&(Bitboards[opposite]&Bitboards[j])) {
                    captured = j;
                }
            }
            notation |= (1 << 16);
            notation |= (captured << 17);
            moves[depth][movecount] = notation;
            movescore[depth][movecount] = 5000+captured*10000+historytable[color][3][capturesquare];
            movecount++;
            ourcaptures^=(1ULL << capturesquare);
        }
        if (!capturesonly) {
            ourmoves = ourmask&(~preoccupied);
            int movenumber = popcount(ourmoves);
            for (int j = 0; j < movenumber; j++) {
                int movesquare = popcount((ourmoves & -ourmoves)-1);
                int notation = rooksquare | (movesquare << 6);
                notation |= (color << 12);
                notation |= (5 << 13);
                moves[depth][movecount]=notation;
                movescore[depth][movecount] = historytable[color][3][movesquare];
                movecount++;
                ourmoves^=(1ULL << movesquare);
            }
        }
        ourrooks^=(1ULL << rooksquare);
    }
    for (int i = 0; i < queencount; i++) {
        int queensquare = popcount((ourqueens & -ourqueens)-1);
        U64 pinmask = ~(0ULL);
        if (pinnedpieces&(1ULL << queensquare)) {
            int queenrank = queensquare&56;
            int queenfile = queensquare&7;
            if (queenrank == pinrank) {
                pinmask = GetRankAttacks(preoccupied, queensquare);
            }
            else if (queenfile == pinfile) {
                pinmask = FileAttacks(preoccupied, queensquare);
            }
            else if ((queenfile-pinfile)*(queenrank-pinrank)>0) {
                pinmask = DiagAttacks(preoccupied, queensquare);
            }
            else {
                pinmask = AntiAttacks(preoccupied, queensquare);
            }
        }
        ourmask = (GetRankAttacks(preoccupied, queensquare)|FileAttacks(preoccupied, queensquare));
        ourmask |= (DiagAttacks(preoccupied, queensquare)|AntiAttacks(preoccupied, queensquare));
        ourmask &= (pinmask&checkmask);
        ourcaptures = ourmask&Bitboards[opposite];
        int capturenumber = popcount(ourcaptures);
        for (int j = 0; j < capturenumber; j++) {
            int capturesquare = popcount((ourcaptures & -ourcaptures)-1);
            int notation = queensquare | (capturesquare << 6);
            notation |= (color << 12);
            notation |= (6 << 13);
            int captured = 0;
            for (int j = 2; j < 7; j++) {
                if ((1ULL << capturesquare)&(Bitboards[opposite]&Bitboards[j])) {
                    captured = j;
                }
            }
            notation |= (1 << 16);
            notation |= (captured << 17);
            moves[depth][movecount] = notation;
            movescore[depth][movecount] = 4000+captured*10000+historytable[color][4][capturesquare];
            movecount++;
            ourcaptures^=(1ULL << capturesquare);
        }
        if (!capturesonly) {
            ourmoves = ourmask&(~preoccupied);
            int movenumber = popcount(ourmoves);
            for (int j = 0; j < movenumber; j++) {
                int movesquare = popcount((ourmoves & -ourmoves)-1);
                int notation = queensquare | (movesquare << 6);
                notation |= (color << 12);
                notation |= (6 << 13);
                moves[depth][movecount]=notation;
                movescore[depth][movecount] = historytable[color][4][movesquare];
                movecount++;
                ourmoves^=(1ULL << movesquare);
            }
        }
        ourqueens^=(1ULL << queensquare);
    }
    if (position&(1 << (14+2*color))) {
        if (!((opponentattacks|occupied)&((1ULL << (kingsquare+3))-(1ULL << kingsquare)))) {
            int notation = kingsquare | ((kingsquare+2) << 6);
            notation |= (color << 12);
            notation |= (7 << 13);
            notation |= (1 << 23);
            moves[depth][movecount]=notation;
            movescore[depth][movecount] = historytable[color][5][kingsquare+2];
            movecount++;
        }
    }
    if (position&(1 << (15+2*color))) {
        if (!(((opponentattacks)&((1ULL << (kingsquare+1))-(1ULL << (kingsquare-2))))||(occupied&((1ULL << kingsquare)-(1ULL << (kingsquare-3)))))) {
            int notation = kingsquare | ((kingsquare-2) << 6);
            notation |= (color << 12);
            notation |= (7 << 13);
            notation |= (1 << 23);
            moves[depth][movecount]=notation;
            movescore[depth][movecount] = historytable[color][5][kingsquare-2];
            movecount++;
        }
    }
    return movecount;
}
string algebraic(int notation) {
    string convert[64] = { "a1", "b1", "c1", "d1", "e1", "f1", "g1", "h1", "a2", "b2", "c2", "d2", "e2", "f2", "g2", "h2",
    "a3", "b3", "c3", "d3", "e3", "f3", "g3", "h3", "a4", "b4", "c4", "d4", "e4", "f4", "g4", "h4", "a5", "b5", "c5", "d5", "e5", "f5", "g5", "h5",
    "a6", "b6", "c6", "d6", "e6", "f6", "g6", "h6","a7", "b7", "c7", "d7", "e7", "f7", "g7", "h7", "a8", "b8", "c8", "d8", "e8", "f8", "g8", "h8"};
    string header = convert[notation&63]+convert[(notation>>6)&63];
    if (notation&(1 << 20)) {
        int piece = (notation>>21)&3;
        if (piece == 0) {
            header = header+"n";
        }
        else if (piece == 1) {
            header = header+"b";
        }
        else if (piece == 2) {
            header = header+"r";
        }
        else {
            header = header+"q";
        }
    }
    return header;
}
U64 perft(int depth, int initialdepth, int color) {
    int movcount = generatemoves(color, 0, depth);
    U64 ans = 0;
    if (depth > 1) {
        for (int i = 0; i < movcount; i++) {
            makemove(moves[depth][i], true);
            if (depth == initialdepth) {
                cout << algebraic(moves[depth][i]);
                cout << ": ";
            }
            ans+=perft(depth-1, initialdepth, color^1);
            unmakemove(moves[depth][i]);
        }
        if (depth == initialdepth-1) {
            cout << ans << " ";
        }
        if (depth == initialdepth) {
            cout << "\n" << ans << "\n";
            auto finish = chrono::steady_clock::now();
            auto diff = chrono::duration_cast<chrono::milliseconds>(finish-start);
            int nps = 1000*(ans/diff.count());
            cout << "nps " << nps << "\n";
        }
        return ans;
    }
    else {
        if (initialdepth == 2) {
            cout << movcount << " ";
        }
        return movcount;
    }
}
U64 perftnobulk(int depth, int initialdepth, int color) {
    int movcount = generatemoves(color, 0, depth);
    U64 ans = 0;
    for (int i = 0; i < movcount; i++) {
        makemove(moves[depth][i], true);
        if (depth == initialdepth) {
            cout << algebraic(moves[depth][i]);
            cout << ": ";
        }
        if (depth>1) {
            ans+=perftnobulk(depth-1, initialdepth, color^1);
        }
        else {
            ans++;
        }
        unmakemove(moves[depth][i]);
    }
    if (depth == initialdepth-1) {
        cout << ans << " ";
    }
    if (depth == initialdepth) {
        cout << "\n" << ans << "\n";
        auto finish = chrono::steady_clock::now();
        auto diff = chrono::duration_cast<chrono::milliseconds>(finish-start);
        int nps = 1000*(ans/diff.count());
        cout << "nps " << nps << "\n";
    }
    return ans;
}
void parseFEN(string FEN) {
    gamelength = 0;
    last = 0;
    root = 0;
    gamephase[0] = 0;
    gamephase[1] = 0;
    evalm[0] = 0;
    evalm[1] = 0;
    evale[0] = 0;
    evale[1] = 0;
    int order[64] = {56, 57, 58, 59, 60, 61, 62, 63, 48, 49, 50, 51, 52, 53, 54, 55, 40, 41, 42, 43, 44, 45, 46, 47,
    32, 33, 34, 35, 36, 37, 38, 39, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23,
    8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7};
    char file[8] = {'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h'};
    int progress = 0;
    for (int i = 0; i < 8; i++) {
        Bitboards[i] = 0ULL;
    }
    int tracker = 0;
    int castling = 0;
    int color = 0;
    while (FEN[tracker]!=' ') {
        char hm = FEN[tracker];
        if ('0' <= hm && hm <= '9') {
            int repeat = (int)hm-48;
            progress+=repeat;
        }
        if ('A'<= hm && hm <= 'Z') {
            Bitboards[0]|=(1ULL << order[progress]);
            if (hm == 'P') {
                Bitboards[2] |= (1ULL << order[progress]);
                evalm[0]+=materialm[0];
                evale[0]+=materiale[0];
                evalm[0]+=pstm[0][order[progress]];
                evale[0]+=pste[0][order[progress]];
            }
            if (hm == 'N') {
                Bitboards[3] |= (1ULL << order[progress]);
                evalm[0]+=materialm[1];
                evale[0]+=materiale[1];
                evalm[0]+=pstm[1][order[progress]];
                evale[0]+=pste[1][order[progress]];
                gamephase[0]+=1;
            }
            if (hm == 'B') {
                Bitboards[4] |= (1ULL << order[progress]);
                evalm[0]+=materialm[2];
                evale[0]+=materiale[2];
                evalm[0]+=pstm[2][order[progress]];
                evale[0]+=pste[2][order[progress]];
                gamephase[0]+=1;
            }
            if (hm == 'R') {
                Bitboards[5] |= (1ULL << order[progress]);
                evalm[0]+=materialm[3];
                evale[0]+=materiale[3];
                evalm[0]+=pstm[3][order[progress]];
                evale[0]+=pste[3][order[progress]];
                gamephase[0]+=2;
            }
            if (hm == 'Q') {
                Bitboards[6] |= (1ULL << order[progress]);
                evalm[0]+=materialm[4];
                evale[0]+=materiale[4];
                evalm[0]+=pstm[4][order[progress]];
                evale[0]+=pste[4][order[progress]];
                gamephase[0]+=4;
            }
            if (hm == 'K') {
                Bitboards[7] |= (1ULL << order[progress]);
                evalm[0]+=pstm[5][order[progress]];
                evale[0]+=pste[5][order[progress]];
            }
            progress++;
        }
        if ('a'<= hm && hm <= 'z') {
            Bitboards[1]|=(1ULL << order[progress]);
            if (hm == 'p') {
                Bitboards[2] |= (1ULL << order[progress]);
                evalm[1]+=materialm[0];
                evale[1]+=materiale[0];
                evalm[1]+=pstm[0][56^order[progress]];
                evale[1]+=pste[0][56^order[progress]];
            }
            if (hm == 'n') {
                Bitboards[3] |= (1ULL << order[progress]);
                evalm[1]+=materialm[1];
                evale[1]+=materiale[1];
                evalm[1]+=pstm[1][56^order[progress]];
                evale[1]+=pste[1][56^order[progress]];
                gamephase[1]+=1;
            }
            if (hm == 'b') {
                Bitboards[4] |= (1ULL << order[progress]);
                evalm[1]+=materialm[2];
                evale[1]+=materiale[2];
                evalm[1]+=pstm[2][56^order[progress]];
                evale[1]+=pste[2][56^order[progress]];
                gamephase[1]+=1;
            }
            if (hm == 'r') {
                Bitboards[5] |= (1ULL << order[progress]);
                evalm[1]+=materialm[3];
                evale[1]+=materiale[3];
                evalm[1]+=pstm[3][56^order[progress]];
                evale[1]+=pste[3][56^order[progress]];
                gamephase[1]+=2;
            }
            if (hm == 'q') {
                Bitboards[6] |= (1ULL << order[progress]);
                evalm[1]+=materialm[4];
                evale[1]+=materiale[4];
                evalm[1]+=pstm[4][56^order[progress]];
                evale[1]+=pste[4][56^order[progress]];
                gamephase[1]+=4;
            }
            if (hm == 'k') {
                Bitboards[7] |= (1ULL << order[progress]);
                evalm[1]+=pstm[5][56^order[progress]];
                evale[1]+=pste[5][56^order[progress]];
            }
            progress++;
        }
        tracker++;
    }
    while (FEN[tracker] == ' ') {
        tracker++;
    }
    if (FEN[tracker] == 'b') {
        color = 1;
    }
    position = color;
    tracker+=2;
    while (FEN[tracker]!=' ') {
        char hm = FEN[tracker];
        if (hm == 'K') {
            castling |= 1;
        }
        if (hm == 'Q') {
            castling |= 2;
        }
        if (hm == 'k') {
            castling |= 4;
        }
        if (hm == 'q') {
            castling |= 8;
        }
        tracker++;
    }
    tracker++;
    position |= (castling << 14);
    if (FEN[tracker] == '-') {
        tracker+=2;
    }
    else {
        int epfile = 0;
        for (int j = 0; j < 8; j++) {
            if (file[j] == FEN[tracker]) {
                epfile = j;
            }
        }
        tracker++;
        int eprank = (int)(FEN[tracker])-49;
        int epsquare = 8*eprank+epfile;
        position |= (epsquare << 8);
        tracker+=2;
    }
    int halfmove = (int)(FEN[tracker])-48;
    tracker++;
    if (FEN[tracker]!=' ') {
        halfmove = 10*halfmove+(int)(FEN[tracker])-48;
    }
    position |= (halfmove << 1);
    zobristhash = scratchzobrist();
    zobrist[0] = zobristhash;
    history[0] = position;
}
void readnnuefile(string file) {
    ifstream nnueweights;
    nnueweights.open(file, ifstream::binary);
    /*char *header = new char[64];
    nnueweights.read(header, 64);
    delete[] header;*/
    for (int i = 0; i < 768; i++) {
        int piece = i / 64;
        int square = i % 64;
        for (int j = 0; j < nnuesize; j++) {
            char *weights = new char[2];
            nnueweights.read(weights, 2);
            short int weight = 256*(short int)(weights[1])+(short int)(unsigned char)(weights[0]);
            nnuelayer1[64 * piece + square][j] = weight;
            delete[] weights;
        }
    }
    for (int i = 0; i < nnuesize; i++) {
        char *biases = new char[2];
        nnueweights.read(biases, 2);
        short int bias = 256*(short int)(biases[1])+(short int)(unsigned char)(biases[0]);
        layer1bias[i] = bias;
        delete[] biases;
    }
    for (int i = 0; i < nnuesize; i++) {
        char *weights = new char[2];
        nnueweights.read(weights, 2);
        short int weight = 256*(short int)(weights[1])+(short int)(unsigned char)(weights[0]);
        ourlayer2[i] = (int)weight;
        delete[] weights;
    }
    for (int i = 0; i < nnuesize; i++) {
        char *weights = new char[2];
        nnueweights.read(weights, 2);
        short int weight = 256*(short int)(weights[1])+(short int)(unsigned char)(weights[0]);
        theirlayer2[i] = (int)weight;
        delete[] weights;
    }
    char *bases = new char[2];
    nnueweights.read(bases, 2);
    short int base = 256*(short int)(bases[1])+(short int)(unsigned char)(bases[0]);
    finalbias = (int)base;
    delete[] bases;
    nnueweights.close();
}
void activatepiece(int color, int piece, int square) {
    for (int i = 0; i < nnuesize; i++) {
        whitehidden[i] += nnuelayer1[64*(6*color+piece)+square][i];
        blackhidden[i] += nnuelayer1[64*(6*(color^1)+piece)+56^square][i];
    }
}
void deactivatepiece(int color, int piece, int square) {
    for (int i = 0; i < nnuesize; i++) {
        whitehidden[i] -= nnuelayer1[64*(6*color+piece)+square][i];
        blackhidden[i] -= nnuelayer1[64*(6*(color^1)+piece)+56^square][i];
    }
}
void initializennue() {
    for (int i = 0; i < nnuesize; i++) {
        whitehidden[i] = layer1bias[i];
        blackhidden[i] = layer1bias[i];
    }
    for (int i = 0; i < 12; i++) {
        U64 pieces = (Bitboards[i/6] & Bitboards[2+(i%6)]);
        int piececount = popcount(pieces);
        for (int j = 0; j < piececount; j++) {
            int square = popcount((pieces & -pieces) - 1);
            activatepiece(i/6, i%6, square);
            pieces ^= (1ULL<<square);
        }
    }
}
void forwardaccumulators(int notation) {
    int from = notation & 63;
    int to = (notation >> 6) & 63;
    int color = (notation >> 12) & 1;
    int piece = (notation >> 13) & 7;
    int epcapture = (notation >> 25) & 1;
    int captured = epcapture ? 2 : ((notation >> 17) & 7);
    int promoted = (notation >> 21) & 3;
    int castling = (notation >> 23) & 1;
    int from1 = (to&4) ? to+1 : to-2;
    int to1 = (to&4) ? to-1 : to+1;
    int to2 = epcapture ? (to+16*color-8) : to;
    int piece2 = (promoted > 0) ? promoted + 1 : piece - 2;
    activatepiece(color, piece2, to);
    deactivatepiece(color, piece-2, from);
    if (captured > 0) {
        deactivatepiece(color^1, captured-2, to2);
    }
    if (castling > 0) {
        activatepiece(color, 3, to1);
        deactivatepiece(color, 3, from1);
    }
}
void backwardaccumulators(int notation) {
    int from = notation & 63;
    int to = (notation >> 6) & 63;
    int color = (notation >> 12) & 1;
    int piece = (notation >> 13) & 7;
    int captured = (notation >> 17) & 7;
    int promoted = (notation >> 21) & 3;
    int epcapture = (notation >> 25) & 1;
    int castling = (notation >> 23) & 1;
    int from1 = to-2;
    int to1 = to+1;
    int to2 = to;
    if (to&4) {
        from1 = to+1;
        to1 = to-1;
    }
    if (epcapture) {
        captured = 2;
        to2 = to+16*color-8;
    }
    int piece2 = (promoted > 0) ? promoted + 1 : piece - 2;
    deactivatepiece(color, piece2, to);
    activatepiece(color, piece-2, from);
    if (captured > 0) {
        activatepiece(color^1, captured-2, to2);
    }
    if (castling > 0) {
        deactivatepiece(color, 3, to1);
        activatepiece(color, 3, from1);
    }
}
int evalnnue(int color) {
    int eval = finalbias * evalQA;
    if (color == 0) {
        for (int i = 0; i < nnuesize; i++) {
            eval += screlu(whitehidden[i]) * ourlayer2[i];
            eval += screlu(blackhidden[i]) * theirlayer2[i];
        }
    } else {
        for (int i = 0; i < nnuesize; i++) {
            eval += screlu(whitehidden[i]) * theirlayer2[i];
            eval += screlu(blackhidden[i]) * ourlayer2[i];
        }
    }
    eval /= evalQA;
    eval *= evalscale;
    eval /= (evalQA * evalQB);
    return eval;
}
int evaluate(int color) {
    int midphase = min(24, gamephase[0]+gamephase[1]);
    int endphase = 24-midphase;
    int mideval = evalm[color]-evalm[color^1];
    int endeval = evale[color]-evale[color^1];
    int bishops = 37*(popcount(Bitboards[color]&Bitboards[4])/2-popcount(Bitboards[color^1]&Bitboards[4])/2);
    int e = (min(gamephase[0], gamephase[1]) == 0) ? 2 : 1;
    return (mideval*midphase+e*endeval*endphase)/24+bishops+11;
}
bool see_exceeds(int move, int color, int threshold) {
    int see_values[6] = {10, 30, 30, 50, 90, 20000};
    int target = (move >> 6) & 63;
    int victim = (move >> 17) & 7;
    int attacker = (move >> 13) & 7;
    int value = (victim > 0) ? see_values[victim - 2] - threshold : -threshold;
    if (value < 0) {
        return false;
    }
    if (value - see_values[attacker - 2] >= 0) {
        return true;
    }
    int pieces[2][6] = {{0, 0, 0, 0, 0, 0}, {0, 0, 0, 0, 0, 0}};
    U64 occupied = Bitboards[0] | Bitboards[1];
    U64 to = (1ULL<<target);
    U64 from = (1ULL<<(move&63));
    U64 us = Bitboards[color];
    U64 enemy = Bitboards[color^1];
    U64 knights = KnightAttacks[target]&Bitboards[3];
    U64 kings = KingAttacks[target]&Bitboards[7];
    pieces[0][0] = popcount((PawnAttacks[color][target]&Bitboards[2]&enemy));
    pieces[1][0] = popcount((PawnAttacks[color^1][target]&Bitboards[2]&us));
    pieces[0][1] = popcount(knights&enemy);
    pieces[1][1] = popcount(knights&us);
    pieces[0][5] = popcount(kings&enemy);
    pieces[1][5] = popcount(kings&us);
    occupied ^= (enemy&Bitboards[5]);
    occupied |= to;
    occupied &= (~from);
    pieces[0][3] = popcount((FileAttacks(occupied,target)|GetRankAttacks(occupied,target))&Bitboards[5]&enemy);
    occupied ^= (Bitboards[5]);
    occupied |= to;
    occupied &= (~from);
    pieces[1][3] = popcount((FileAttacks(occupied,target)|GetRankAttacks(occupied,target))&Bitboards[5]&us);
    occupied ^= (us&(Bitboards[5]|Bitboards[2]|Bitboards[4]));
    occupied |= to;
    occupied &= (~from);
    pieces[1][2] = popcount((DiagAttacks(occupied,target)|AntiAttacks(occupied,target))&Bitboards[4]&us);
    occupied ^= (Bitboards[4]|Bitboards[2]);
    occupied |= to;
    occupied &= (~from);
    pieces[0][2] = popcount((DiagAttacks(occupied,target)|AntiAttacks(occupied,target))&Bitboards[4]&enemy);
    occupied ^= (enemy&(Bitboards[5]|Bitboards[6]));
    occupied |= to;
    occupied &= (~from);
    pieces[0][4] += popcount((FileAttacks(occupied,target)|GetRankAttacks(occupied,target))&Bitboards[6]&enemy);
    occupied ^= (enemy&(Bitboards[2]|Bitboards[4]|Bitboards[5]));
    occupied |= to;
    occupied &= (~from);
    pieces[0][4] += popcount((DiagAttacks(occupied,target)|AntiAttacks(occupied,target))&Bitboards[6]&enemy);
    occupied ^= (Bitboards[2]|Bitboards[4]|Bitboards[6]);
    occupied |= to;
    occupied &= (~from);
    pieces[1][4] += popcount((DiagAttacks(occupied,target)|AntiAttacks(occupied,target))&Bitboards[6]&us);
    occupied ^= (us&(Bitboards[2]|Bitboards[4]|Bitboards[5]));
    occupied |= to;
    occupied &= (~from);
    pieces[1][4] += popcount((FileAttacks(occupied,target)|GetRankAttacks(occupied,target))&Bitboards[6]&us);
    if (attacker > 2) {
      pieces[1][attacker - 2]--;
    }
    int next[2] = {0, 0};
    int previous[2] = {0, attacker - 2};
    int i = 0;
    while (true) {
        while (pieces[i][next[i]] == 0 && next[i] < 6) {
            next[i]++;
        }
        if (next[i] > 5) {
            return (value >= 0);
        }
        value += (2 * i - 1) * see_values[previous[i ^ 1]];
        if ((2 * i - 1) * (value + (1 - 2 * i) * see_values[next[i]]) >= 1 - i) {
            return i;
        }
        previous[i] = next[i];
        pieces[i][next[i]]--;
        i ^= 1;
    }
}
int quiesce(int alpha, int beta, int color, int depth) {
    int score = useNNUE ? evalnnue(color) : evaluate(color);
    int bestscore = -30000;
    int movcount;
    if (depth > 4) {
        return score;
    }
    bool incheck = checkers(color);
    if (incheck) {
        movcount = generatemoves(color, 0, maxdepth+depth);
        if (movcount == 0) {
            return -27000;
        }
    }
    else {
        bestscore = score;
        if (alpha < score) {
            alpha = score;
        }
        if (score >= beta) {
            return score;
        }
        movcount = generatemoves(color, 1, maxdepth+depth);
    }
    if (depth < 4) {
        for (int i = 0; i < movcount; i++) {
            int j = i;
            while (j > 0 && movescore[maxdepth+depth][j] > movescore[maxdepth+depth][j-1]) {
                swap(moves[maxdepth+depth][j], moves[maxdepth+depth][j-1]);
                swap(movescore[maxdepth+depth][j], movescore[maxdepth+depth][j-1]);
                j--;
            }
        }
    }
    for (int i = 0; i < movcount; i++) {
        bool good = (incheck || see_exceeds(moves[maxdepth+depth][i], color, 0));
        if (good) {
            makemove(moves[maxdepth+depth][i], 1);
            if (useNNUE) {
                forwardaccumulators(moves[maxdepth+depth][i]);
            }
            score = -quiesce(-beta, -alpha, color^1, depth+1);
            unmakemove(moves[maxdepth+depth][i]);
            if (useNNUE) {
                backwardaccumulators(moves[maxdepth+depth][i]);
            }
            if (score >= beta) {
                return score;
            }
            if (score > alpha) {
                alpha = score;
            }
            if (score > bestscore) {
                bestscore = score;
            }
        }
    }
    return bestscore;
}
int alphabeta(int depth, int ply, int alpha, int beta, int color, bool nmp, int nodelimit, int timelimit) {
    if (repetitions() > 1) {
        return 0;
    }
    if (depth <= 0 || ply >= maxdepth) {
        return quiesce(alpha, beta, color, 0);
    }
    int score = -30000;
    int bestscore = -30000;
    int allnode = 0;
    int movcount;
    int index = zobristhash%TTsize;
    int ttmove = 0;
    int bestmove1 = -1;
    int ttdepth = TT[index].depth;
    int ttage = max(gamelength-TT[index].age, 0);
    bool update = (depth >= (ttdepth-ttage/3));
    bool isPV = (beta-alpha > 1);
    int staticeval = useNNUE ? evalnnue(color) : evaluate(color);
    bool incheck = (checkers(color) != 0ULL);
    searchstack[ply].incheck = incheck;
    searchstack[ply].eval = staticeval;
    bool improving = false;
    if (ply > 1) {
        improving = (staticeval > searchstack[ply-2].eval);
    }
    if (TT[index].key == zobristhash) {
        score = TT[index].score;
        ttmove = TT[index].hashmove;
        int nodetype = TT[index].nodetype;
        if (ttdepth >= depth) {
            if (!isPV && repetitions() == 0) {
                if (nodetype == 3) {
                    return score;
                }
                if ((nodetype&1)&&(score >= beta)) {
                    return score;
                }
                if ((nodetype&2)&&(score <= alpha)) {
                    return score;
                }
            }
        }
        else {
            int margin = 40+60*(depth-ttdepth);
            if ((nodetype&1) && (score-margin >= beta) && (abs(beta) < 27000) && !incheck && (ply > 0)) {
                return (score+beta)/2;
            }
        }
        staticeval = score;
    }
    int margin = 40+60*(depth);
    if (ply > 0 && score == -30000) {
        if (staticeval-margin >= beta && (abs(beta) < 27000) && !incheck) {
            return (staticeval+beta)/2;
        }
    }
    movcount = generatemoves(color, 0, ply);
    if (movcount == 0) {
        if (checkers(color)) {
            return -1*(28000-ply);
        }
        else {
            return 0;
        }
    }
    if ((!incheck && gamephase[color] > 0) && (depth > 1 && nmp) && (staticeval > beta)) {
        makenullmove();
        score = -alphabeta(depth-2-depth/3, ply+1, -beta, 1-beta, color^1, false, nodelimit, timelimit);
        unmakenullmove();
        if (score >= beta) {
            return beta;
        }
    }
    if (depth > 0) {
        for (int i = 0; i < movcount; i++) {
            int j = i;
            if (moves[ply][i] == ttmove) {
                movescore[ply][i] = (1 << 20);
            }
            if (moves[ply][i] == killers[ply][0]) {
                movescore[ply][i]+=20000;
            }
            if (moves[ply][i] == killers[ply][1]) {
                movescore[ply][i]+=10000;
            }
            while (j > 0 && movescore[ply][j] > movescore[ply][j-1]) {
                swap(moves[ply][j], moves[ply][j-1]);
                swap(movescore[ply][j], movescore[ply][j-1]);
                j--;
            }
        }
    }
    for (int i = 0; i < movcount; i++) {
        bool nullwindow = (i > 0);
        int r = (movescore[ply][i] < 30000) ? min(depth-1, lmr_reductions[depth][i]) : 0;
        r = max(0, r - (incheck || isPV) - movescore[ply][i]/16384);
        int e = (movcount == 1) ? 1 : 0;
        //bool prune = ((beta-alpha < 2) && (depth < 5) && (i > 6+4*depth) && movescore[depth][i] < 1000);
        if (!stopsearch) {
            makemove(moves[ply][i], true);
            if (useNNUE) {
                forwardaccumulators(moves[ply][i]);
            }
            if (nullwindow) {
                score = -alphabeta(depth-1-r, ply+1, -alpha-1, -alpha, color^1, true, nodelimit, timelimit);
                if (score > alpha && r > 0) {
                    score = -alphabeta(depth-1, ply+1, -alpha-1, -alpha, color^1, true, nodelimit, timelimit);
                }
                if (score > alpha && score < beta) {
                    score = -alphabeta(depth-1, ply+1, -beta, -alpha, color^1, true, nodelimit, timelimit);
                }
            }
            else {
                score = -alphabeta(depth-1+e, ply+1, -beta, -alpha, color^1, true, nodelimit, timelimit);
            }
            unmakemove(moves[ply][i]);
            if (useNNUE) {
                backwardaccumulators(moves[ply][i]);
            }
            if (score > bestscore) {
                if (score > alpha) {
                    if (score >= beta) {
                        if (update && !stopsearch && abs(score) < 29000) {
                            updatett(index, depth, score, 1, moves[ply][i]);
                        }
                        if ((((moves[ply][i]>>16)&1) == 0) && (killers[ply][0] != moves[ply][i])) {
                            killers[ply][1] = killers[ply][0];
                            killers[ply][0] = moves[ply][i];
                        }
                        int target = (moves[ply][i]>>6)&63;
                        int piece = (moves[ply][i]>>13)&7;
                        historytable[color][piece-2][target]+=(depth*depth*depth-(depth*depth*depth*historytable[color][piece-2][target])/27000);
                        return score;
                    }
                    alpha = score;
                    allnode = 1;
                }
                if (ply == 0) {
                    bestmove = moves[ply][i];
                }
                bestmove1 = i;
                bestscore = score;
            }
            if (nodecount > nodelimit) {
                stopsearch = true;
            }
            if (depth > 1) {
                auto now = chrono::steady_clock::now();
                auto timetaken = chrono::duration_cast<chrono::milliseconds>(now - start);
                if (timetaken.count() > timelimit) {
                    stopsearch = true;
                }
            }
        }
    }
    if (update && !stopsearch) {
        updatett(index, depth, bestscore, 2+allnode, moves[ply][bestmove1]);
    }
    return bestscore;
}
void iterative(int nodelimit, int softtimelimit, int hardtimelimit, int color) {
    nodecount = 0;
    stopsearch = false;
    start = chrono::steady_clock::now();
    int score = useNNUE ? evalnnue(color) : evaluate(color);
    int depth = 1;
    int bestmove1 = 0;
    int pvtable[maxdepth];
    resethistory();
    while (!stopsearch) {
        bestmove = -1;
        int delta = 30;
        int alpha = score-delta;
        int beta = score+delta;
        bool fail = true;
        while (fail) {
            int score1 = alphabeta(depth, 0, alpha, beta, color, false, nodelimit, hardtimelimit);
            if (score1 >= beta) {
                beta += delta;
                delta += delta;
            }
            else if (score1 <= alpha) {
                alpha -= delta;
                delta += delta;
            }
            else {
                score = score1;
                fail = false;
            }
        }
        auto now = chrono::steady_clock::now();
        auto timetaken = chrono::duration_cast<chrono::milliseconds>(now-start);
        if (nodecount < nodelimit && timetaken.count() < hardtimelimit && depth < maxdepth && bestmove >= 0) {
            int last = depth;
            int pvcolor = color;
            bool stop = false;
            for (int i = 0; i < depth; i++) {
                int index = zobristhash%TTsize;
                stop = true;
                if (TT[index].key == zobristhash && TT[index].nodetype == 3) {
                    int movcount = generatemoves(pvcolor, 0, 0);
                    for (int j = 0; j < movcount; j++) {
                        if (moves[0][j] == TT[index].hashmove) {
                            stop = false;
                        }
                    }
                }
                if (stop) {
                    last = i;
                    i = depth;
                }
                else {
                    pvcolor^=1;
                    pvtable[i] = TT[index].hashmove;
                    makemove(TT[index].hashmove, 1);
                }
            }
            for (int i = last-1; i >= 0; i--) {
                unmakemove(pvtable[i]);
            }
            if (proto == "uci") {
                if (abs(score) <= 27000) {
                    cout << "info depth " << depth << " nodes " << nodecount << " time " << timetaken.count() << " score cp " << score << " pv ";
                    for (int i = 0; i < last; i++) {
                        cout << algebraic(pvtable[i]) << " ";
                    }
                    cout << "\n";
                }
                else {
                    int matescore;
                    if (score > 0) {
                        matescore = 1+(28000-score)/2;
                    }
                    else {
                        matescore = (-28000-score)/2;
                    }
                    cout << "info depth " << depth << " nodes " << nodecount << " time " << timetaken.count() << " score mate " << matescore << " pv ";
                    for (int i = 0; i < last; i++) {
                        cout << algebraic(pvtable[i]) << " ";
                    }
                    cout << "\n";
                }
            }
            if (proto == "xboard") {
                cout << depth << " " << score << " " << timetaken.count()/10 << " " << nodecount << " ";
                for (int i=0; i < last; i++) {
                    cout << algebraic(pvtable[i]) << " ";
                }
                cout << "\n";
            }
            depth++;
            bestmove1 = bestmove;
        }
        else {
            stopsearch = true;
        }
        if (timetaken.count() > softtimelimit) {
            stopsearch = true;
        }
    }
    auto now = chrono::steady_clock::now();
    auto timetaken = chrono::duration_cast<chrono::milliseconds>(now-start);
    if (timetaken.count() > 0 && proto == "uci") {
        int nps = 1000*(nodecount/timetaken.count());
        cout << "info nodes " << nodecount << " nps " << nps << "\n";
    }
    if (proto == "uci") {
        cout << "bestmove " << algebraic(bestmove1) << "\n";
    }
    if (proto == "xboard") {
        cout << "move " << algebraic(bestmove1) << "\n";
        makemove(bestmove1, 0);
    }
}
void uci() {
    string ucicommand;
    getline(cin, ucicommand);
    if (ucicommand == "uci") {
        cout << "id name sscg13 chess engine \n" << "id author sscg13 \n" << "uciok\n";
    }
    if (ucicommand == "quit") {
        exit(0);
    }
    if (ucicommand == "isready") {
        cout << "readyok\n";
    }
    if (ucicommand == "ucinewgame") {
        initializett();
        initializeboard();
        if (useNNUE) {
            initializennue();
        }
    }
    if (ucicommand.substr(0, 17) == "position startpos") {
        initializeboard();
        int color = 0;
        string mov = "";
        for (int i = 24; i <= ucicommand.length(); i++) {
            if ((ucicommand[i]==' ') || (i == ucicommand.length())) {
                int len = generatemoves(color, 0, 0);
                int played = -1;
                for (int j = 0; j < len; j++) {
                    if (algebraic(moves[0][j])==mov) {
                        played = j;
                    }
                }
                if (played >= 0) {
                    makemove(moves[0][played], false);
                    color^=1;
                }
                mov = "";
            }
            else {
                mov+=ucicommand[i];
            }
        }
        if (useNNUE) {
            initializennue();
        }
    }
    if (ucicommand.substr(0, 12) == "position fen") {
        int reader = 13;
        while (ucicommand[reader]!='m' && reader < ucicommand.length()) {
            reader++;
        }
        string fen = ucicommand.substr(13, reader-12);
        parseFEN(fen);
        int color = position&1;
        string mov = "";
        for (int i = reader+6; i <= ucicommand.length(); i++) {
            if ((ucicommand[i]==' ') || (i == ucicommand.length())) {
                int len = generatemoves(color, 0, 0);
                int played = -1;
                for (int j = 0; j < len; j++) {
                    if (algebraic(moves[0][j])==mov) {
                        played = j;
                    }
                }
                if (played >= 0) {
                    makemove(moves[0][played], false);
                    color^=1;
                }
                mov = "";
            }
            else {
                mov+=ucicommand[i];
            }
        }
        if (useNNUE) {
            initializennue();
        }
    }
    if (ucicommand.substr(0, 8) == "go wtime") {
        int wtime;
        int btime;
        int winc = 0;
        int binc = 0;
        int sum;
        int add;
        int reader = 8;
        while (ucicommand[reader] != 'b') {
            reader++;
        }
        reader--;
        while (ucicommand[reader] == ' ') {
            reader--;
        }
        sum = 0;
        add = 1;
        while (ucicommand[reader] != ' ') {
            sum+=((int)(ucicommand[reader]-48))*add;
            add*=10;
            reader--;
        }
        if (sum < 100) {
            sum = 100;
        }
        wtime = sum;
        while (ucicommand[reader] != 'w' && reader < ucicommand.length()) {
            reader++;
        }
        reader--;
        while (ucicommand[reader] == ' ') {
            reader--;
        }
        sum = 0;
        add = 1;
        while (ucicommand[reader] != ' ') {
            sum+=((int)(ucicommand[reader]-48))*add;
            add*=10;
            reader--;
        }
        if (sum < 100) {
            sum = 100;
        }
        btime = sum;
        while (ucicommand[reader] != 'b' && reader < ucicommand.length()) {
            reader++;
        }
        reader--;
        while (ucicommand[reader] == ' ') {
            reader--;
        }
        if (reader < ucicommand.length()-1) {
            sum = 0;
            add = 1;
            while (ucicommand[reader] != ' ') {
                sum+=((int)(ucicommand[reader]-48))*add;
                add*=10;
                reader--;
            }
            winc = sum;
            reader = ucicommand.length()-1;
            while (ucicommand[reader] == ' ') {
                reader--;
            }
            sum = 0;
            add = 1;
            while (ucicommand[reader] != ' ') {
                sum+=((int)(ucicommand[reader]-48))*add;
                add*=10;
                reader--;
            }
            binc = sum;
        }
        int color = position&1;
        if (color == 0) {
            iterative(1000000000, wtime/40+winc/3, min(wtime/2, wtime/10+winc), 0);

        }
        else {
            iterative(1000000000, btime/40+binc/3, min(btime/2, btime/10+binc), 1);
        }
    }
    if (ucicommand.substr(0, 11) == "go movetime") {
        int sum = 0;
        int add = 1;
        int reader = ucicommand.length()-1;
        while (ucicommand[reader] != ' ') {
            sum+=((int)(ucicommand[reader]-48))*add;
            add*=10;
            reader--;
        }
        int color = position&1;
        iterative(1000000000, sum, sum, color);
    }
    if (ucicommand.substr(0, 8) == "go nodes") {
        int sum = 0;
        int add = 1;
        int reader = ucicommand.length()-1;
        while (ucicommand[reader] != ' ') {
            sum+=((int)(ucicommand[reader]-48))*add;
            add*=10;
            reader--;
        }
        int color = position&1;
        iterative(sum, 120000, 120000, color);
    }
    if (ucicommand.substr(0, 11) == "go infinite") {
        int color = position&1;
        iterative(1000000000, 120000, 120000, color);
    }
    if (ucicommand.substr(0, 8) == "go perft") {
        start = chrono::steady_clock::now();
        int color = position&1;
        int sum = 0;
        int add = 1;
        int reader = ucicommand.length()-1;
        while (ucicommand[reader] != ' ') {
            sum+=((int)(ucicommand[reader]-48))*add;
            add*=10;
            reader--;
        }
        perft(sum, sum, color);
    }
    if (ucicommand.substr(0, 9) == "go sperft") {
        start = chrono::steady_clock::now();
        int color = position&1;
        int sum = 0;
        int add = 1;
        int reader = ucicommand.length()-1;
        while (ucicommand[reader] != ' ') {
            sum+=((int)(ucicommand[reader]-48))*add;
            add*=10;
            reader--;
        }
        perftnobulk(sum, sum, color);
    }
    if (ucicommand.substr(0, 23) == "setoption name EvalFile") {
        string nnuefile = ucicommand.substr(30, ucicommand.length() - 30);
        if (nnuefile != "<empty>") {
            readnnuefile(nnuefile);
            useNNUE = true;
            initializennue();
            cout << "info string using nnue file " << nnuefile << "\n";
        }
        else {
            useNNUE = false;
        }
    }
    if (ucicommand.substr(0, 3) == "see") {
        string mov = ucicommand.substr(4, ucicommand.length() - 4);
        int color = position & 1;
        int movcount = generatemoves(color, 0, 0);
        int move = 0;
        for (int i = 0; i < movcount; i++) {
            if (algebraic(moves[0][i]) == mov) {
                move = moves[0][i];
            }
        }
        cout << algebraic(move) << " " << see_exceeds(move, color, 0) << "\n";
    }
}
void xboard() {
    string xcommand;
    getline(cin, xcommand);
    if (xcommand.substr(0, 8) == "protover") {
        cout << "feature ping=1 setboard=1 analyze=0 sigint=0 sigterm=0 myname=\"sscg13 engine\" variants=\"normal\" done=1\n";
    }
    if (xcommand == "new") {
        initializett();
        initializeboard();
        gosent = false;
    }
    if (xcommand.substr(0, 8) == "setboard") {
        string fen = xcommand.substr(9, xcommand.length()-9);
        parseFEN(fen);
    }
    if (xcommand.substr(0, 4) == "time") {
        int reader = 5;
        while ('0' <= xcommand[reader] && xcommand[reader] <= '9') {
            reader++;
        }
        reader--;
        int sum = 0;
        int add = 10;
        while (xcommand[reader] != ' ') {
            sum+=((int)(xcommand[reader]-48))*add;
            add*=10;
            reader--;
        }
        movetime = sum/12;
    }
    if (xcommand.substr(0, 7) == "level 0") {
        int reader = 8;
        int sum1 = 0;
        int sum2 = 0;
        movetime = 0;
        int add = 60000;
        while ((xcommand[reader] != ' ') && (xcommand[reader] != ':')) {
            reader++;
        }
        int save = reader;
        reader--;
        while (xcommand[reader] != ' ') {
            sum1+=((int)(xcommand[reader]-48))*add;
            add*=10;
            reader--;
        }
        add = 10000;
        reader = save+1;
        if (xcommand[save] == ':') {
            while (xcommand[reader] != ' ') {
                sum1+=((int)(xcommand[reader]-48))*add;
                add/=10;
                reader++;
            }
        }
        add = 1000;
        bool incenti = false;
        reader = xcommand.length()-1;
        while (xcommand[reader] != ' ') {
            if (xcommand[reader] >= '0') {
                sum2+=((int)xcommand[reader]-48)*add;
                add*=10;
            }
            if (xcommand[reader] == '.') {
                incenti = true;
            }
            reader--;
        }
        if (incenti) {
            sum2/=100;
        }
        movetime = sum1/10+sum2;
    }
    if (xcommand.substr(0, 4) == "ping") {
        int sum = 0;
        int add = 1;
        int reader = xcommand.length()-1;
        while (xcommand[reader] != ' ') {
            sum+=((int)(xcommand[reader]-48))*add;
            add*=10;
            reader--;
        }
        cout << "pong " << sum << "\n";
    }
    if ((xcommand.length() == 4) || (xcommand.length() == 5)) {
        int color = position&1;
        int len = generatemoves(color, 0, 0);
        int played = -1;
        for (int j = 0; j < len; j++) {
            if (algebraic(moves[0][j])==xcommand) {
                played = j;
            }
        }
        if (played >= 0) {
            makemove(moves[0][played], false);
            if (gosent) {
                int color = position&1;
                iterative(1000000000, movetime/4, movetime, color);
            }
        }
    }
    if (xcommand == "go") {
        int color = position&1;
        iterative(1000000000, movetime/4, movetime, color);
        gosent = true;
    }
}
int main() {
    initializeleaperattacks();
    initializemasks();
    initializerankattacks();
    initializeboard();
    initializelmr();
    initializezobrist();
    initializett();
    srand(time(0));
    getline(cin, proto);
    if (proto == "uci") {
        cout << "id name sscg13 chess engine\n" << "id author sscg13\n"
        << "option name EvalFile type string default <empty>\n" << "uciok\n";
        while (true) {
            uci();
        }
    }
    if (proto == "xboard") {
        while (true) {
            xboard();
        }
    }
    return 0;
}
