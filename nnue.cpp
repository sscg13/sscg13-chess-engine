#include <cmath>
#include <fstream>
#define INCBIN_PREFIX
#include "incbin.h"

const int inputbuckets = 4;
const int nnuesize = 16;
const int outputbuckets = 8;
const int evalscale = 400;
const int evalQA = 255;
const int evalQB = 64;
const int kingbuckets[64] = {
  0, 0, 0, 0, 1, 1, 1, 1,
  0, 0, 0, 0, 1, 1, 1, 1,
  0, 0, 0, 0, 1, 1, 1, 1,
  2, 2, 2, 2, 3, 3, 3, 3,
  2, 2, 2, 2, 3, 3, 3, 3,
  2, 2, 2, 2, 3, 3, 3, 3,
  2, 2, 2, 2, 3, 3, 3, 3,
  2, 2, 2, 2, 3, 3, 3, 3
};
const int material[6] = {1, 1, 1, 1, 1, 0};
const int bucketdivisor = 32 / outputbuckets;
const int nnuefilesize =
    (inputbuckets * 1536 * nnuesize + 2 * nnuesize + 4 * nnuesize * outputbuckets + 2 * outputbuckets);
INCBIN(char, NNUE, EUNNfile);
int screlu(short int x) {
  return std::pow(std::max(std::min((int)x, 255), 0), 2);
}
class NNUE {
  short int nnuelayer1[inputbuckets][768][nnuesize];
  short int layer1bias[nnuesize];
  int ourlayer2[outputbuckets][nnuesize];
  int theirlayer2[outputbuckets][nnuesize];
  short int accumulator[inputbuckets][2][nnuesize];
  uint64_t cachebitboards[inputbuckets][2][8];
  int finalbias[outputbuckets];
  int activebucket[2];
  int totalmaterial;

public:
  void loaddefaultnet();
  void readnnuefile(std::string file);
  void activatepiece(int bucket, int color, int piece, int square);
  void deactivatepiece(int bucket, int color, int piece, int square);
  void refreshfromscratch(int bucket, int color, uint64_t *Bitboards);
  void refreshfromcache(int bucket, int color, uint64_t *Bitboards);
  void initializennue(uint64_t *Bitboards);
  void forwardaccumulators(int notation, uint64_t *Bitboards);
  void backwardaccumulators(int notation, uint64_t *Bitboards);
  int evaluate(int color);
};

void NNUE::loaddefaultnet() {
  int offset = 0;
  for (int k = 0; k < inputbuckets; k++) {
    for (int i = 0; i < 768; i++) {
      int piece = i / 64;
      int square = i % 64;
      int convert[12] = {0, 3, 1, 4, 2, 5, 6, 9, 7, 10, 8, 11};
      for (int j = 0; j < nnuesize; j++) {
        short int weight = 256 * (short int)(NNUEData[offset + 1]) +
                          (short int)(unsigned char)(NNUEData[offset]);
        nnuelayer1[k][64 * convert[piece] + square][j] = weight;
        offset += 2;
      }
    }
  }
  for (int i = 0; i < nnuesize; i++) {
    short int bias = 256 * (short int)(NNUEData[offset + 1]) +
                     (short int)(unsigned char)(NNUEData[offset]);
    layer1bias[i] = bias;
    offset += 2;
  }
  for (int j = 0; j < outputbuckets; j++) {
    for (int i = 0; i < nnuesize; i++) {
      short int weight = 256 * (short int)(NNUEData[offset + 1]) +
                         (short int)(unsigned char)(NNUEData[offset]);
      ourlayer2[j][i] = (int)weight;
      offset += 2;
    }
    for (int i = 0; i < nnuesize; i++) {
      short int weight = 256 * (short int)(NNUEData[offset + 1]) +
                         (short int)(unsigned char)(NNUEData[offset]);
      theirlayer2[j][i] = (int)weight;
      offset += 2;
    }
  }
  for (int j = 0; j < outputbuckets; j++) {
    short int base = 256 * (short int)(NNUEData[offset + 1]) +
                     (short int)(unsigned char)(NNUEData[offset]);
    finalbias[j] = base;
    offset += 2;
  }
}
void NNUE::readnnuefile(std::string file) {
  std::ifstream nnueweights;
  nnueweights.open(file, std::ifstream::binary);
  char *weights = new char[nnuefilesize];
  nnueweights.read(weights, nnuefilesize);
  int offset = 0;
  for (int k = 0; k < inputbuckets; k++) {
    for (int i = 0; i < 768; i++) {
      int piece = i / 64;
      int square = i % 64;
      int convert[12] = {0, 3, 1, 4, 2, 5, 6, 9, 7, 10, 8, 11};
      for (int j = 0; j < nnuesize; j++) {
        short int weight = 256 * (short int)(weights[offset + 1]) +
                          (short int)(unsigned char)(weights[offset]);
        nnuelayer1[k][64 * convert[piece] + square][j] = weight;
        offset += 2;
      }
    }
  }
  for (int i = 0; i < nnuesize; i++) {
    short int bias = 256 * (short int)(weights[offset + 1]) +
                     (short int)(unsigned char)(weights[offset]);
    layer1bias[i] = bias;
    offset += 2;
  }
  for (int j = 0; j < outputbuckets; j++) {
    for (int i = 0; i < nnuesize; i++) {
      short int weight = 256 * (short int)(weights[offset + 1]) +
                         (short int)(unsigned char)(weights[offset]);
      ourlayer2[j][i] = (int)weight;
      offset += 2;
    }
    for (int i = 0; i < nnuesize; i++) {
      short int weight = 256 * (short int)(weights[offset + 1]) +
                         (short int)(unsigned char)(weights[offset]);
      theirlayer2[j][i] = (int)weight;
      offset += 2;
    }
  }
  for (int j = 0; j < outputbuckets; j++) {
    short int base = 256 * (short int)(weights[offset + 1]) +
                     (short int)(unsigned char)(weights[offset]);
    finalbias[j] = base;
    offset += 2;
  }
  delete[] weights;
  nnueweights.close();
}
void NNUE::activatepiece(int bucket, int color, int piece, int square) {
  for (int i = 0; i < nnuesize; i++) {
    accumulator[bucket][color][i] += nnuelayer1[bucket][64*piece + (56 * color) ^ square][i];
  }
  cachebitboards[bucket][color][color ^ (piece / 6)] ^= (1ULL << square);
  cachebitboards[bucket][color][2 + (piece % 6)] ^= (1ULL << square);
}
void NNUE::deactivatepiece(int bucket, int color, int piece, int square) {
  for (int i = 0; i < nnuesize; i++) {
    accumulator[bucket][color][i] -= nnuelayer1[bucket][64*piece + (56 * color) ^ square][i];
  }
  cachebitboards[bucket][color][color ^ (piece / 6)] ^= (1ULL << square);
  cachebitboards[bucket][color][2 + (piece % 6)] ^= (1ULL << square);
}
void NNUE::refreshfromscratch(int bucket, int color, uint64_t *Bitboards) {
  for (int i = 0; i < nnuesize; i++) {
    accumulator[bucket][color][i] = layer1bias[i];
  }
  for (int i = 0; i < 12; i++) {
    uint64_t pieces = (Bitboards[i / 6] & Bitboards[2 + (i % 6)]);
    int piececount = __builtin_popcountll(pieces);
    for (int j = 0; j < piececount; j++) {
      int square = __builtin_popcountll((pieces & -pieces) - 1);
      activatepiece(bucket, color, (i % 6) + 6 * (color ^ (i/6)), square);
      pieces ^= (1ULL << square);
    }
  }
  for (int i = 0; i < 8; i++) {
    cachebitboards[bucket][color][i] = Bitboards[i];
  }
}
void NNUE::refreshfromcache(int bucket, int color, uint64_t *Bitboards) {
  uint64_t add[12];
  uint64_t remove[12];
  for (int i = 0; i < 12; i++) {
    add[i] = (Bitboards[i/6] & Bitboards[2 + (i % 6)]) & ~(cachebitboards[bucket][color][i/6] & cachebitboards[bucket][color][2 + (i % 6)]);
    remove[i] = (cachebitboards[bucket][color][i/6] & cachebitboards[bucket][color][2 + (i % 6)]) & ~(Bitboards[i/6] & Bitboards[2 + (i % 6)]);
  }
  for (int i = 0; i < 12; i++) {
    int addcount = __builtin_popcountll(add[i]);
    for (int j = 0; j < addcount; j++) {
      int square = __builtin_ctzll(add[i]);
      activatepiece(bucket, color, (i % 6) + 6 * (color ^ (i/6)), square);
      add[i] ^= (1ULL << square);
    }
    int removecount = __builtin_popcountll(remove[i]);
    for (int j = 0; j < removecount; j++) {
      int square = __builtin_ctzll(remove[i]);
      deactivatepiece(bucket, color, (i % 6) + 6 * (color ^ (i/6)), square);
      remove[i] ^= (1ULL << square);
    }
  }
}
void NNUE::initializennue(uint64_t *Bitboards) {
  totalmaterial = 0;
  for (int i = 0; i < inputbuckets; i++) {
    refreshfromscratch(i, 0, Bitboards);
    refreshfromscratch(i, 1, Bitboards);
  }
  for (int i = 0; i < 12; i++) {
    uint64_t pieces = (Bitboards[i / 6] & Bitboards[2 + (i % 6)]);
    int piececount = __builtin_popcountll(pieces);
    totalmaterial += piececount * material[i % 6];
  }
  activebucket[0] = kingbuckets[__builtin_popcountll((Bitboards[0] & Bitboards[7]) - 1)];
  activebucket[1] = kingbuckets[56 ^ __builtin_popcountll((Bitboards[1] & Bitboards[7]) - 1)];
}
void NNUE::forwardaccumulators(int notation, uint64_t *Bitboards) {
  int from = notation & 63;
  int to = (notation >> 6) & 63;
  int color = (notation >> 12) & 1;
  int piece = (notation >> 13) & 7;
  int captured = (notation >> 17) & 7;
  int promoted = (notation >> 21) & 3;
  int piece2 = (promoted > 0) ? piece : piece - 2;
  activatepiece(activebucket[color ^ 1], color^1, 6 + piece2, to);
  deactivatepiece(activebucket[color ^ 1], color^1, 4 + piece, from);
  if (captured > 0) {
    deactivatepiece(activebucket[color ^ 1], color ^ 1, captured - 2, to);
  }
  int oldbucket = kingbuckets[from ^ (56 * color)];
  int newbucket = kingbuckets[to ^ (56 * color)];
  if (piece == 7 && oldbucket != newbucket) {
    int scratchrefreshtime = __builtin_popcountll(Bitboards[0]|Bitboards[1]);
    int cacherefreshtime = __builtin_popcountll((cachebitboards[newbucket][color][0]|cachebitboards[newbucket][color][1])^(Bitboards[0]|Bitboards[1]));
    if (scratchrefreshtime <= cacherefreshtime) {
      refreshfromscratch(newbucket, color, Bitboards);
    }
    else {
      refreshfromcache(newbucket, color, Bitboards);
    }
    activebucket[color] = newbucket;
  }
  else {
    activatepiece(activebucket[color], color, piece2, to);
    deactivatepiece(activebucket[color], color, piece - 2, from);
    if (captured > 0) {
      deactivatepiece(activebucket[color], color, 4 + captured, to);
    }
  }
}
void NNUE::backwardaccumulators(int notation, uint64_t *Bitboards) {
  int from = notation & 63;
  int to = (notation >> 6) & 63;
  int color = (notation >> 12) & 1;
  int piece = (notation >> 13) & 7;
  int captured = (notation >> 17) & 7;
  int promoted = (notation >> 21) & 3;
  int piece2 = promoted ? piece : piece - 2;
  deactivatepiece(activebucket[color^1], color^1, 6 + piece2, to);
  activatepiece(activebucket[color^1], color^1, 4 + piece, from);
  if (captured > 0) {
    activatepiece(activebucket[color^1], color ^ 1, captured - 2, to);
  }
  int oldbucket = kingbuckets[to ^ (56 * color)];
  int newbucket = kingbuckets[from ^ (56 * color)];
  if (piece == 7 && oldbucket != newbucket) {
    int scratchrefreshtime = __builtin_popcountll(Bitboards[0]|Bitboards[1]);
    int cacherefreshtime = __builtin_popcountll((cachebitboards[newbucket][color][0]|cachebitboards[newbucket][color][1])^(Bitboards[0]|Bitboards[1]));
    if (scratchrefreshtime <= cacherefreshtime) {
      refreshfromscratch(newbucket, color, Bitboards);
    }
    else {
      refreshfromcache(newbucket, color, Bitboards);
    }
    activebucket[color] = newbucket;
  }
  else {
    deactivatepiece(activebucket[color], color, piece2, to);
    activatepiece(activebucket[color], color, piece - 2, from);
    if (captured > 0) {
      activatepiece(activebucket[color], color, 4 + captured, to);
    }
  }
}
int NNUE::evaluate(int color) {
  int bucket = std::min(totalmaterial / bucketdivisor, outputbuckets - 1);
  int eval = finalbias[bucket] * evalQA;
  for (int i = 0; i < nnuesize; i++) {
    eval += screlu(accumulator[activebucket[color]][color][i]) * ourlayer2[bucket][i];
  }
  for (int i = 0; i < nnuesize; i++) {
    eval += screlu(accumulator[activebucket[color^1]][color^1][i]) * theirlayer2[bucket][i];
  }
  eval /= evalQA;
  eval *= evalscale;
  eval /= (evalQA * evalQB);
  return eval;
}
