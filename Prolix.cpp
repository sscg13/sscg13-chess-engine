#include "board.cpp"
#include "nnue.cpp"
#include <chrono>
#include <fstream>
#include <string>
#include <thread>
#include <time.h>
std::string proto = "uci";
std::string uciinfostring =
    "id name Prolix \nid author sscg13 \noption name UCI_Variant type combo "
    "default shatranj var shatranj \noption name Threads type spin default 1 "
    "min 1 max 1 \noption name Hash type spin default 32 min 1 max 1024 "
    "\noption name Use NNUE type check default true \noption name EvalFile "
    "type string default <internal> \noption name UCI_ShowWDL type check "
    "default true \nuciok\n";
// 1 bit color, 7 bits halfmove
// 6 bits from square, 6 bits to square, 1 bit color, 3 bits piece moved, 1 bit
// castling, 1 bit double pawn push, 1 bit en passant, 1 bit promotion, 2 bits
// promoted piece, 1 bit capture, 3 bits piece captured 26 bits total for now?
const int maxmaxdepth = 32;
int lmr_reductions[maxmaxdepth][256];
auto start = std::chrono::steady_clock::now();
std::ifstream datainput;
std::string inputfile;
struct TTentry {
  U64 key;
  int score;
  int depth;
  int age;
  int nodetype;
  int hashmove;
};
struct abinfo {
  int playedmove;
  int eval;
};
class Engine {
  Board Bitboards;
  int historytable[2][6][64];
  int capthist[2][6][6];
  int TTsize = 1048576;
  std::vector<TTentry> TT;
  bool useNNUE = true;
  bool showWDL = true;
  NNUE EUNN;
  int killers[32][2];
  int countermoves[6][64];
  bool gosent = false;
  bool stopsearch = false;
  bool suppressoutput = false;
  int maxdepth = 32;
  abinfo searchstack[64];
  int bestmove = 0;
  int movetime = 0;
  std::random_device rd;
  std::mt19937 mt;
  std::ofstream dataoutput;
  void initializett();
  void updatett(int index, int depth, int score, int nodetype, int hashmove);
  void resethistory();
  int movestrength(int mov, int color);
  int quiesce(int alpha, int beta, int color, int depth);
  int alphabeta(int depth, int ply, int alpha, int beta, int color, bool nmp,
                int nodelimit, int timelimit);
  int wdlmodel(int eval);
  int normalize(int eval);
  int iterative(int nodelimit, int softtimelimit, int hardtimelimit, int color);
  void autoplay();

public:
  void startup();
  void bench();
  void datagen(int n, std::string outputfile);
  void uci();
  void xboard();
};
void Engine::initializett() {
  TT.resize(TTsize);
  for (int i = 0; i < TTsize; i++) {
    TT[i].key = (U64)i + 1ULL;
    TT[i].score = 0;
    TT[i].depth = 0;
    TT[i].age = 0;
    TT[i].nodetype = 0;
    TT[i].hashmove = 0;
  }
}
void Engine::updatett(int index, int depth, int score, int nodetype,
                      int hashmove) {
  if (index < TTsize) {
    TT[index].key = Bitboards.zobristhash;
    TT[index].depth = depth;
    TT[index].age = Bitboards.gamelength;
    TT[index].hashmove = hashmove;
    TT[index].nodetype = nodetype;
    TT[index].score = score;
  }
}
void Engine::resethistory() {
  for (int i = 0; i < 6; i++) {
    for (int j = 0; j < 64; j++) {
      historytable[0][i][j] = 0;
      historytable[1][i][j] = 0;
      countermoves[i][j] = 0;
    }
    for (int j = 0; j < 6; j++) {
      capthist[0][i][j] = 0;
      capthist[1][i][j] = 0;
    }
  }
  for (int i = 0; i < 32; i++) {
    killers[i][0] = 0;
    killers[i][1] = 0;
  }
}
void Engine::startup() {
  initializett();
  resethistory();
  Bitboards.initialize();
  EUNN.loaddefaultnet();
  EUNN.initializennue(Bitboards.Bitboards);
  mt.seed(rd());
}
void initializelmr() {
  for (int i = 0; i < maxmaxdepth; i++) {
    for (int j = 0; j < 256; j++) {
      lmr_reductions[i][j] =
          (i == 0 || j == 0) ? 0 : floor(0.59 + log(i) * log(j) * 0.46);
    }
  }
}
int Engine::movestrength(int mov, int color) {
  int to = (mov >> 6) & 63;
  int piece = (mov >> 13) & 7;
  int captured = (mov >> 17) & 7;
  int promoted = (mov >> 21) & 3;
  if (captured) {
    return 10000 * captured + 12000 * promoted + 10000 - 1000 * piece +
           capthist[color][piece - 2][captured - 2];
  } else {
    return 60000 * promoted + historytable[color][piece - 2][to];
  }
}
int Engine::quiesce(int alpha, int beta, int color, int depth) {
  int score = useNNUE ? EUNN.evaluate(color) : Bitboards.evaluate(color);
  int bestscore = -30000;
  int movcount;
  if (depth > 3) {
    return score;
  }
  bool incheck = Bitboards.checkers(color);
  if (incheck) {
    movcount = Bitboards.generatemoves(color, 0, maxdepth + depth);
    if (movcount == 0) {
      return -27000;
    }
  } else {
    bestscore = score;
    if (alpha < score) {
      alpha = score;
    }
    if (score >= beta) {
      return score;
    }
    movcount = Bitboards.generatemoves(color, 1, maxdepth + depth);
  }

  if (depth < 1) {
    for (int i = 0; i < movcount - 1; i++) {
      for (int j = i + 1;
           movestrength(Bitboards.moves[maxdepth + depth][j], color) >
               movestrength(Bitboards.moves[maxdepth + depth][j - 1], color) &&
           j > 0;
           j--) {
        std::swap(Bitboards.moves[maxdepth + depth][j],
                  Bitboards.moves[maxdepth + depth][j - 1]);
      }
    }
  }
  for (int i = 0; i < movcount; i++) {
    int mov = Bitboards.moves[maxdepth + depth][i];
    bool good = (incheck || Bitboards.see_exceeds(mov, color, 0));
    if (good) {
      Bitboards.makemove(mov, 1);
      if (useNNUE) {
        EUNN.forwardaccumulators(mov);
      }
      score = -quiesce(-beta, -alpha, color ^ 1, depth + 1);
      Bitboards.unmakemove(mov);
      if (useNNUE) {
        EUNN.backwardaccumulators(mov);
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
int Engine::alphabeta(int depth, int ply, int alpha, int beta, int color,
                      bool nmp, int nodelimit, int timelimit) {
  if (Bitboards.repetitions() > 1) {
    return 0;
  }
  if (Bitboards.halfmovecount() >= 140) {
    return 0;
  }
  if (Bitboards.twokings()) {
    return 0;
  }
  if (Bitboards.bareking(color ^ 1)) {
    return (28001 - ply);
  }
  if (depth <= 0 || ply >= maxdepth) {
    return quiesce(alpha, beta, color, 0);
  }
  int score = -30000;
  int bestscore = -30000;
  int allnode = 0;
  int movcount;
  int index = Bitboards.zobristhash % TTsize;
  int ttmove = 0;
  int bestmove1 = -1;
  int ttdepth = TT[index].depth;
  int ttage = std::max(Bitboards.gamelength - TT[index].age, 0);
  bool update = (depth >= (ttdepth - ttage / 3));
  bool incheck = (Bitboards.checkers(color) != 0ULL);
  bool isPV = (beta - alpha > 1);
  int staticeval = useNNUE ? EUNN.evaluate(color) : Bitboards.evaluate(color);
  searchstack[ply].eval = staticeval;
  bool improving = false;
  if (ply > 1) {
    improving = (staticeval > searchstack[ply - 2].eval);
  }
  int quiets = 0;
  if (TT[index].key == Bitboards.zobristhash) {
    score = TT[index].score;
    ttmove = TT[index].hashmove;
    int nodetype = TT[index].nodetype;
    if (ttdepth >= depth) {
      if (!isPV && Bitboards.repetitions() == 0) {
        if (nodetype == 3) {
          return score;
        }
        if ((nodetype & 1) && (score >= beta)) {
          return score;
        }
        if ((nodetype & 2) && (score <= alpha)) {
          return score;
        }
      }
    } else {
      int margin = std::max(40, 70 * (depth - ttdepth - improving));
      if (((nodetype & 1) && (score - margin >= beta)) &&
          (abs(beta) < 27000 && !incheck) && (ply > 0)) {
        return (score + beta) / 2;
      }
    }
  }
  int margin = std::max(40, 70 * (depth - improving));
  if (ply > 0 && score == -30000) {
    if (staticeval - margin >= beta && (abs(beta) < 27000 && !incheck)) {
      return (staticeval + beta) / 2;
    }
  }
  movcount = Bitboards.generatemoves(color, 0, ply);
  if (movcount == 0) {
    return -1 * (28000 - ply);
  }
  if ((!incheck && Bitboards.gamephase[color] > 3) && (depth > 1 && nmp) &&
      (staticeval >= beta)) {
    Bitboards.makenullmove();
    searchstack[ply].playedmove = 0;
    score = -alphabeta(std::max(0, depth - 2 - (depth + 1) / 3), ply + 1, -beta,
                       1 - beta, color ^ 1, false, nodelimit, timelimit);
    Bitboards.unmakenullmove();
    if (score >= beta) {
      return beta;
    }
  }
  /*if ((depth < 3) && (staticeval + 200*depth < alpha) && !isPV) {
      int qsearchscore = quiesce(alpha, beta, color, 0);
      if (qsearchscore <= alpha) {
          return alpha;
      }
  }*/
  int counter = 0;
  int previousmove = 0;
  int previouspiece = 0;
  int previoussquare = 0;
  if (ply > 0 && nmp) {
    previousmove = searchstack[ply - 1].playedmove;
    previouspiece = (previousmove >> 13) & 7;
    previoussquare = (previousmove >> 6) & 63;
    counter = countermoves[previouspiece - 2][previoussquare];
  }
  int movescore[256];
  for (int i = 0; i < movcount; i++) {
    int mov = Bitboards.moves[ply][i];
    if (mov == ttmove) {
      movescore[i] = (1 << 20);
    } else {
      movescore[i] = movestrength(mov, color);
    }
    if (mov == killers[ply][0]) {
      movescore[i] += 20000;
    }
    /*else if (mov == killers[ply][1]) {
      movescore[i] += 10000;
    }*/
    else if ((mov & 4095) == counter) {
      movescore[i] += 10000;
    }
    if (Bitboards.see_exceeds(mov, color, 0)) {
      movescore[i] += 15000;
    }
    int j = i;
    while (j > 0 && movescore[j] > movescore[j - 1]) {
      std::swap(Bitboards.moves[ply][j], Bitboards.moves[ply][j - 1]);
      std::swap(movescore[j], movescore[j - 1]);
      j--;
    }
  }
  for (int i = 0; i < movcount; i++) {
    bool nullwindow = (i > 0);
    int r = 0;
    bool prune = false;
    int mov = Bitboards.moves[ply][i];
    if (!iscapture(mov)) {
      quiets++;
      /*if (quiets > 7*depth) {
        prune = true;
      }*/
      r = std::min(depth - 1, lmr_reductions[depth][i]);
    }
    r = std::max(0, r - isPV - improving);
    int e = (movcount == 1);
    if (!stopsearch && !prune) {
      Bitboards.makemove(mov, true);
      searchstack[ply].playedmove = mov;
      if (useNNUE) {
        EUNN.forwardaccumulators(mov);
      }
      if (nullwindow) {
        score = -alphabeta(depth - 1 - r, ply + 1, -alpha - 1, -alpha,
                           color ^ 1, true, nodelimit, timelimit);
        if (score > alpha && r > 0) {
          score = -alphabeta(depth - 1, ply + 1, -alpha - 1, -alpha, color ^ 1,
                             true, nodelimit, timelimit);
        }
        if (score > alpha && score < beta) {
          score = -alphabeta(depth - 1, ply + 1, -beta, -alpha, color ^ 1, true,
                             nodelimit, timelimit);
        }
      } else {
        score = -alphabeta(depth - 1, ply + 1, -beta, -alpha, color ^ 1, true,
                           nodelimit, timelimit);
      }
      Bitboards.unmakemove(mov);
      if (useNNUE) {
        EUNN.backwardaccumulators(mov);
      }
      if (score > bestscore) {
        if (score > alpha) {
          if (score >= beta) {
            if (update && !stopsearch && abs(score) < 29000) {
              updatett(index, depth, score, 1, mov);
            }
            if (!iscapture(mov) && (killers[ply][0] != mov)) {
              killers[ply][1] = killers[ply][0];
              killers[ply][0] = mov;
            }
            int target = (mov >> 6) & 63;
            int piece = (mov >> 13) & 7;
            int captured = (mov >> 17) & 7;
            if (captured > 0) {
              capthist[color][piece - 2][captured - 2] +=
                  (depth * depth * depth -
                   (depth * depth * depth *
                    capthist[color][piece - 2][captured - 2]) /
                       27000);
            } else {
              historytable[color][piece - 2][target] +=
                  (depth * depth -
                   (depth * depth * historytable[color][piece - 2][target]) /
                       27000);
            }
            for (int j = 0; j < i; j++) {
              int mov2 = Bitboards.moves[ply][j];
              if (!iscapture(mov2)) {
                historytable[color][((mov2 >> 13) & 7) - 2][(mov2 >> 6) & 63] -=
                    (depth * 3);
              }
            }
            if (ply > 0 && nmp && !iscapture(mov)) {
              countermoves[previouspiece - 2][previoussquare] = (mov & 4095);
            }
            return score;
          }
          alpha = score;
          allnode = 1;
        }
        if (ply == 0) {
          bestmove = mov;
        }
        bestmove1 = i;
        bestscore = score;
      }
      if (Bitboards.nodecount > nodelimit) {
        stopsearch = true;
      }
      if (depth > 3) {
        auto now = std::chrono::steady_clock::now();
        auto timetaken =
            std::chrono::duration_cast<std::chrono::milliseconds>(now - start);
        if (timetaken.count() > timelimit) {
          stopsearch = true;
        }
      }
    }
  }
  if ((update && !stopsearch) &&
      ((bestmove1 >= 0) && (abs(bestscore) < 29000))) {
    updatett(index, depth, bestscore, 2 + allnode,
             Bitboards.moves[ply][bestmove1]);
  }
  return bestscore;
}
int Engine::wdlmodel(int eval) {
  int material = Bitboards.material();
  double m = std::max(std::min(material, 64), 4) / 32.0;
  double as[4] = {12.86611189, -1.56947052, -105.75177291, 247.30758159};
  double bs[4] = {-7.31901285, 36.79299424, -14.98330140, 64.14426025};
  double a = (((as[0] * m + as[1]) * m + as[2]) * m) + as[3];
  double b = (((bs[0] * m + bs[1]) * m + bs[2]) * m) + bs[3];
  return int(0.5 + 1000 / (1 + exp((a - double(eval)) / b)));
}
int Engine::normalize(int eval) {
  if (abs(eval) == 27000) {
    return eval;
  }
  int material = Bitboards.material();
  double m = std::max(std::min(material, 64), 4) / 32.0;
  double as[4] = {12.86611189, -1.56947052, -105.75177291, 247.30758159};
  double a = (((as[0] * m + as[1]) * m + as[2]) * m) + as[3];
  return round(100 * eval / a);
}
int Engine::iterative(int nodelimit, int softtimelimit, int hardtimelimit,
                      int color) {
  Bitboards.nodecount = 0;
  stopsearch = false;
  start = std::chrono::steady_clock::now();
  int score = useNNUE ? EUNN.evaluate(color) : Bitboards.evaluate(color);
  int returnedscore = score;
  int depth = 1;
  int bestmove1 = 0;
  int pvtable[maxdepth];
  resethistory();
  while (!stopsearch) {
    bestmove = -1;
    int delta = 30;
    int alpha = score - delta;
    int beta = score + delta;
    bool fail = true;
    while (fail) {
      int score1 = alphabeta(depth, 0, alpha, beta, color, false, nodelimit,
                             hardtimelimit);
      if (score1 >= beta) {
        beta += delta;
        delta += delta;
      } else if (score1 <= alpha) {
        alpha -= delta;
        delta += delta;
      } else {
        score = score1;
        fail = false;
      }
    }
    auto now = std::chrono::steady_clock::now();
    auto timetaken =
        std::chrono::duration_cast<std::chrono::milliseconds>(now - start);
    if (Bitboards.nodecount < nodelimit && timetaken.count() < hardtimelimit &&
        depth < maxdepth && bestmove >= 0) {
      returnedscore = score;
      int last = depth;
      int pvcolor = color;
      bool stop = false;
      for (int i = 0; i < depth; i++) {
        int index = Bitboards.zobristhash % TTsize;
        stop = true;
        if (TT[index].key == Bitboards.zobristhash && TT[index].nodetype == 3) {
          int movcount = Bitboards.generatemoves(pvcolor, 0, 0);
          for (int j = 0; j < movcount; j++) {
            if (Bitboards.moves[0][j] == TT[index].hashmove) {
              stop = false;
            }
          }
        }
        if (stop) {
          last = i;
          i = depth;
        } else {
          pvcolor ^= 1;
          pvtable[i] = TT[index].hashmove;
          Bitboards.makemove(TT[index].hashmove, 1);
        }
      }
      for (int i = last - 1; i >= 0; i--) {
        Bitboards.unmakemove(pvtable[i]);
      }
      if (proto == "uci" && !suppressoutput) {
        if (abs(score) <= 27000) {
          int normalscore = normalize(score);
          std::cout << "info depth " << depth << " nodes "
                    << Bitboards.nodecount << " time " << timetaken.count()
                    << " score cp " << normalscore;
          if (showWDL) {
            int winrate = wdlmodel(score);
            int lossrate = wdlmodel(-score);
            int drawrate = 1000 - winrate - lossrate;
            std::cout << " wdl " << winrate << " " << drawrate << " "
                      << lossrate;
          }
          std::cout << " pv ";
          for (int i = 0; i < last; i++) {
            std::cout << algebraic(pvtable[i]) << " ";
          }
          std::cout << "\n";
        } else {
          int matescore;
          if (score > 0) {
            matescore = 1 + (28000 - score) / 2;
          } else {
            matescore = (-28000 - score) / 2;
          }
          std::cout << "info depth " << depth << " nodes "
                    << Bitboards.nodecount << " time " << timetaken.count()
                    << " score mate " << matescore;
          if (showWDL) {
            int winrate = 1000 * (matescore > 0);
            int lossrate = 1000 * (matescore < 0);
            std::cout << " wdl " << winrate << " 0 " << lossrate;
          }
          std::cout << " pv ";
          for (int i = 0; i < last; i++) {
            std::cout << algebraic(pvtable[i]) << " ";
          }
          std::cout << "\n";
        }
      }
      if (proto == "xboard") {
        std::cout << depth << " " << score << " " << timetaken.count() / 10
                  << " " << Bitboards.nodecount << " ";
        for (int i = 0; i < last; i++) {
          std::cout << algebraic(pvtable[i]) << " ";
        }
        std::cout << "\n";
      }
      depth++;
      if (depth == maxdepth) {
        stopsearch = true;
      }
      bestmove1 = bestmove;
    } else {
      stopsearch = true;
    }
    if (timetaken.count() > softtimelimit) {
      stopsearch = true;
    }
  }
  auto now = std::chrono::steady_clock::now();
  auto timetaken =
      std::chrono::duration_cast<std::chrono::milliseconds>(now - start);
  if (timetaken.count() > 0 && (proto == "uci") && !suppressoutput) {
    int nps = 1000 * (Bitboards.nodecount / timetaken.count());
    std::cout << "info nodes " << Bitboards.nodecount << " nps " << nps << "\n";
  }
  if (proto == "uci" && !suppressoutput) {
    std::cout << "bestmove " << algebraic(bestmove1) << "\n";
  }
  if (proto == "xboard") {
    std::cout << "move " << algebraic(bestmove1) << "\n";
    Bitboards.makemove(bestmove1, 0);
    if (useNNUE) {
      EUNN.forwardaccumulators(bestmove1);
    }
  }
  bestmove = bestmove1;
  return returnedscore;
}
void Engine::autoplay() {
  suppressoutput = true;
  initializett();
  resethistory();
  int seed = mt() % 40320;
  Bitboards.parseFEN(get8294400FEN(seed, seed));
  std::string game = "";
  std::string result = "";
  int extra = (mt() >> 11) & 1;
  for (int i = 0; i < 7 + extra; i++) {
    int num_moves = Bitboards.generatemoves(i & 1, 0, 0);
    if (num_moves == 0) {
      suppressoutput = false;
      initializett();
      resethistory();
      seed = mt() % 40320;
      Bitboards.parseFEN(get8294400FEN(seed, seed));
      return;
    }
    int rand_move = mt() % num_moves;
    Bitboards.makemove(Bitboards.moves[0][rand_move], 0);
    game += algebraic(Bitboards.moves[0][rand_move]);
    game += " ";
  }
  if (useNNUE) {
    EUNN.initializennue(Bitboards.Bitboards);
  }
  if (Bitboards.generatemoves(0, 0, 0) == 0) {
    suppressoutput = false;
    initializett();
    resethistory();
    Bitboards.initialize();
    return;
  }
  std::string fens[1024];
  int scores[1024];
  int maxmove = 0;
  bool finished = false;
  while (!finished) {
    int color = Bitboards.position & 1;
    int score = iterative(65536, 50, 50, color);
    if ((bestmove > 0) && (((bestmove >> 16) & 1) == 0) &&
        (Bitboards.checkers(color) == 0ULL) && (abs(score) < 27000)) {
      fens[maxmove] = Bitboards.getFEN();
      scores[maxmove] = score * (1 - 2 * color);
      maxmove++;
    }
    /*if ((bestmove > 0) && (((bestmove >> 16) & 1) == 0) && (checkers(color) ==
    0ULL) && (abs(score) < 200) && (abs(score) > 100)) { bookoutput << getFEN()
    << "\n";
    }*/
    if (bestmove == 0) {
      std::cout << "Null best move? mitigating by using proper null move \n";
      Bitboards.makenullmove();
    } else {
      Bitboards.makemove(bestmove, 0);
    }
    if (Bitboards.twokings()) {
      finished = true;
      result = "0.5";
    } else if (Bitboards.bareking(color)) {
      finished = true;
      if (color == 0) {
        result = "0.0";
      } else {
        result = "1.0";
      }
    } else if (Bitboards.repetitions() >= 2) {
      finished = true;
      result = "0.5";
    } else if (Bitboards.generatemoves(color ^ 1, 0, 0) == 0) {
      finished = true;
      if (color == 0) {
        result = "1.0";
      } else {
        result = "0.0";
      }
    } else if (Bitboards.halfmovecount() >= 140) {
      finished = true;
      result = "0.5";
    } else if (Bitboards.gamelength >= 900) {
      finished = true;
      result = "0.5";
    }
    if (useNNUE && bestmove > 0) {
      EUNN.forwardaccumulators(bestmove);
    }
  }
  for (int i = 0; i < maxmove; i++) {
    dataoutput << fens[i] << " | " << scores[i] << " | " << result << "\n";
  }
  suppressoutput = false;
  initializett();
  resethistory();
  Bitboards.initialize();
}
void Engine::datagen(int n, std::string outputfile) {
  dataoutput.open(outputfile, std::ofstream::app);
  for (int i = 0; i < n; i++) {
    autoplay();
    std::cout << i << "\n";
  }
  dataoutput.close();
}
void Engine::bench() {
  std::string benchfens[14] = {
      "r5r1/1k6/1pqb4/1Bppn1p1/P1n1p2p/P1N1P2P/2KQ1p2/1RBR2N1 w - - 0 45",
      "8/1R6/4q3/3Nk1p1/2P3p1/3PK3/8/8 w - - 2 83",
      "8/8/8/1KQQQ3/2P3qP/5k2/7b/8 b - - 20 76",
      "2r1r3/p1pk1ppp/bpnpp2b/8/3P4/BPQ1PN1P/P1P1KPP1/R6R b - - 1 14",
      "3kq3/3p4/3p1p2/6pK/1R1Q4/1P1B1r2/8/8 w - - 2 44",
      "1nbkq3/1rpppr1p/3b1p2/p1PP1Pp1/1p6/PP1NP1PB/3Q3n/RNBKR3 w - - 0 20",
      "r4br1/8/p2k2qp/7n/1R1N4/3BB1P1/P2PPQ1P/3K4 w - - 3 32",
      "8/8/8/8/3Qk1n1/2K1P3/8/8 b - - 46 162",
      "rnbkqbnr/ppppp1p1/5p1p/8/8/3P2P1/PPP1PP1P/RNBKQBNR w - - 0 1",
      "5b1r/8/1p1pq1p1/p1k3P1/5RP1/P1PB4/4KQ2/8 w - - 1 44",
      "2r1qr2/8/1pkp2pb/p2pn1N1/3R2PP/3BP1Q1/P1P1R3/2K5 b - - 6 30",
      "1r2q3/R4pn1/1p1pkn2/3p1p2/1PpP2p1/N1P1K1P1/3Q3P/2B1R3 b - - 5 31",
      "8/1Q6/3Q4/3p1p2/2pkq2R/5q2/5K2/8 w - - 2 116",
      "8/4k3/4R3/2PK4/1P3Nn1/P2PPn2/5r2/8 b - - 2 58"};
  suppressoutput = true;
  maxdepth = 14;
  auto commence = std::chrono::steady_clock::now();
  int nodes = 0;
  for (int i = 0; i < 14; i++) {
    startup();
    Bitboards.parseFEN(benchfens[i]);
    int color = Bitboards.position & 1;
    iterative(1000000000, 120000, 120000, color);
    nodes += Bitboards.nodecount;
  }
  auto conclude = std::chrono::steady_clock::now();
  int timetaken =
      std::chrono::duration_cast<std::chrono::milliseconds>(conclude - commence)
          .count();
  int nps = 1000 * (nodes / timetaken);
  std::cout << nodes << " nodes " << nps << " nps\n";
}
void Engine::uci() {
  std::string ucicommand;
  getline(std::cin, ucicommand);
  if (ucicommand == "uci") {
    std::cout << uciinfostring;
  }
  if (ucicommand == "quit") {
    exit(0);
  }
  if (ucicommand == "isready") {
    std::cout << "readyok\n";
  }
  if (ucicommand == "ucinewgame") {
    initializett();
    Bitboards.initialize();
    EUNN.initializennue(Bitboards.Bitboards);
  }
  if (ucicommand.substr(0, 17) == "position startpos") {
    Bitboards.initialize();
    int color = 0;
    std::string mov = "";
    for (int i = 24; i <= ucicommand.length(); i++) {
      if ((ucicommand[i] == ' ') || (i == ucicommand.length())) {
        int len = Bitboards.generatemoves(color, 0, 0);
        int played = -1;
        for (int j = 0; j < len; j++) {
          if (algebraic(Bitboards.moves[0][j]) == mov) {
            played = j;
          }
        }
        if (played >= 0) {
          Bitboards.makemove(Bitboards.moves[0][played], false);
          color ^= 1;
        }
        mov = "";
      } else {
        mov += ucicommand[i];
      }
    }
    EUNN.initializennue(Bitboards.Bitboards);
  }
  if (ucicommand.substr(0, 12) == "position fen") {
    int reader = 13;
    while (ucicommand[reader] != 'm' && reader < ucicommand.length()) {
      reader++;
    }
    std::string fen = ucicommand.substr(13, reader - 12);
    Bitboards.parseFEN(fen);
    int color = Bitboards.position & 1;
    std::string mov = "";
    for (int i = reader + 6; i <= ucicommand.length(); i++) {
      if ((ucicommand[i] == ' ') || (i == ucicommand.length())) {
        int len = Bitboards.generatemoves(color, 0, 0);
        int played = -1;
        for (int j = 0; j < len; j++) {
          if (algebraic(Bitboards.moves[0][j]) == mov) {
            played = j;
          }
        }
        if (played >= 0) {
          Bitboards.makemove(Bitboards.moves[0][played], false);
          color ^= 1;
        }
        mov = "";
      } else {
        mov += ucicommand[i];
      }
    }
    EUNN.initializennue(Bitboards.Bitboards);
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
      sum += ((int)(ucicommand[reader] - 48)) * add;
      add *= 10;
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
      sum += ((int)(ucicommand[reader] - 48)) * add;
      add *= 10;
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
    if (reader < ucicommand.length() - 1) {
      sum = 0;
      add = 1;
      while (ucicommand[reader] != ' ') {
        sum += ((int)(ucicommand[reader] - 48)) * add;
        add *= 10;
        reader--;
      }
      winc = sum;
      reader = ucicommand.length() - 1;
      while (ucicommand[reader] == ' ') {
        reader--;
      }
      sum = 0;
      add = 1;
      while (ucicommand[reader] != ' ') {
        sum += ((int)(ucicommand[reader] - 48)) * add;
        add *= 10;
        reader--;
      }
      binc = sum;
    }
    int color = Bitboards.position & 1;
    if (color == 0) {
      int score =
          iterative(1000000000, wtime / 40 + winc / 3, wtime / 10 + winc, 0);
    } else {
      int score =
          iterative(1000000000, btime / 40 + binc / 3, btime / 10 + binc, 1);
    }
  }
  if (ucicommand.substr(0, 11) == "go movetime") {
    int sum = 0;
    int add = 1;
    int reader = ucicommand.length() - 1;
    while (ucicommand[reader] != ' ') {
      sum += ((int)(ucicommand[reader] - 48)) * add;
      add *= 10;
      reader--;
    }
    int color = Bitboards.position & 1;
    int score = iterative(1000000000, sum, sum, color);
  }
  if (ucicommand.substr(0, 8) == "go nodes") {
    int sum = 0;
    int add = 1;
    int reader = ucicommand.length() - 1;
    while (ucicommand[reader] != ' ') {
      sum += ((int)(ucicommand[reader] - 48)) * add;
      add *= 10;
      reader--;
    }
    int color = Bitboards.position & 1;
    int score = iterative(sum, 120000, 120000, color);
  }
  if (ucicommand.substr(0, 11) == "go infinite") {
    int color = Bitboards.position & 1;
    int score = iterative(1000000000, 120000, 120000, color);
  }
  if (ucicommand.substr(0, 8) == "go perft") {
    start = std::chrono::steady_clock::now();
    int color = Bitboards.position & 1;
    int sum = 0;
    int add = 1;
    int reader = ucicommand.length() - 1;
    while (ucicommand[reader] != ' ') {
      sum += ((int)(ucicommand[reader] - 48)) * add;
      add *= 10;
      reader--;
    }
    Bitboards.perft(sum, sum, color);
  }
  if (ucicommand.substr(0, 9) == "go sperft") {
    start = std::chrono::steady_clock::now();
    int color = Bitboards.position & 1;
    int sum = 0;
    int add = 1;
    int reader = ucicommand.length() - 1;
    while (ucicommand[reader] != ' ') {
      sum += ((int)(ucicommand[reader] - 48)) * add;
      add *= 10;
      reader--;
    }
    Bitboards.perftnobulk(sum, sum, color);
  }
  if (ucicommand.substr(0, 9) == "set input") {
    inputfile = ucicommand.substr(10, ucicommand.length() - 10);
  }
  if (ucicommand.substr(0, 14) == "setoption name") {
    int reader = 15;
    std::string option = "";
    while (ucicommand[reader] != ' ') {
      option += ucicommand[reader];
      reader++;
    }
    if (option == "Hash") {
      reader = ucicommand.length() - 1;
      int sum = 0;
      int add = 1;
      while (ucicommand[reader] != ' ') {
        sum += ((int)(ucicommand[reader] - 48)) * add;
        add *= 10;
        reader--;
      }
      if (sum <= 1024) {
        int oldTTsize = TTsize;
        TTsize = 32768 * sum;
        TT.resize(TTsize);
        TT.shrink_to_fit();
      }
    }
    if (option == "EvalFile") {
      std::string nnuefile = ucicommand.substr(30, ucicommand.length() - 30);
      if (nnuefile != "<internal>") {
        EUNN.readnnuefile(nnuefile);
        EUNN.initializennue(Bitboards.Bitboards);
        std::cout << "info string using nnue file " << nnuefile << "\n";
      }
    }
    if (option == "UCI_ShowWDL") {
      std::string value = ucicommand.substr(33, ucicommand.length() - 33);
      if (value == "true") {
        showWDL = true;
      } else {
        showWDL = false;
      }
    }
    if (option == "Use") {
      std::string value = ucicommand.substr(30, ucicommand.length() - 30);
      if (value == "true") {
        useNNUE = true;
      } else {
        useNNUE = false;
      }
    }
  }
  if (ucicommand.substr(0, 3) == "see") {
    std::string mov = ucicommand.substr(4, ucicommand.length() - 4);
    int color = Bitboards.position & 1;
    int movcount = Bitboards.generatemoves(color, 0, 0);
    int internal = 0;
    for (int i = 0; i < movcount; i++) {
      if (algebraic(Bitboards.moves[0][i]) == mov) {
        internal = Bitboards.moves[0][i];
      }
    }
    std::cout << algebraic(internal) << " "
              << Bitboards.see_exceeds(internal, color, 0) << "\n";
  }
  if (ucicommand == "history") {
    int color = Bitboards.position & 1;
    int movcount = Bitboards.generatemoves(color, 0, 0);
    std::cout << "History values:\n";
    for (int i = 0; i < movcount; i++) {
      int internal = Bitboards.moves[0][i];
      std::cout
          << algebraic(internal) << ": "
          << historytable[color][(internal >> 13) & 7 - 2][(internal >> 6) & 63]
          << "\n";
    }
  }
}
void Engine::xboard() {
  std::string xcommand;
  getline(std::cin, xcommand);
  if (xcommand.substr(0, 8) == "protover") {
    std::cout << "feature ping=1 setboard=1 analyze=0 sigint=0 sigterm=0 "
                 "myname=\"Prolix\" variants=\"shatranj\"\nfeature done=1\n";
  }
  if (xcommand == "new") {
    initializett();
    Bitboards.initialize();
    EUNN.initializennue(Bitboards.Bitboards);
    gosent = false;
  }
  if (xcommand.substr(0, 8) == "setboard") {
    std::string fen = xcommand.substr(9, xcommand.length() - 9);
    Bitboards.parseFEN(fen);
    EUNN.initializennue(Bitboards.Bitboards);
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
      sum += ((int)(xcommand[reader] - 48)) * add;
      add *= 10;
      reader--;
    }
    movetime = sum / 16;
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
      sum1 += ((int)(xcommand[reader] - 48)) * add;
      add *= 10;
      reader--;
    }
    add = 10000;
    reader = save + 1;
    if (xcommand[save] == ':') {
      while (xcommand[reader] != ' ') {
        sum1 += ((int)(xcommand[reader] - 48)) * add;
        add /= 10;
        reader++;
      }
    }
    add = 1000;
    bool incenti = false;
    reader = xcommand.length() - 1;
    while (xcommand[reader] != ' ') {
      if (xcommand[reader] >= '0') {
        sum2 += ((int)xcommand[reader] - 48) * add;
        add *= 10;
      }
      if (xcommand[reader] == '.') {
        incenti = true;
      }
      reader--;
    }
    if (incenti) {
      sum2 /= 100;
    }
    movetime = sum1 / 10 + sum2;
  }
  if (xcommand.substr(0, 4) == "ping") {
    int sum = 0;
    int add = 1;
    int reader = xcommand.length() - 1;
    while (xcommand[reader] != ' ') {
      sum += ((int)(xcommand[reader] - 48)) * add;
      add *= 10;
      reader--;
    }
    std::cout << "pong " << sum << "\n";
  }
  if ((xcommand.length() == 4) || (xcommand.length() == 5)) {
    int color = Bitboards.position & 1;
    int len = Bitboards.generatemoves(color, 0, 0);
    int played = -1;
    for (int j = 0; j < len; j++) {
      if (algebraic(Bitboards.moves[0][j]) == xcommand) {
        played = j;
      }
    }
    if (played >= 0) {
      Bitboards.makemove(Bitboards.moves[0][played], false);
      if (useNNUE) {
        EUNN.forwardaccumulators(Bitboards.moves[0][played]);
      }
      if (gosent) {
        int color = Bitboards.position & 1;
        int score = iterative(1000000000, movetime / 3, movetime, color);
      }
    }
  }
  if (xcommand == "go") {
    int color = Bitboards.position & 1;
    int score = iterative(1000000000, movetime / 3, movetime, color);
    gosent = true;
  }
}
int main(int argc, char *argv[]) {
  initializeleaperattacks();
  initializemasks();
  initializerankattacks();
  initializezobrist();
  initializelmr();
  if (argc > 1) {
    if (std::string(argv[1]) == "bench") {
      Engine Prolix;
      Prolix.startup();
      Prolix.bench();
      return 0;
    }
    if (std::string(argv[1]) == "datagen") {
      if (argc < 5) {
        std::cerr << "Too few arguments given";
        return 0;
      }
      int threads = atoi(argv[2]);
      int games = atoi(argv[3]);
      std::cout << "Generating with " << threads << " threads x " << games
                << " games:\n";
      std::vector<std::thread> datagenerators(threads);
      std::vector<Engine> Engines(threads);
      for (int i = 0; i < threads; i++) {
        std::string outputfile =
            std::string(argv[4]) + std::to_string(i) + ".txt";
        Engines[i].startup();
        datagenerators[i] =
            std::thread(&Engine::datagen, &Engines[i], games, outputfile);
      }
      for (auto &thread : datagenerators) {
        thread.join();
      }
      return 0;
    }
  }
  Engine Prolix;
  Prolix.startup();
  getline(std::cin, proto);
  if (proto == "uci") {
    std::cout << uciinfostring;
    while (true) {
      Prolix.uci();
    }
  }
  if (proto == "xboard") {
    while (true) {
      Prolix.xboard();
    }
  }
  return 0;
}
