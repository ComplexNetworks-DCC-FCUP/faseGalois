/* -------------------------------------------------

//                                                 
//  88888888888           ad88888ba   88888888888  
//  88                   d8"     "8b  88           
//  88                   Y8,          88           
//  88aaaaa  ,adPPYYba,  `Y8aaaaa,    88aaaaa      
//  88"""""  ""     `Y8    `"""""8b,  88"""""      
//  88       ,adPPPPP88          `8b  88           
//  88       88,    ,88  Y8a     a8P  88           
//  88       `"8bbdP"Y8   "Y88888P"   88888888888  
//                                                 
//

Pedro {Paredes, Ribeiro} - DCC/FCUP
----------------------------------------------------
Isomorphism Utilities

Adapted from gtrieScanner - http://www.dcc.fc.up.pt/gtries/

---------------------------------------------------- */

#ifndef _ISOMORPHISM_
#define _ISOMORPHISM_

#define MAXS 200

// Limits for subgraph size
#define MIN_MOTIF_SIZE  3
#define MAX_MOTIF_SIZE 50
#define MAXMOTIF 20

#define MAXMAT 10000

//#include "Graph.h"

#define MAXN MAX_MOTIF_SIZE
#define WORKSPACE_SIZE MAXN*160

#include "tnauty.h"
#include "Galois/Graph/Graph.h"

typedef Galois::Graph::FirstGraph<int, int, false> Graph;
typedef Graph::GraphNode GNode;

class Isomorphism {
 private:  
  static bool dir;
  static setword workspace[WORKSPACE_SIZE];
  static int n,m, lab[MAXN], ptn[MAXN], orbits[MAXN];
  static set *gv;
  static graphnau g[MAXN*MAXM];

  /*static void _goCan(int x, int pos, const char *in, 
		     char *perm, char *used,
		     char *current, char *best, int size);

  static void _goCan2(int pos, const char *in, int *perm, bool *used, char *best, int size, char *current);*/
    
 public:
  static void initNauty(int size, bool dir);
  static void finishNauty();

  static void canonicalStrNauty(std::string v, char *s);

  /*static void canonicalNauty(const char *in, char *out, int size);
  static void canonicalBigger(const char *in, char *out, int size);
  static void canonicalBigger2(const char *in, char *out, int size);
  static void canonicalBasedNauty(const char *in, char *out, int size); // GT Canon
  static void canonicalBasedNautyReverse(const char *in, char *out, int size);
  static void canonicalRandom(const char *in, char *out, int size);*/
};

#endif


