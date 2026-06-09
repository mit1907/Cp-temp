/*
 * ╔══════════════════════════════════════════════════════════════╗
 * ║          COMPETITIVE PROGRAMMING TEMPLATE — C++              ║
 * ║          GitHub: https://github.com/mit1907/Cp-temp          ║
 * ╚══════════════════════════════════════════════════════════════╝
 *
 * 
 */

// ─── HEADERS ──────────────────────────────────────────────────
#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
using namespace std;
using namespace __gnu_pbds;

// ─── MACROS ───────────────────────────────────────────────────
#define int         long long
#define pb          push_back
#define ppb         pop_back
#define pf          push_front
#define ppf         pop_front
#define ff          first
#define ss          second
#define fi          first
#define se          second
#define all(x)      (x).begin(),(x).end()
#define rall(x)     (x).rbegin(),(x).rend()
#define sz(x)       (int)(x).size()
#define uniq(v)     (v).erase(unique(all(v)),(v).end())
#define yes         cout << "YES\n"
#define no          cout << "NO\n"
#define nl          '\n'
#define endl        "\n"             // cout flush avoid karta hai → fast output

// Fast I/O
#define FAST        ios::sync_with_stdio(false); cin.tie(nullptr)

// Loop shortcuts
#define FOR(i,a,b)  for(int i = (a); i < (b); i++)
#define FORR(i,a,b) for(int i = (a); i >= (b); i--)
#define REP(i,n)    FOR(i, 0, n)

// STL shortcuts
#define LB          lower_bound
#define UB          upper_bound
#define mxv(a)      *max_element(all(a))
#define mnv(a)      *min_element(all(a))
#define mxi(a)      max_element(all(a)) - (a).begin()
#define mni(a)      min_element(all(a)) - (a).begin()
#define SUM(a)      accumulate(all(a), 0LL)
#define REV(a)      reverse(all(a))

// Debug (contest mein comment out kar do)
#define dbg(x)      cerr << #x << " = " << x << nl
#define dbg2(x,y)   cerr << #x << "=" << x << "  " << #y << "=" << y << nl

// ─── TYPEDEFS ─────────────────────────────────────────────────
typedef long long           ll;
typedef unsigned long long  ull;
typedef long double         ld;
typedef pair<int,int>       pii;
typedef pair<int,int>       pi;
typedef pair<ll,ll>         pll;
typedef vector<int>         vi;
typedef vector<ll>          vll;
typedef vector<pii>         vpii;
typedef vector<pi>          vpi;
typedef vector<string>      vs;

// ─── POLICY-BASED DS (Order Statistics Tree) ──────────────────
// pbds s; s.insert(x);
// s.order_of_key(x)   → x se strictly chote elements ki count
// s.find_by_order(k)  → k-th smallest element (0-indexed)
typedef tree<int, null_type, less_equal<int>,
             rb_tree_tag, tree_order_statistics_node_update> pbds;

            
// ─── CONSTANTS ────────────────────────────────────────────────
const int   MOD  = 1e9 + 7;
const int   MOD2 = 998244353;
const int   INF  = 1e18;
const int   NEG  = -1e18;
const ld    PI   = acos((ld)-1);
const int   dx[] = {0, 0, 1, -1};    // 4-directional
const int   dy[] = {1, -1, 0, 0};
// const int dx[] = {0,0,1,-1,1,1,-1,-1};  // 8-directional
// const int dy[] = {1,-1,0,0,1,-1,1,-1};


// ─── UTILITY FUNCTIONS ────────────────────────────────────────

// Modular arithmetic
int mod(int a, int m = MOD)            { return ((a % m) + m) % m; }
int add(int a, int b, int m = MOD)     { return mod(a + b, m); }
int sub(int a, int b, int m = MOD)     { return mod(a - b, m); }
int mul(int a, int b, int m = MOD)     { return mod(a % m * (b % m), m); }

// Fast power → a^b % mod
int power(int a, int b, int m = MOD) {
    int res = 1; a %= m;
    while (b > 0) {
        if (b & 1) res = mul(res, a, m);
        a = mul(a, a, m);
        b >>= 1;
    }
    return res;
}

// Modular inverse (mod must be prime)
int inv(int a, int m = MOD) { return power(a, m - 2, m); }

// GCD / LCM
int gcd(int a, int b) { return b ? gcd(b, a % b) : a; }
int lcm(int a, int b) { return a / gcd(a, b) * b; }

// SIEVE OF ERATOSTHENES
// Usage: sieve() → fir isPrime[x] check karo
const int MAXN = 1e6 + 5;
vector<bool> isPrime(MAXN, true);
vi primes;

void sieve(int n = MAXN - 1) {
    isPrime[0] = isPrime[1] = false;
    for (int i = 2; i <= n; i++) {
        if (isPrime[i]) {
            primes.pb(i);
            for (ll j = (ll)i * i; j <= n; j += i)
                isPrime[j] = false;
        }
    }
}

// BINARY SEARCH HELPERS
// Pehli position jahan arr[pos] >= val
int loB(vi& arr, int val) { return lower_bound(all(arr), val) - arr.begin(); }
// Pehli position jahan arr[pos] > val
int upB(vi& arr, int val) { return upper_bound(all(arr), val) - arr.begin(); }

// GRAPH (Adjacency List) 
// Weighted: vector<pair<int,int>> adj[MAXN]
// solve() mein: adj.assign(n+1, {});

// BFS
vi bfs(int src, int n, vector<vi>& adj) {
    vi dist(n + 1, -1);
    queue<int> q;
    dist[src] = 0; q.push(src);
    while (!q.empty()) {
        int u = q.front(); q.pop();
        for (int v : adj[u])
            if (dist[v] == -1) { dist[v] = dist[u] + 1; q.push(v); }
    }
    return dist;
}

// DFS (iterative — stack overflow nahi hoga)
void dfs(int src, vector<vi>& adj, vi& visited) {
    stack<int> st;
    st.push(src); visited[src] = 1;
    while (!st.empty()) {
        int u = st.top(); st.pop();
        for (int v : adj[u])
            if (!visited[v]) { visited[v] = 1; st.push(v); }
    }
}

// UNION-FIND (DSU)
struct DSU {
    vi parent, rank_;
    DSU(int n) : parent(n+1), rank_(n+1, 0) { iota(all(parent), 0); }
    int find(int x) { return parent[x] == x ? x : parent[x] = find(parent[x]); }
    bool unite(int x, int y) {
        x = find(x); y = find(y);
        if (x == y) return false;
        if (rank_[x] < rank_[y]) swap(x, y);
        parent[y] = x;
        if (rank_[x] == rank_[y]) rank_[x]++;
        return true;
    }
    bool connected(int x, int y) { return find(x) == find(y); }
};

// ─── SEGMENT TREE (Range Sum + Point Update) ──────────────────
struct SegTree {
    int n; vll tree;
    SegTree(int n) : n(n), tree(4*n, 0) {}
    void update(int node, int s, int e, int i, ll val) {
        if (s == e) { tree[node] = val; return; }
        int mid = (s + e) / 2;
        if (i <= mid) update(2*node, s, mid, i, val);
        else          update(2*node+1, mid+1, e, i, val);
        tree[node] = tree[2*node] + tree[2*node+1];
    }
    ll query(int node, int s, int e, int l, int r) {
        if (r < s || e < l) return 0;
        if (l <= s && e <= r) return tree[node];
        int mid = (s + e) / 2;
        return query(2*node, s, mid, l, r) + query(2*node+1, mid+1, e, l, r);
    }
    void update(int i, ll val) { update(1, 0, n-1, i, val); }
    ll query(int l, int r)     { return query(1, 0, n-1, l, r); }
};

void solve() {
    // Write a code 

}
// ─── MAIN ─────────────────────────────────────────────────────
signed main() {
    FAST;
    int t=1;
    cin>>t;
    while (t--) solve();

    return 0;
}
