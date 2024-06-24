/*
	File: ATC-dp_b.cpp
	Date and Time Created: 2024-03-13 13:46:34
	Author: Rahul M. Navneeth
*/

/* ----------------- HEADER FILES ----------------- */

#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>

/* ----------------- NAMESPACE ----------------- */

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/* ----------------- TEMPLATES ------------------ */

/* clang-format off */

// TRIGGER
bool M_TIME = 0;

// MACROS
#define fast_io ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL);
#define io freopen("./input.txt", "r", stdin); freopen("./output.txt", "w", stdout); freopen("./output.txt", "w", stderr);
#define endl '\n'
#define LINF LLONG_MAX
#define INF INT_MAX
#define mpa make_pair

// TYPEDEF
typedef long long ll;
typedef unsigned long long ull;
typedef long double lld;
typedef tree<ll, null_type, less<ll>, rb_tree_tag, tree_order_statistics_node_update> pbds; // POLICY BASED DS

// SHORTCUTS
#define vi vector<int>
#define vvi vector<vector<int>>
#define pii pair<int, int>
#define ar array
#define pb push_back
#define pob pop_back
#define all(x) x.begin(), x.end()
#define sz(x) (int)(x.size())
#define F first
#define S second

// DEBUGGING
void dbg(ll t) { cout << t; }
void dbg(int t) { cout << t; }
void dbg(string t) { cout << t; }
void dbg(char t) { cout << t; }
void dbg(lld t) { cout << t; }
void dbg(double t) { cout << t; }
void dbg(ull t) { cout << t; }

template <class T, class V> void dbg(pair<T, V> p);
template <class T> void dbg(vector<T> v);
template <class T> void dbg(set<T> v);
template <class T, class V> void dbg(map<T, V> v);
template <class T> void dbg(multiset<T> v);

template <class T, class V> void dbg(pair<T, V> p) { cout << "{ "; dbg(p.F); cout << " : "; dbg(p.S); cout << " }"; }
template <class T> void dbg(vector<T> v) { cout << "[ "; for (T i : v) { dbg(i); cout << " "; } cout << "]"; }
template <class T> void dbg(set<T> v) { cout << "[ "; for (T i : v) { dbg(i); cout << " "; } cout << "]"; }
template <class T> void dbg(multiset<T> v) { cout << "[ "; for (T i : v) { dbg(i); cout << " "; } cout << "]"; }
template <class T, class V> void dbg(map<T, V> v) { cout << "[ "; for (auto i : v) { dbg(i); cout << " "; } cout << "]"; }
void dbg(pbds v) { cout << "[ "; for (auto i : v) { dbg(i); cout << " "; } cout << "]"; }

// FUNCTIONS
#define REP(i, a, b) for (int i = a; i < b; i++)
#define REPR(i, a, b) for (int i = a; i >= b; i--)
#define UNIQUE_SORT(v) sort(all(v)); v.erase(unique(all(v)), v.end())
mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());
void swap(int &x, int &y) { int temp = x; x = y; y = temp; }
ll combination(ll n, ll r, ll m, ll *fact, ll *ifact) { ll val1 = fact[n]; ll val2 = ifact[n - r]; ll val3 = ifact[r]; return (((val1 * val2) % m) * val3) % m; }
bool revsort(ll a, ll b) {return a > b;}
ll phin(ll n) {ll number = n; if (n % 2 == 0) {number /= 2; while (n % 2 == 0) n /= 2;} for (ll i = 3; i <= sqrt(n); i += 2) {if (n % i == 0) {while (n % i == 0)n /= i; number = (number / i * (i - 1));}} if (n > 1)number = (number / n * (n - 1)) ; return number;} //O(sqrt(N))
ll getRandomNumber(ll l, ll r) {return uniform_int_distribution<ll>(l, r)(rng);} 
vector<ll> sieve(int n) {int*arr = new int[n + 1](); vector<ll> vect; for (int i = 2; i <= n; i++)if (arr[i] == 0) {vect.push_back(i); for (int j = 2 * i; j <= n; j += i)arr[j] = 1;} return vect;}
ll modpow(ll a, ll b, ll MOD) { ll res = 1; while(b > 0) { if(b & 1) { res = (res * a) % MOD; } b = b >> 1; a = (a*a) % MOD; } return res; }
void extendgcd(ll a, ll b, ll *v) { if (b == 0) { v[0] = 1; v[1] = 0; v[2] = a; return; }
extendgcd(b, a % b, v); ll x = v[1]; v[1] = v[0] - v[1] * (a / b); v[0] = x; return; } // PASS AN ARRY OF SIZE1 3
ll mminv(ll a, ll b) { ll arr[3]; extendgcd(a, b, arr); return arr[0]; } // FOR NON PRIME B
ll mminvprime(ll a, ll b) { return modpow(a, b - 2, b); }
ll mod_add(ll a, ll b, ll m) { a = a % m; b = b % m; return (((a + b) % m) + m) % m; }
ll mod_mul(ll a, ll b, ll m) { a = a % m; b = b % m; return (((a * b) % m) + m) % m; }
ll mod_sub(ll a, ll b, ll m) { a = a % m; b = b % m; return (((a - b) % m) + m) % m; }
ll mod_div(ll a, ll b, ll m) { a = a % m; b = b % m; return (mod_mul(a, mminvprime(b, m), m) + m) % m; } // ONLY FOR PRIME M
void precision(int a) { cout << setprecision(a) << fixed; }

// CONSTANTS
const float PI = 3.141592653589793238462;
const int MOD = 1e9 + 7;
const int mxn = 1e7;

/* clang-format on */

/* --------------------- CODE BEGINS ---------------------- */

void solve() {
    int N, K; cin >> N >> K;
    int a[N];
    for(int i = 0 ; i < N ; i++) cin >> a[i];
    int dp[N];
    fill(dp, dp+N, INT_MAX);
    dp[0] = 0;
    for(int i = 1 ; i < N ; i++) {
        for(int j = 1 ; j <= min(i, K) ; j++) {
            dp[i] = min(dp[i], dp[i-j] + abs(a[i-j]-a[i]));
        }
    }
    cout << dp[N-1] << "\n";
    return;
}

/*---------------------- MAIN DRIVER ------------------------*/

// MAIN
int32_t main() {
  fast_io;
  io;
  high_resolution_clock::time_point start, end;
  if(M_TIME) start = chrono::high_resolution_clock::now();
  int t = 1;
  // cin >> t;
  while (t--) solve();
  if(M_TIME) {
    end = chrono::high_resolution_clock::now();
    auto duration = chrono::duration_cast<chrono::milliseconds>(end - start);
    cout << "RUNTIME: " << duration.count() << " ms\n";
  }
  return 0;
}
