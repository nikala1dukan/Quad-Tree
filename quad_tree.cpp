//#pragma GCC optimize("O3,unroll-loops")
#define VISUAL
#ifdef VISUAL
#include <limits>
#include <vector>
#include <iostream>
#include <iomanip>
#include <cstdint>
#include <map>
#include <random>
#include <chrono>
#include <algorithm>
#include <functional>
#include <string>
#include <set>
#include <queue>
#include <fstream>
#include <time.h>
#include <bitset>
#include <climits>
#include <cassert>
#else
#include <bits/stdc++.h>

#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>

using namespace __gnu_pbds;
template <typename T, typename S>

using ordered_set = tree<T, null_type, S, rb_tree_tag, tree_order_statistics_node_update>;

#endif

//#pragma GCC target("avx2,bmi,bmi2,popcnt,lzcnt,fma,abm")
// #pragma GCC optimaze("trapv")

using namespace std;

#define int int32_t
#define all(a) a.begin(),a.end()
using uint = uint32_t;
using ll = int64_t;
using ull = uint64_t;
using ld = double;
using ldl = long double;
using pii = pair<int, int>;
using pll = pair<ll, ll>;

constexpr ldl PI = 3.141592653589793238462643383279502884L;

// #define int ll

const int mod = 1'000'000'007;
const int ugly = 998'244'353;

template <typename T>
istream &operator>>(istream &in, pair<T, T> &p)
{
    in >> p.first >> p.second;
    return in;
}
template <typename T>
ostream &operator<<(ostream &out, const pair<T, T> &p)
{
    out << p.first << ' ' << p.second;
    return out;
}
template <typename T>
istream &operator>>(istream &in, vector<T> &v)
{
    for (T &i : v)
        in >> i;
    return in;
}
template <typename T>
ostream &operator<<(ostream &out, const vector<T> &v)
{
    for (const T &i : v)
        out << i << ' ';
    return out;
}

ll binpow(ll x, ll pow, int m)
{
    if (pow == 0)
        return 1 % m;
    ll res = binpow(x, pow >> 1, m);
    res = (ll)res * res % m;
    if (pow & 1)
        res = (ll)res * x % m;
    return res;
}

ll inv(ll x, int prime)
{
    return binpow(x % prime, prime - 2, prime);
}

template <typename T>
bool is_prime(T x)
{
    if (x == 1)
    {
        return false;
    }
    for (T d = 2; d * d <= x; d++)
    {
        if (x % d == 0)
            return false;
    }
    return true;
}

template <typename T>
struct VEC
{
    T x, y;

    VEC() {};

    VEC(T a, T b) : x(a), y(b) {};

    template <typename U>
    VEC(const VEC<U> &other) : x(other.x), y(other.y){};

    VEC<T> operator+(const VEC &a) const
    {
        return VEC(this->x + a.x, this->y + a.y);
    }

    VEC<T> &operator=(const VEC &a)
    {
        x = a.x;
        y = a.y;
        return *this;
    }

    VEC<T> operator/(T a) const
    {
        return VEC(this->x / a, this->y / a);
    }

    VEC<T> operator-(const VEC &a) const
    {
        return VEC(this->x - a.x, this->y - a.y);
    }

    VEC &operator-=(VEC &a)
    {
        x -= a.x;
        y -= a.y;
        return *this;
    }

    VEC &operator+=(VEC &a)
    {
        x += a.x;
        y += a.y;
        return *this;
    }

    VEC operator-() const
    {
        return VEC(-this->x, -this->y);
    }

    T operator*(const VEC &a) const
    {
        return this->x * a.x + this->y * a.y;
    }

    VEC operator*(ldl a)
    {
        return VEC(this->x * a, this->y * a);
    }

    VEC operator*(ll a)
    {
        return VEC(this->x * a, this->y * a);
    }

    T operator^(const VEC &a) const
    {
        return this->x * a.y - this->y * a.x;
    }

    bool operator>(const VEC &a) const
    {
        return this->y > a.y || (this->y == a.y && this->x > a.x);
    }
    bool operator<(const VEC &a) const
    {
        return this->y < a.y || (this->y == a.y && this->x < a.x);
    }
    bool operator==(const VEC &a) const
    {
        return this->x == a.x && this->y == a.y;
    }
    T dist2() const
    {
        return this->x * this->x + this->y * this->y;
    }
    T dist2(const VEC<T> a) const
    {
        return (this->x - a.x) * (this->x - a.x) + (this->y - a.y) * (this->y - a.y);
    }
    bool operator!=(const VEC &a) const
    {
        return this->x != a.x || this->y != a.y;
    }

    VEC<T> rotate90() {
        return {-y, x};
    }
};

template <typename T>
struct LINE
{
    ll a, b, c;
    LINE() {};
    LINE(ll _a, ll _b, ll _c) : a(_a), b(_b), c(_c) {};
    template <typename U>
    LINE(const VEC<U> &u, const VEC<U> &v) : a(u.y - v.y), b(v.x - u.x), c(-a * u.x - b * u.y){};
    template <typename U>
    LINE(const LINE<U> &other) : a(other.a), b(other.b), c(other.c){};

    VEC<T> normal() const
    {
        return VEC<T>(a, b);
    };
    VEC<T> forward() const
    {
        return VEC<T>(-b, a);
    };
};

template <typename T>
ldl polar(VEC<T> a, VEC<T> b)
{
    ldl ret = atan2(b ^ a, a * b);
    return (ret > 0 ? ret : 2 * PI + ret);
}

template <typename T>
ldl angle(VEC<T> a, VEC<T> b)
{
    return abs(atan2(a ^ b, a * b));
}

template <typename T>
ldl dist(VEC<T> a, VEC<T> b)
{
    return sqrtl((a.x - b.x) * (a.x - b.x) + (a.y - b.y) * (a.y - b.y));
}

template <typename T>
ldl dist(LINE<T> u, VEC<T> v)
{
    return (ldl)abs(u.a * v.x + u.b * v.y + u.c) / sqrt(u.a * u.a + u.b * u.b);
}

template <typename T>
istream &operator>>(istream &in, VEC<T> &a)
{
    in >> a.x >> a.y;
    return in;
}

template <typename T>
ostream &operator<<(ostream &out, const VEC<T> &a)
{
    out << a.x << ' ' << a.y;
    return out;
}

template <typename T>
istream &operator>>(istream &in, LINE<T> &a)
{
    in >> a.a >> a.b >> a.c;
    return in;
}

template <typename T>
ostream &operator<<(ostream &out, const LINE<T> &a)
{
    out << a.a << ' ' << a.b << ' ' << a.c;
    return out;
}

template <typename T>
int sign(T a)
{
    return (a < 0 ? -1 : (a > 0 ? 1 : 0));
}

template <typename T>
bool seginters(const VEC<T> &st1, const VEC<T> &fn1, const VEC<T> &st2, const VEC<T> &fn2)
{
    if (st1 == fn1 && st2 == fn2)
        return st1 == st2;
    VEC<T> dot = st1 - st2;
    VEC<T> dot2 = st1 - fn2;
    VEC<T> v = fn2 - st2;
    VEC<T> u = st2 - fn2;
    if (fn2 != st2 && (dot ^ v) == 0 && (dot * v) >= 0 && (dot2 ^ u) == 0 && (dot2 * u) >= 0)
        return true;
    dot = st2 - st1;
    dot2 = st2 - fn1;
    v = fn1 - st1;
    u = st1 - fn1;
    if (fn1 != st1 && (dot ^ v) == 0 && (dot * v) >= 0 && (dot2 ^ u) == 0 && (dot2 * u) >= 0)
        return true;
    dot = fn2 - st1;
    dot2 = fn2 - fn1;
    v = fn1 - st1;
    u = st1 - fn1;
    if (fn1 != st1 && (dot ^ v) == 0 && (dot * v) >= 0 && (dot2 ^ u) == 0 && (dot2 * u) >= 0)
        return true;
    dot = fn1 - st2;
    dot2 = fn1 - fn2;
    v = fn2 - st2;
    u = st2 - fn2;
    if (fn2 != st2 && (dot ^ v) == 0 && (dot * v) >= 0 && (dot2 ^ u) == 0 && (dot2 * u) >= 0)
        return true;

    return sign((st2 - st1) ^ (fn1 - st1)) != sign((fn2 - st1) ^ (fn1 - st1)) && sign((st1 - st2) ^ (fn2 - st2)) != sign((fn1 - st2) ^ (fn2 - st2));
}

bool parallel(const LINE<ldl> &l1, const LINE<ldl> &l2)
{
    return (l1.normal() ^ l2.normal()) == 0;
}

template <typename T>
bool lies_on(const VEC<T> &dot, const LINE<T> l)
{
    ldl p = l.a * dot.x + l.b * dot.y + l.c;
    return l.a * dot.x + l.b * dot.y + l.c == 0;
}

bool same_lines(const LINE<ldl> &l1, const LINE<ldl> &l2)
{
    VEC<ldl> dot = (l1.a == 0 ? VEC<ldl>{0., -(ldl)l1.c / l1.b} : VEC<ldl>{-(ldl)l1.c / l1.a, 0.});
    return (parallel(l1, l2) && lies_on(dot, l2));
}

VEC<ldl> lines_point_inters(const LINE<ldl> &l1, const LINE<ldl> &l2)
{
    vector<ldl> r1{(ldl)l1.a, (ldl)l1.b, -(ldl)l1.c}, r2{(ldl)l2.a, (ldl)l2.b, -(ldl)l2.c};
    if (l1.a == 0)
        swap(r1, r2);
    if (r1[0] != 0)
    {
        ldl p = r1[0];
        for (ldl &x : r1)
            x /= p;
        ldl c = r2[0];
        for (int i = 0; i < 3; i++)
        {
            r2[i] -= r1[i] * c;
        }
    }
    if (r2[1] != 0)
    {
        ldl p = r2[1];
        for (ldl &x : r2)
            x /= p;
        ldl c = r1[1];
        for (int i = 1; i < 3; i++)
        {
            r1[i] -= r2[i] * c;
        }
    }
    return VEC<ldl>(r1[2], r2[2]);
}

template <typename T>
bool is_under_line(LINE<T> &l, VEC<T> &v)
{
    if (l.b == 0)
    {
        return l.a * v.x > -l.c;
    }
    if (l.b > 0)
    {
        return l.a * v.x + l.b * v.y + l.c < 0;
    }
    return l.a * v.x + l.b * v.y + l.c > 0;
}

bool ononeline(VEC<ll> &a, VEC<ll> &b, VEC<ll> &c)
{
    return (((a - b) ^ (c - b)) == 0);
}

template <typename T>
struct VEC3
{
    T x = 0;
    T y = 0;
    T z = 0;

    VEC3() = default;

    template <typename S>
    VEC3(S xx, S yy, S zz) : x(xx), y(yy), z(zz)
    {
    }

    T operator*(const VEC3 &a) const
    {
        return this->x * a.x + this->y * a.y + this->z * a.z;
    }

    VEC3<T> operator^(const VEC3 &a) const
    {
        return VEC3<T>(-z * a.y + y * a.z, z * a.x - x * a.z, -y * a.x + x * a.y);
    }

    T dist2()
    {
        return x * x + y * y + z * z;
    }
};

template <typename T>
T mixedproduct(const VEC3<T> &a, const VEC3<T> &b, const VEC3<T> &c)
{
    return a * (b ^ c);
}

template <typename T>
VEC3<T> operator+(const VEC3<T> &a, const VEC3<T> &b)
{
    return VEC3<T>(a.x + b.x, a.y + b.y, a.z + b.z);
}

template <typename T>
VEC3<T> operator-(const VEC3<T> &a, const VEC3<T> &b)
{
    return VEC3<T>(a.x - b.x, a.y - b.y, a.z - b.z);
}

template <typename T>
istream &operator>>(istream &in, VEC3<T> &a)
{
    in >> a.x >> a.y >> a.z;
    return in;
}

template <typename T>
ostream &operator<<(ostream &out, const VEC3<T> &a)
{
    out << a.x << ' ' << a.y << ' ' << a.z;
    return out;
}

void idle()
{
    while (true)
    {
    }
}

template <typename T>
struct DCEL_HULL
{
    vector<VEC3<T>> coords;
    vector<int> ord;
    vector<int> faces;
    vector<pair<int, int>> bgen;
    vector<int> nxt;
    vector<int> twin;
    vector<int> eface;
    vector<int> deleted;

    bool in_itriangle(VEC<T> dot, VEC<T> v1, VEC<T> v2, VEC<T> v3)
    {
        return (abs((v2 - v1) ^ (v3 - v1))) == (abs((v2 - dot) ^ (v3 - dot)) + abs((v1 - dot) ^ (v3 - dot)) + abs((v1 - dot) ^ (v2 - dot)));
    }

    bool is_visible(int fc, const VEC3<T> &dot)
    {
        VEC3<T> perp = (coords[ord[bgen[faces[fc]].second]] - coords[ord[bgen[faces[fc]].first]]) ^ (coords[ord[bgen[nxt[faces[fc]]].second]] - coords[ord[bgen[nxt[faces[fc]]].first]]);
        T in_plane = perp * (dot - coords[ord[bgen[faces[fc]].first]]);
        if (in_plane > 0)
        {
            return true;
        }
        else if (in_plane < 0)
        {
            return false;
        }
        VEC3<T> v1 = coords[ord[bgen[faces[fc]].first]];
        VEC3<T> v2 = coords[ord[bgen[faces[fc]].second]];
        VEC3<T> v3 = coords[ord[bgen[nxt[faces[fc]]].second]];

        bool in = in_itriangle(VEC<T>(dot.y, dot.z), VEC<T>(v1.y, v1.z), VEC<T>(v2.y, v2.z), VEC<T>(v3.y, v3.z)) && in_itriangle(VEC<T>(dot.x, dot.z), VEC<T>(v1.x, v1.z), VEC<T>(v2.x, v2.z), VEC<T>(v3.x, v3.z)) && in_itriangle(VEC<T>(dot.x, dot.y), VEC<T>(v1.x, v1.y), VEC<T>(v2.x, v2.y), VEC<T>(v3.x, v3.y));
        return !in;
    }

    void add_point(int ind)
    {
        auto dot = coords[ord[ind]];

        vector<int> dnow;
        for (int fc = 0; fc < faces.size(); ++fc)
        {
            if (deleted[fc] == -1)
                continue;
            deleted[fc] = is_visible(fc, dot);
            if (deleted[fc])
                dnow.push_back(fc);
        }
        if (dnow.size() == 0)
        {
            return;
        }

        int edges[10 * ord.size()];
        int px = 0;

        for (auto fc : dnow)
        {
            int e = faces[fc];
            if (!deleted[eface[twin[e]]])
            {
                edges[px++] = e;
                break;
            }
            e = nxt[e];
            if (!deleted[eface[twin[e]]])
            {
                edges[px++] = e;
                break;
            }
            e = nxt[e];
            if (!deleted[eface[twin[e]]])
            {
                edges[px++] = e;
                break;
            }
        }

        if (px == 0)
        {
            cout << "empty edges\n";
            exit(0);
        }

        while (px < 2 || edges[0] != edges[px - 1])
        {
            int e = nxt[edges[px - 1]];
            int cnt = 0;
            while (!(deleted[eface[e]] == 1 && !deleted[eface[twin[e]]]))
            {
                e = nxt[twin[e]];

                if (cnt > 10000)
                {
                    cout << "inf cycle next\n";
                    exit(0);
                }
                ++cnt;
            }
            edges[px++] = e;

            if (px > 10000)
            {
                cout << "inf cycle edges\n";
                exit(0);
            }
        }
        if (edges[0] == edges[px - 1])
            --px;

        int prev = -1;
        int forgotten = -1;
        for (int i = 0; i < px; ++i)
        {
            nxt[edges[i]] = bgen.size();
            bgen.emplace_back(bgen[edges[i]].second, ind);
            nxt.push_back(bgen.size());
            bgen.emplace_back(ind, bgen[edges[i]].first);
            nxt.push_back(edges[i]);

            eface[edges[i]] = faces.size();
            eface.push_back(faces.size());
            eface.push_back(faces.size());
            faces.push_back(edges[i]);

            deleted.push_back(0);
            // deleted[edges[i]] = 0;

            twin.push_back(-1);
            if (prev != -1)
            {
                twin[prev] = bgen.size() - 1;
                twin.push_back(prev);
            }
            else
            {
                twin.push_back(-1);
                forgotten = bgen.size() - 1;
            }
            prev = bgen.size() - 2;
        }
        if (forgotten == -1)
        {
            cout << "forgotten = -1\n";
            exit(0);
        }
        twin[forgotten] = bgen.size() - 2;
        twin[bgen.size() - 2] = forgotten;

        for (auto fc : dnow)
        {
            deleted[fc] = -1;
        }
    }

    bool on_line()
    {
        bool b1 = ((coords[ord[1]] - coords[ord[0]]) ^ (coords[ord[2]] - coords[ord[0]])).dist2() == 0;
        bool b2 = ((coords[ord[1]] - coords[ord[0]]) ^ (coords[ord[3]] - coords[ord[0]])).dist2() == 0;
        bool b3 = ((coords[ord[2]] - coords[ord[0]]) ^ (coords[ord[3]] - coords[ord[0]])).dist2() == 0;
        bool b4 = ((coords[ord[2]] - coords[ord[1]]) ^ (coords[ord[3]] - coords[ord[1]])).dist2() == 0;
        return b1 || b2 || b3 || b4;
    }

    DCEL_HULL(const vector<int> &inds, const vector<VEC3<T>> &dots) : coords(dots), ord(inds)
    {
        assert(dots.size() > 3 && inds.size() == dots.size());
        mt19937 gen(chrono::steady_clock().now().time_since_epoch().count());
        while (on_line())
        {
            shuffle(ord.begin(), ord.end(), gen);
        }
        bgen.reserve(10 * inds.size());
        twin.reserve(10 * inds.size());
        eface.reserve(10 * inds.size());
        faces.reserve(10 * inds.size());
        nxt.reserve(10 * inds.size());
        deleted.reserve(10 * inds.size());
        // face 0
        bgen.emplace_back(0, 1);
        bgen.emplace_back(1, 2);
        bgen.emplace_back(2, 0);
        nxt.push_back(1);
        nxt.push_back(2);
        nxt.push_back(0);
        VEC3<T> norm = (dots[ord[bgen[0].second]] - dots[ord[bgen[0].first]]) ^ (dots[ord[bgen[1].second]] - dots[ord[bgen[1].first]]);
        if (norm * (dots[ord[3]] - dots[ord[1]]) > 0)
        {
            swap(ord[0], ord[1]);
            // swap(bgen[0].first, bgen[0].second);
            // swap(bgen[1].first, bgen[1].second);
            // swap(bgen[2].first, bgen[2].second);
            // nxt[0] = 2;
            // nxt[2] = 1;
            // nxt[1] = 0;
        }
        faces.push_back(0);
        eface.assign(3, 0);
        // face 1
        bgen.emplace_back(bgen[1].second, bgen[1].first);
        bgen.emplace_back(bgen[1].first, 3);
        bgen.emplace_back(3, bgen[1].second);
        eface.push_back(1);
        eface.push_back(1);
        eface.push_back(1);
        faces.push_back(3);
        nxt.push_back(4);
        nxt.push_back(5);
        nxt.push_back(3);
        // face 2
        bgen.emplace_back(bgen[2].second, bgen[2].first);
        bgen.emplace_back(bgen[5].second, bgen[5].first);
        bgen.emplace_back(bgen[5].first, bgen[2].second);
        eface.push_back(2);
        eface.push_back(2);
        eface.push_back(2);
        faces.push_back(6);
        nxt.push_back(7);
        nxt.push_back(8);
        nxt.push_back(6);
        // face 3
        bgen.emplace_back(bgen[0].second, bgen[0].first);
        bgen.emplace_back(bgen[8].second, bgen[8].first);
        bgen.emplace_back(bgen[4].second, bgen[4].first);
        eface.push_back(3);
        eface.push_back(3);
        eface.push_back(3);
        faces.push_back(9);
        nxt.push_back(10);
        nxt.push_back(11);
        nxt.push_back(9);
        // twins
        twin.assign(12, 0);
        twin[0] = 9;
        twin[9] = 0;
        twin[1] = 3;
        twin[3] = 1;
        twin[2] = 6;
        twin[6] = 2;
        twin[4] = 11;
        twin[11] = 4;
        twin[5] = 7;
        twin[7] = 5;
        twin[8] = 10;
        twin[10] = 8;
        // hull
        deleted.assign(4, 0);
        for (int i = 4; i < ord.size(); ++i)
        {
            add_point(i);
        }
    }
};

template <typename T>
ldl dist2(const VEC3<T> &v1, const VEC3<T> &v2)
{
    return (v1.x - v2.x) * (v1.x - v2.x) + (v1.y - v2.y) * (v1.y - v2.y) + (v1.z - v2.z) * (v1.z - v2.z);
}

template <typename T>
vector<VEC<T>> minkowski_sum(const vector<VEC<T>> &pol1, const vector<VEC<T>> &pol2)
{
    assert(pol1.size() > 1 && pol2.size() > 1);
    vector<VEC<T>> ret;

    int sz1 = pol1.size(), sz2 = pol2.size();
    int px1 = 0, px2 = 0;
    for (int i = 0; i < sz1; i++)
    {
        if (pol1[px1].y < pol1[i].y || (pol1[px1].y == pol1[i].y && pol1[px1].x < pol1[i].x))
        {
            px1 = i;
        }
    }
    for (int i = 0; i < sz2; i++)
    {
        if (pol2[px2].y < pol2[i].y || (pol2[px2].y == pol2[i].y && pol2[px2].x < pol2[i].x))
        {
            px2 = i;
        }
    }
    int inc1 = 0, inc2 = 0;
    while (inc1 < sz1 || inc2 < sz2)
    {
        ret.push_back(pol1[(px1 + inc1) % sz1] + pol2[(px2 + inc2) % sz2]);
        T cross = (pol1[((px1 + inc1 + 1) % sz1)] - pol1[((px1 + inc1) % sz1)]) ^ (pol2[((px2 + inc2 + 1) % sz2)] - pol2[((px2 + inc2) % sz2)]);
        if (cross > 0)
        {
            ++inc1;
        }
        else if (cross < 0)
        {
            ++inc2;
        }
        else
        {
            ++inc1;
            ++inc2;
        }
    }

    return ret;
}

template <typename T>
T double_area(const vector<VEC<T>> &pol)
{
    T ret = 0;
    for (int i = 0; i < pol.size(); i++)
    {
        ret += pol[i] ^ pol[(i + 1) % pol.size()];
    }
    return ret;
}

// #define STRE

struct quadtree 
{
    struct node {
        int ind = -1;
        int ch[4] = {-1, -1, -1, -1};
        int cnt = 0;
    };
    vector<node> tree;
    vector<VEC<ldl>> dots;
    VEC<ldl> corner;
    ldl len;

    quadtree(const VEC<ldl>& corner_, ldl len_) : corner(corner_), len(len_), tree(1) {
    };

    int d;
    int add(const VEC<ldl>& dot) {
        dots.push_back(dot);
        d = 0;
        rec_add(0, corner, len, dots.size() - 1, true);
        return d;
    }

    void update(int ind) {
        tree[ind].cnt = (tree[ind].ind != -1);
        for (int i = 0; i < 4; i++)
        {
            if (tree[ind].ch[i] != -1) {
                tree[ind].cnt += tree[tree[ind].ch[i]].cnt;
            }
        }
    }

    int calc_quadrant(const VEC<ldl>& dot, VEC<ldl>* corn, ldl ln) {
        int p1 = dot.x < (corn->x + ln / 2);
        int p2 = dot.y < (corn->y + ln / 2);
        if (!p1) {
            corn->x += ln / 2;
        }
        if (!p2) {
            corn->y += ln / 2;
        }
        return (2 * p1) + p2;
    }

    void rec_add(int ind, VEC<ldl> corn, ldl ln, int dind, bool upd = false) {
        d += upd;
        if (tree[ind].cnt == 0) {
            tree[ind].ind = dind;
        } else {
            if (tree[ind].ind != -1) {
                VEC<ldl> ncorn = corn;
                int q = calc_quadrant(dots[tree[ind].ind], &ncorn, ln);
                if (tree[ind].ch[q] == -1) {
                    tree[ind].ch[q] = tree.size();
                    tree.emplace_back();
                }
                rec_add(tree[ind].ch[q], ncorn, ln / 2, tree[ind].ind);
                tree[ind].ind = -1;
            }
            int q = calc_quadrant(dots[dind], &corn, ln);
            if (tree[ind].ch[q] == -1) {
                tree[ind].ch[q] = tree.size();
                tree.emplace_back();
            }
            rec_add(tree[ind].ch[q], corn, ln / 2, dind, upd);
        }
        update(ind);
    }

    int readd = -1;
    VEC<ldl> gdot;
    void remove(const VEC<ldl>& dot) {
        gdot = dot;
        readd = -1;
        rec_remove(0, corner, len);
        if (readd != -1) {
            rec_add(0, corner, len, readd);
        }
    }

    void rec_remove(int ind, VEC<ldl> corn, ldl ln) {
        bool good = true;
        if (tree[ind].cnt == 2) {
            for (int i = 0; i < 4; i++)
            {
                if (tree[ind].ch[i] != -1 && tree[tree[ind].ch[i]].ind != -1) {
                    good = false;
                    if (dots[tree[tree[ind].ch[i]].ind] == gdot) {
                        tree[tree[ind].ch[i]].ind = -1;
                        tree[tree[ind].ch[i]].cnt = 0;
                    } else {
                        readd = tree[tree[ind].ch[i]].ind;
                        tree[tree[ind].ch[i]].ind = -1;
                        tree[tree[ind].ch[i]].cnt = 0;
                    }
                }
            }
        }
        if (good) {
            if (tree[ind].cnt == 1 && tree[ind].ind != -1) {
                tree[ind].ind = -1;
            } else {
                int q = calc_quadrant(gdot, &corn, ln);
                rec_remove(tree[ind].ch[q], corn, ln / 2);
            }
        }
        update(ind);
    }
};


signed main()
{
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    cout << fixed << setprecision(18);

    int t = 1;
    //cin >> t;
    while (t--)
    {
        int n;
        cin >> n;
        
        quadtree tree({0, 0}, 32);
        for (int i = 0; i < n; i++)
        {
            char type;
            VEC<ldl> dot;
            cin >> type >> dot;
            if (type == '+') {
                cout << tree.add(dot) << '\n';
            } else {
                tree.remove(dot);
            }
        }
        

    }
    return 0;
}
