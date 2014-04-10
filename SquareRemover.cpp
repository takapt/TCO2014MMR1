#define NDEBUG

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>
#include <climits>
#include <cfloat>
#include <ctime>
#include <cassert>
#include <map>
#include <utility>
#include <set>
#include <iostream>
#include <memory>
#include <string>
#include <vector>
#include <algorithm>
#include <functional>
#include <sstream>
#include <complex>
#include <stack>
#include <queue>
#include <numeric>
#include <list>
#include <iomanip>
#include <fstream>
#include <bitset>


using namespace std;

#define foreach(it, c) for (__typeof__((c).begin()) it=(c).begin(); it != (c).end(); ++it)
template <typename T> void print_container(ostream& os, const T& c) { const char* _s = " "; if (!c.empty()) { __typeof__(c.begin()) last = --c.end(); foreach (it, c) { os << *it; if (it != last) os << _s; } } }
template <typename T> ostream& operator<<(ostream& os, const vector<T>& c) { print_container(os, c); return os; }
template <typename T> ostream& operator<<(ostream& os, const set<T>& c) { print_container(os, c); return os; }
template <typename T> ostream& operator<<(ostream& os, const multiset<T>& c) { print_container(os, c); return os; }
template <typename T> ostream& operator<<(ostream& os, const deque<T>& c) { print_container(os, c); return os; }
template <typename T, typename U> ostream& operator<<(ostream& os, const map<T, U>& c) { print_container(os, c); return os; }
template <typename T, typename U> ostream& operator<<(ostream& os, const pair<T, U>& p) { os << "(" << p.first << ", " << p.second << ")"; return os; }

template <typename T> void print(T a, int n, const string& split = " ") { for (int i = 0; i < n; i++) { cerr << a[i]; if (i + 1 != n) cerr << split; } cerr << endl; }
template <typename T> void print2d(T a, int w, int h, int width = -1, int br = 1) { for (int i = 0; i < h; ++i) { for (int j = 0; j < w; ++j) { if (width != -1) cerr.width(width); cerr << a[i][j] << ' '; } cerr << endl; } while (br--) cerr << endl; }
template <typename T> void input(T& a, int n) { for (int i = 0; i < n; ++i) cin >> a[i]; }
#define dump(v) (cerr << #v << ": " << v << endl)

#define rep(i, n) for (int i = 0; i < (int)(n); ++i)
#define all(a) (a).begin(), (a).end()
#define clr(a, x) memset(a, x, sizeof(a))
#define sz(a) ((int)(a).size())
#define mp(a, b) make_pair(a, b)
#define ten(n) ((long long)(1e##n))

template <typename T, typename U> void upmin(T& a, const U& b) { a = min<T>(a, b); }
template <typename T, typename U> void upmax(T& a, const U& b) { a = max<T>(a, b); }
template <typename T> void uniq(T& a) { sort(a.begin(), a.end()); a.erase(unique(a.begin(), a.end()), a.end()); }
template <class T> string to_s(const T& a) { ostringstream os; os << a; return os.str(); }
template <class T> T to_T(const string& s) { istringstream is(s); T res; is >> res; return res; }
void fast_io() { cin.tie(0); ios::sync_with_stdio(false); }
bool in_rect(int x, int y, int w, int h) { return 0 <= x && x < w && 0 <= y && y < h; }
bool in_sq(int x, int y, int n) { return in_rect(x, y, n, n); }

typedef long long ll;
typedef pair<int, int> pint;



typedef unsigned int uint;
typedef unsigned short ushort;
typedef unsigned char uchar;

uint pss(uint first, uint second) { return (first << 16) | second; }
ushort pcc(uchar first, uchar second) { return (first << 8) | second; }
ushort pss_first(uint pair) { return pair >> 16; }
ushort pss_second(uint pair) { return pair & 0xffff; }
uchar pcc_first(ushort pair) { return pair >> 8; }
uchar pcc_second(ushort pair) { return pair & 0xff; }


///
const int dir_dx[] = { 0, 1, 0, -1 };
const int dir_dy[] = { 1, 0, -1, 0 };
enum Dir
{
    DOWN,
    RIGHT,
    UP,
    LEFT,

    NA,
};
Dir rev_dir(Dir dir)
{
    return Dir((dir + 2) % 4);
}

class Action
{
public:
    Action(int x, int y, Dir dir)
        : x(x), y(y), dir(dir)
    {
    }

    int x, y;
    Dir dir;
};

const int rect_dx[] = { 0, 1, 0, 1 };
const int rect_dy[] = { 0, 0, 1, 1 };

class Board
{
public:
    Board(int colors, const vector<string>& board, vector<int>* buffer)
        : n(board.size()), colors(colors), buffer(buffer), score(0), buffer_index(0)
    {
        rep(y, n) rep(x, n)
            this->board[y][x] = board[y][x] - '0';
        adjust();
    }

    int get_score() const
    {
        return score;
    }

    int size() const
    {
        return n;
    }

    int at(int x, int y) const
    {
        assert(in_sq(x, y, n));
        return board[y][x];
    }

private:
    typedef priority_queue<uint, vector<uint>, greater<uint>> PQ;
    void push_q(int tx, int ty, PQ& q) const
    {
        rep(i, 4)
        {
            int x = tx - rect_dx[i];
            int y = ty - rect_dy[i];
            if (in_sq(x, y, n - 1) && all_same(x, y))
                q.push(pss(y, x));
        }
    }
    void adjust(PQ& q)
    {
        while (!q.empty())
        {
//             int ty = q.top().first, tx = q.top().second;
            int ty = pss_first(q.top());
            int tx = pss_second(q.top());
            q.pop();

            if (all_same(tx, ty))
            {
                ++score;
                rep(i, 4)
                {
                    int x = tx + rect_dx[i];
                    int y = ty + rect_dy[i];
                    assert(buffer_index < buffer->size());
                    board[y][x] = (*buffer)[buffer_index++];
                }

                rep(i, 4)
                {
                    int x = tx + rect_dx[i];
                    int y = ty + rect_dy[i];
                    push_q(x, y, q);
                }
            }
        }
    }
    void adjust()
    {
        PQ q;
        rep(y, n - 1) rep(x, n - 1)
            if (all_same(x, y))
                q.push(pss(y, x));
        adjust(q);
    }
public:
    void move(const Action& action)
    {
        int x1 = action.x;
        int y1 = action.y;
        int x2 = x1 + dir_dx[action.dir];
        int y2 = y1 + dir_dy[action.dir];
        assert(in_sq(x1, y1, n));
        assert(in_sq(x2, y2, n));
        swap(board[y1][x1], board[y2][x2]);

        PQ q;
        push_q(x1, y1, q);
        push_q(x2, y2, q);
        adjust(q);
    }

    string to_s() const
    {
        string res;
        rep(y, n)
        {
            rep(x, n)
                res += board[y][x] + '0';
            res += "\n";
        }
        return res;
    }

private:
    int n;
    int colors;
    vector<int>* buffer;
    int buffer_index;

    int board[16][16];
    int score;

    bool all_same(int tx, int ty) const
    {
        int c = board[ty][tx];
        rep(i, 4)
        {
            int x = tx + rect_dx[i];
            int y = ty + rect_dy[i];
            assert(in_sq(x, y, n));
            if (board[y][x] != c)
                return false;
        }
        return true;
    }
};

const int MAX_MOVES = ten(4);

class Solver
{
public:
    Solver(int colors, const Board& init_board)
        : init_board(init_board), n(init_board.size()), colors(colors)
    {
    }

    vector<Action> solve()
    {
        vector<Node> stages[MAX_MOVES + 1];
        stages[0].push_back(Node(init_board, vector<Action>(), -1, -1));

        rep(moves, MAX_MOVES)
        {
            const int beam_width = 1;

            auto& stage = stages[moves];
            sort(all(stage));
            if (stage.size() > beam_width)
                stage.erase(stage.begin() + beam_width, stage.end());

//             dump(moves);

            rep(node_i, stage.size())
            {
                const Node& node = stage[node_i];

//                 int num_colors[6] = {};
//                 rep(y, n) rep(x, n)
//                     ++num_colors[node.board.at(x, y)];
//                 const int color = max_element(num_colors, num_colors + colors) - num_colors;

                rep(ty, n - 1) rep(tx, n - 1) rep(color, colors)
                {
                    int order[] = { 0, 1, 2, 3 };
//                     do
//                     {
                        Board board = node.board;
                        vector<Action> actions;
                        if (solve_actions(tx, ty, color, order, board, actions))
                        {
                            assert(actions.size() > 0);
                            int next_moves = moves + actions.size();
                            if (next_moves <= MAX_MOVES)
                            {
                                Node next_node(board, actions, moves, node_i);
                                stages[next_moves].push_back(next_node);
                                sort(all(stages[next_moves]));
                                if (stages[next_moves].size() > beam_width)
                                    stages[next_moves].pop_back();
                            }
                        }
//                     } while (next_permutation(order, order + 4));
                }
            }
        }


        int best_score = -1, best_moves, best_index;
        rep(moves, MAX_MOVES + 1) rep(i, stages[moves].size())
        {
            int score = stages[moves][i].board.get_score();
            if (score > best_score)
            {
                best_score = score;
                best_moves = moves;
                best_index = i;
            }
        }
        assert(best_score >= 0);
        vector<Action> actions;
        for (int moves = best_moves, index = best_index; moves > 0; )
        {
            Node& node = stages[moves][index];
            auto& acts = node.actions;
            for (int i = sz(acts) - 1; i >= 0; --i)
                actions.push_back(acts[i]);

            moves = node.prev_moves;
            index = node.prev_index;
        }
        reverse(all(actions));
        while (actions.size() < MAX_MOVES)
            actions.push_back(Action(0, 0, RIGHT));
        return actions;
    }

private:
    bool solve_actions(int tx, int ty, int color, const int* order, Board& board, vector<Action>& res_actions)
    {
        assert(0 <= color && color < colors);
        assert(in_sq(tx, ty, n));

        res_actions.clear();

        bool fixed[16][16];
        rep(y, n) rep(x, n)
            fixed[y][x] = false;

        rep(i, 4)
        {
            int sx = tx + rect_dx[i];
            int sy = ty + rect_dy[i];
            assert(fixed[sy][sx] == false);

            vector<Action> acts;
            if (!solve_min_actions(board, sx, sy, color, fixed, acts))
                return false;

            for (auto& a : acts)
            {
                board.move(a);
                res_actions.push_back(a);
            }
//             if (board.at(sx, sy) != color)
//                 return false;

            fixed[sy][sx] = true;
        }
        return true;
    }
    bool solve_min_actions(const Board& board, int sx, int sy, int color, const bool fixed[16][16], vector<Action>& res_actions)
    {
        assert(in_sq(sx, sy, n));

        if (fixed[sy][sx] && board.at(sx, sy) != color)
            return false;

        if (board.at(sx, sy) == color)
            return true;

        const int inf = ten(7);
        int cost[16][16];
        Dir used_dir[16][16];
        rep(y, n) rep(x, n)
            cost[y][x] = inf;

        queue<pint> q;
        cost[sy][sx] = 0;
        q.push(pint(sx, sy));
        while (!q.empty())
        {
            const int cx = q.front().first, cy = q.front().second;
            q.pop();

            if (board.at(cx, cy) == color)
            {
                vector<Action> actions;
                for (int x = cx, y = cy; cost[y][x] > 0; )
                {
                    assert(cost[y][x] < inf);
                    Dir dir = rev_dir(used_dir[y][x]);
                    actions.push_back(Action(x, y, dir));

                    x += dir_dx[dir];
                    y += dir_dy[dir];
                }

                bool ok = true;
                Board b = board;
                for (auto& a : actions)
                {
                    if (b.at(a.x, a.y) != color)
                    {
                        ok = false;
                        break;
                    }
                    b.move(a);
                }
                if (ok)
                {
                    res_actions.insert(res_actions.end(), all(actions));
                    return true;
                }
            }

            const int ncost = cost[cy][cx] + 1;
            rep(dir, 4)
            {
                int nx = cx + dir_dx[dir];
                int ny = cy + dir_dy[dir];
                if (in_sq(nx, ny, n) && !fixed[ny][nx] && ncost < cost[ny][nx])
                {
                    cost[ny][nx] = ncost;
                    used_dir[ny][nx] = Dir(dir);
                    q.push(pint(nx, ny));
                }
            }
        }
        return false;
    }

private:
    const Board& init_board;
    const int n;
    const int colors;

    struct Node
    {
        Node(const Board& board, const vector<Action>& actions, int prev_moves, int prev_index)
            : board(board), actions(actions), prev_moves(prev_moves), prev_index(prev_index)
        {
        }

        bool operator<(const Node& other) const
        {
            return board.get_score() > other.board.get_score();
        }

        Board board;
        vector<Action> actions;
        int prev_moves;
        int prev_index;
    };
};

class SquareRemover
{
public:
    vector<int> playIt(int colors, vector<string> _board, int startSeed)
    {
        vector<int> buffer = make_buffer(startSeed, colors);
        Board board(colors, _board, &buffer);

        Solver solver(colors, board);
        vector<Action> actions = solver.solve();
        return make_result(actions);
    }

    vector<int> make_result(const vector<Action>& actions)
    {
        vector<int> res;
        for (auto& a : actions)
        {
            res.push_back(a.y);
            res.push_back(a.x);

            int dir;
            switch (a.dir)
            {
                case UP:
                    dir = 0;
                    break;
                case RIGHT:
                    dir = 1;
                    break;
                case DOWN:
                    dir = 2;
                    break;
                case LEFT:
                    dir = 3;
                    break;
                default:
                    abort();
            }
            res.push_back(dir);
        }
        return res;
    }

    vector<int> make_buffer(int seed, int colors)
    {
        const int len = ten(4) * 4 * 10;
        vector<int> buffer(len);
        ll a = seed;
        rep(i, len)
        {
            buffer[i] = a % colors;
            a = (a * 48271) % 2147483647;
        }
        return buffer;
    }
};

#ifdef LOCAL
int main()
{
    int colors;
    cin >> colors;

    int n;
    cin >> n;
    vector<string> board(n);
    rep(i, n)
        cin >> board[i];

    int startSeed;
    cin >> startSeed;

    vector<int> res = SquareRemover().playIt(colors, board, startSeed);

    rep(i, 30000)
        cout << res[i] << endl;
    cout.flush();
}
#endif
