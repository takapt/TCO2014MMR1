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


typedef unsigned long long ull;
typedef unsigned int uint;
typedef unsigned short ushort;
typedef unsigned char uchar;

uint pss(uint first, uint second) { return (first << 16) | second; }
ushort pcc(uchar first, uchar second) { return (first << 8) | second; }
ushort pss_first(uint pair) { return pair >> 16; }
ushort pss_second(uint pair) { return pair & 0xffff; }
uchar pcc_first(ushort pair) { return pair >> 8; }
uchar pcc_second(ushort pair) { return pair & 0xff; }


template <typename T, int SIZE>
class Queue
{
public:
    Queue()
        : front_p(0), back_p(0)
    {
    }

    void push(T a)
    {
        assert(back_p < SIZE);
        data[back_p++] = a;
    }
    T& front()
    {
        return data[front_p];
    }
    void pop()
    {
        ++front_p;
    }
    int size() const
    {
        return back_p - front_p;
    }
    bool empty() const
    {
        return size() == 0;
    }
    void clear()
    {
        front_p = back_p = 0;
    }

private:
    T data[SIZE];
    int front_p, back_p;
};
template <typename T, int SIZE>
class PriorityQueue
{
public:
    PriorityQueue()
        : n(0)
    {
    }

    void push(const T& a)
    {
        data[n++] = a;
        up(n - 1);
        assert(n <= SIZE);
    }

    void pop()
    {
        data[0] = data[--n];
        down(0);
    }

    T top() const
    {
        return data[0];
    }

    int size() const
    {
        return n;
    }

    bool empty() const
    {
        return size() == 0;
    }

    void clear()
    {
        n = 0;
    }

private:
    T data[SIZE];
    int n;

    void up(int k)
    {
        while (k > 0)
        {
            int par = (k - 1) / 2;
            if (!(data[k] < data[par]))
                break;

            swap(data[k], data[par]);
            k = par;
        }
    }

    void down(int k)
    {
        for (;;)
        {
            int next = k;
            int a = 2 * k + 1, b = 2 * k + 2;
            if (a < n && data[a] < data[next])
                next = a;
            if (b < n && data[b] < data[next])
                next = b;

            if (next == k)
                break;

            swap(data[k], data[next]);
            k = next;
        }
    }
};

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
    Action(){}

    int x, y;
    Dir dir;
};

const int rect_dx[] = { 0, 1, 0, 1 };
const int rect_dy[] = { 0, 0, 1, 1 };

class Board
{
public:
    Board(int colors, const vector<string>& board, vector<int>* buffer)
        :
            n(board.size()),
            colors(colors),
            buffer(buffer),
            score(0),
            buffer_index(0),
            same_three_color_rects(0)
    {
        rep(y, n) rep(x, n)
            set(x, y, board[y][x] - '0');

        rep(y, n - 1) rep(x, n - 1)
            is_same_three[y][x] = false;
        rep(y, n - 1) rep(x, n - 1)
            update_same_three(x, y);

        PQ q;
        rep(y, n - 1) rep(x, n - 1)
            if (all_same(x, y))
                q.push(pss(y, x));
        adjust(q);
    }

    int get_score() const
    {
        return score;
    }

    int get_same_three_color_rects() const
    {
        return same_three_color_rects;
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
//     typedef priority_queue<uint, vector<uint>, greater<uint>> PQ;
    typedef PriorityQueue<uint, 16 * 16> PQ;
    void push_q(int tx, int ty, PQ& q)
    {
        rep(i, 4)
        {
            int x = tx - rect_dx[i];
            int y = ty - rect_dy[i];

            if (in_sq(x, y, n - 1))
            {
                update_same_three(x, y);
                if (all_same(x, y))
                    q.push(pss(y, x));
            }
        }
    }
    void adjust(PQ& q)
    {
        while (!q.empty())
        {
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
                    set(x, y, (*buffer)[buffer_index++]);
                }

                rep(i, 9)
                {
                    static const int ndx[] = { -1, 0, 1, -1, 0, 1, -1, 0, 1 };
                    static const int ndy[] = { -1, -1, -1, 0, 0, 0, 1, 1, 1 };
                    int x = tx + ndx[i];
                    int y = ty + ndy[i];

                    if (in_sq(x, y, n - 1))
                    {
                        update_same_three(x, y);
                        if (all_same(x, y))
                            q.push(pss(y, x));
                    }
                }
            }
        }
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
        int c1 = at(x1, y1);
        int c2 = at(x2, y2);
        set(x1, y1, c2);
        set(x2, y2, c1);

        PQ q;
        push_q(x1, y1, q);
        push_q(x2, y2, q);
        adjust(q);
    }

    bool operator==(const Board& other) const
    {
        if (buffer_index!= other.buffer_index)
            return false;

        rep(y, n) rep(x, n)
            if (at(x, y) != other.at(x, y))
                return false;

        return true;
    }

    string to_s() const
    {
        string res;
        rep(y, n)
        {
            rep(x, n)
                res += at(x, y) + '0';
            res += "\n";
        }
        return res;
    }

    ull hash() const
    {
        const ull base = ten(9) + 7;
        ull h = 0;
        rep(y, n) rep(x, n)
            h = h * base + at(x, y);
        return h;
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
        int c = at(tx, ty);
        rep(i, 4)
        {
            int x = tx + rect_dx[i];
            int y = ty + rect_dy[i];
            assert(in_sq(x, y, n));
            if (at(x, y) != c)
                return false;
        }
        return true;
    }

    void set(int x, int y, int color)
    {
        assert(in_sq(x, y, n));
        assert(0 <= color && color < colors);
        board[y][x] = color;
    }

    //
    int same_three_color_rects;
    bool is_same_three[16][16];
    void update_same_three(int tx, int ty)
    {
        assert(in_sq(tx, ty, n - 1));

        int num_colors[6];
        int c[4];
        rep(i, 4)
            c[i] = at(tx + rect_dx[i], ty + rect_dy[i]);
        num_colors[c[0]] = num_colors[c[1]] = 0;
        rep(i, 4)
            ++num_colors[c[i]];
        int max_num = max(num_colors[c[0]], num_colors[c[1]]);

        if (is_same_three[ty][tx])
        {
            --same_three_color_rects;
            is_same_three[ty][tx] = false;
        }
        if (max_num >= 3)
        {
            ++same_three_color_rects;
            is_same_three[ty][tx] = true;
        }
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
        map<int, int> nexts_log;

        vector<Node> stages[MAX_MOVES + 1];
        stages[0].push_back(Node(init_board, vector<Action>(), -1, -1));

        const int beam_width = 12 * 16 * 16 / (max(10, n) * max(10, n));
        rep(moves, MAX_MOVES)
        {
            auto& stage = stages[moves];
            if (stage.empty())
                continue;

//             vector<int> scores;
//             for (Node& node : stage)
//                 scores.push_back(node.board.get_score());
//             sort(all(scores));
//             fprintf(stderr, "%5d: %d\n", moves, stage.size());
//             cerr << scores << endl;

            rep(node_i, stage.size())
            {
                const Node& node = stage[node_i];

                int nexts = 0;

                for (int max_cost = 2; nexts == 0 && max_cost <= 3; ++max_cost)
                {
                    rep(ty, n - 1) rep(tx, n - 1)
                    {
                        int num_colors[6] = {};
                        rep(i, 4)
                            ++num_colors[node.board.at(tx + rect_dx[i], ty + rect_dy[i])];
                        static vector<int> use_colors;
                        use_colors.clear();
                        rep(color, colors)
                            if (num_colors[color] >= (4 - max_cost))
                                use_colors.push_back(color);

                        for (int color : use_colors)
                        {
                            Board board = node.board;
                            static vector<Action> actions;
                            actions.clear();
                            if (solve_actions(tx, ty, color, max_cost, board, actions))
                            {
                                assert(actions.size() > 0);
                                assert(actions.size() <= max_cost);
                                const int next_moves = moves + actions.size();
                                if (next_moves <= MAX_MOVES)
                                {
                                    bool diff_state = true;
                                    for (Node& no : stages[next_moves])
                                    {
                                        if (board == no.board)
                                        {
                                            diff_state = false;
                                            break;
                                        }
                                    }
                                    if (diff_state)
                                    {
                                        Node next_node(board, actions, moves, node_i);
                                        if (stages[next_moves].size() == beam_width)
                                        {
                                            rep(i, stages[next_moves].size())
                                            {
                                                if (next_node < stages[next_moves][i])
                                                {
                                                    stages[next_moves][i] = next_node;
                                                    break;
                                                }
                                            }
                                        }
                                        else
                                            stages[next_moves].push_back(next_node);

                                        ++nexts;
                                    }
                                }
                            }
                        }
                    }
                }

                ++nexts_log[nexts];
            }
        }
//         for (pint it : nexts_log)
//             fprintf(stderr, "%3d: %d\n", it.first, it.second);
//         dump((n - 1) * (n - 1));

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

        map<int, int> act_num;
        vector<Action> actions;
        for (int moves = best_moves, index = best_index; moves > 0; )
        {
            Node& node = stages[moves][index];
            Action* acts = node.actions;
            for (int i = node.actions_size - 1; i >= 0; --i)
                actions.push_back(acts[i]);

            moves = node.prev_moves;
            index = node.prev_index;

            ++act_num[node.actions_size];
        }
        for (auto it : act_num)
            fprintf(stderr, "%d: %d\n", it.first, it.second);
        reverse(all(actions));
        while (actions.size() < MAX_MOVES)
            actions.push_back(Action(0, 0, RIGHT));
        return actions;
    }

private:
    bool solve_actions(int tx, int ty, int color, int max_cost, Board& board, vector<Action>& res_actions)
    {
        assert(0 <= color && color < colors);
        assert(in_sq(tx, ty, n));

        res_actions.clear();

        bool fixed[16][16];
        for (int y = max(0, ty - max_cost); y <= min(n - 1, ty + max_cost); ++y)
            for (int x = max(0, tx - max_cost); x <= min(n - 1, tx + max_cost); ++x)
                fixed[y][x] = false;

        int diffs = 4;
        rep(i, 4)
        {
            int sx = tx + rect_dx[i];
            int sy = ty + rect_dy[i];
            if (board.at(sx, sy) == color)
            {
                fixed[sy][sx] = true;
                --diffs;
            }
        }

        const int ori_score = board.get_score();
        rep(i, 4)
        {
            const int sx = tx + rect_dx[i];
            const int sy = ty + rect_dy[i];

            if (fixed[sy][sx])
                continue;

            static vector<Action> acts;
            acts.clear();
            if (!solve_min_actions(board, sx, sy, color, fixed, max_cost, acts))
                return false;

            for (auto& a : acts)
            {
                board.move(a);
                res_actions.push_back(a);
                if (board.get_score() > ori_score)
                    return res_actions.size() <= max_cost;
            }
            if (board.at(sx, sy) != color)
                return false;

            fixed[sy][sx] = true;
            --diffs;

            if (res_actions.size() + diffs > max_cost)
                return false;
        }
        return true;
    }
    bool solve_min_actions(const Board& board, int sx, int sy, int color, const bool fixed[16][16], int max_cost, vector<Action>& res_actions)
    {
        assert(in_sq(sx, sy, n));

        if (board.at(sx, sy) == color)
            return true;

        const int inf = ten(7);
        int cost[16][16];
        Dir used_dir[16][16];
        for (int y = max(0, sy - max_cost); y <= min(n - 1, sy + max_cost); ++y)
            for (int x = max(0, sx - max_cost); x <= min(n - 1, sx + max_cost); ++x)
                cost[y][x] = inf;

        Queue<uint, 16 * 16> q;
        cost[sy][sx] = 0;
        q.push(pss(sx, sy));
        while (!q.empty())
        {
            const int cx = pss_first(q.front());
            const int cy = pss_second(q.front());
            q.pop();

            const int ncost = cost[cy][cx] + 1;
            if (ncost > max_cost)
                continue;

            rep(dir, 4)
            {
                int nx = cx + dir_dx[dir];
                int ny = cy + dir_dy[dir];
                if (in_sq(nx, ny, n) && !fixed[ny][nx] && ncost < cost[ny][nx])
                {
                    cost[ny][nx] = ncost;
                    used_dir[ny][nx] = Dir(dir);

                    if (board.at(nx, ny) == color)
                    {
                        for (int x = nx, y = ny; cost[y][x] > 0; )
                        {
                            assert(cost[y][x] < inf);
                            Dir dir = rev_dir(used_dir[y][x]);
                            res_actions.push_back(Action(x, y, dir));

                            x += dir_dx[dir];
                            y += dir_dy[dir];
                        }
                        return true;
                    }

                    q.push(pss(nx, ny));
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
            :
                board(board),
                actions_size(actions.size()),
                prev_moves(prev_moves),
                prev_index(prev_index)
        {
            assert(actions_size <= 4);
            rep(i, actions_size)
                this->actions[i] = actions[i];

            score = eval_board();
        }

        bool operator<(const Node& other) const
        {
            return score > other.score;
        }

        Board board;
        Action actions[4];
        int actions_size;
        int prev_moves;
        int prev_index;

    private:
        int eval_board()
        {
            return board.get_score() * 4 + board.get_same_three_color_rects();
        }
        int score;
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
