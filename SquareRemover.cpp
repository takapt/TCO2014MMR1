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
#include <unordered_set>


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

uchar encode_pos(int x, int y)
{
    assert(0 <= x && x < 16);
    assert(0 <= y && y < 16);
    return x | (y << 4);
}
uchar decode_pos(uchar pos, int& x, int& y)
{
    x = pos & 0xf;
    y = (pos >> 4) & 0xf;
}


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
template <typename T, int SIZE, typename CMP = less<T> >
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

    bool cmp(const T& a, const T& b) const
    {
        return CMP()(a, b);
    }

    void up(int k)
    {
        while (k > 0)
        {
            int par = (k - 1) / 2;
            if (!cmp(data[k], data[par]))
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
            if (a < n && cmp(data[a], data[next]))
                next = a;
            if (b < n && cmp(data[b], data[next]))
                next = b;

            if (next == k)
                break;

            swap(data[k], data[next]);
            k = next;
        }
    }
};

#ifdef _MSC_VER
#include <Windows.h>
#else
#include <sys/time.h>
#endif
class Timer
{
    typedef double time_type;
    typedef unsigned int skip_type;

private:
    time_type start_time;
    time_type elapsed;

#ifdef _MSC_VER
    time_type get_ms() { return (time_type)GetTickCount64() / 1000; }
#else
    time_type get_ms() { struct timeval t; gettimeofday(&t, NULL); return (time_type)t.tv_sec * 1000 + (time_type)t.tv_usec / 1000; }
#endif

public:
    Timer() {}

    void start() { start_time = get_ms(); }
    time_type get_elapsed() { return elapsed = get_ms() - start_time; }
};

class TimeCounter
{
public:
    TimeCounter(int n)
        : n(n), sum(0)
    {
    }

    void add(double t)
    {
        if (q.size() == n)
        {
            sum -= q.front();
            q.pop_front();
        }
        sum += t;
        q.push_back(t);
    }

    double average() const
    {
        assert(!q.empty());
        return sum / q.size();
    }

private:
    int n;
    deque<double> q;
    double sum;
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

const int color_bits = 4;
const ull color_mask = (1 << color_bits) - 1;
const ull two_color_mask = (1 << (2 * color_bits)) - 1;
const ull four_color_mask = (1 << (4 * color_bits)) - 1;


bool same_three_color_table[1 << (4 * color_bits)];
int pack_four_colors(int a, int b, int c, int d)
{
    return a | (b << color_bits) | (c << (2 * color_bits)) | (d << (3 * color_bits));
}
void init_same_three_color_table()
{
    rep(a, 6) rep(b, 6) rep(c, 6) rep(d, 6)
    {
        int num[6] = {};
        ++num[a];
        ++num[b];
        ++num[c];
        ++num[d];
        int max_num = *max_element(num, num + 6);
        same_three_color_table[pack_four_colors(a, b, c, d)] = max_num >= 3;
    }
}
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
        rep(y, 16)
            this->board[y] = 0;

        rep(y, n) rep(x, n)
            set(x, y, board[y][x] - '0');

        rep(y, n - 1) rep(x, n - 1)
            update_same_three(x, y);

        PQ q;
        rep(y, n - 1) rep(x, n - 1)
            if (all_same(x, y))
                q.push(pss(y, x));
        adjust(q);
    }
    Board(){}


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
        return (board[y] >> (color_bits * x)) & color_mask;
    }

private:
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

                for (int dy = -1; dy <= 1; ++dy)
                {
                    for (int dx = -1; dx <= 1; ++dx)
                    {
                        int x = tx + dx;
                        int y = ty + dy;

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

        rep(y, n)
            if (board[y] != other.board[y])
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
        ull h = buffer_index;
        rep(y, n)
            h = h * base + board[y];
        return h;
    }

private:
    ull four_color(int x, int y) const
    {
        if (y == -1)
            return 1919817;
        else if (y == n)
            return 114517;

        assert(0 <= y && y < n);

        if (x == -1)
            return ((board[y] << color_bits) & four_color_mask) | 7;
//         else if (x == n - 3)
//             return ((board[y] >> (color_bits * (n - 3))) & four_color_mask) | (9 << (3 * color_bits));
        else
            return (board[y] >> (color_bits * x)) & four_color_mask;
    }
public:
    ull sub_hash(int tx, int ty) const
    {
        assert(in_sq(tx, ty, n - 1));

        const ull base = ten(9) + 7;
        ull h = 0;
        for (int y = ty - 1; y <= ty + 2; ++y)
            h = h * base + four_color(tx - 1, y);
        return h;
    }

private:
    int n;
    int colors;
    vector<int>* buffer;
    int buffer_index;

    ull board[16];
    int score;

    bool all_same(int tx, int ty) const
    {
        assert(in_sq(tx, ty, n - 1));
        int a = two_color(tx, ty);
        int b = two_color(tx, ty + 1);
        if (a != b)
            return false;
        int c0 = a & color_mask;
        int c1 = (a >> color_bits) & color_mask;
        return c0 == c1;
    }

    void set(int x, int y, int color)
    {
        assert(in_sq(x, y, n));
        assert(0 <= color && color < colors);
        board[y] = (board[y] & ~(color_mask << (color_bits * x))) | (ull(color) << (color_bits * x));
        assert(at(x, y) == color);
    }

    int two_color(int x, int y) const
    {
        assert(0 <= x && x < n - 1);
        assert(0 <= y && y < n);
        return (board[y] >> (color_bits * x)) & two_color_mask;
    }

    //
    int same_three_color_rects;
    bitset<256> is_same_three; 
    void update_same_three(int tx, int ty)
    {
        assert(in_sq(tx, ty, n - 1));

        const uchar tpos = encode_pos(tx, ty);
        if (is_same_three[tpos])
        {
            --same_three_color_rects;
            is_same_three.flip(tpos);
        }

        int packed = two_color(tx, ty) | (two_color(tx, ty + 1) << (2 * color_bits));
        if (same_three_color_table[packed])
        {
            ++same_three_color_rects;
            is_same_three.flip(tpos);
        }
    }
};


const int MAX_MOVES = ten(4);
const int MAX_COST = 3;
const int NUM_Q = 4;

class Solver
{
public:
    Solver(int colors, const Board& init_board)
        : init_board(init_board), n(init_board.size()), colors(colors)
    {
    }

    vector<Action> solve()
    {
// #define USE_TIMER

#ifdef LOCAL
#ifdef USE_TIMER
        const double GLOBAL_TLE = 9 * 1000;
#else
        const double GLOBAL_TLE = 1e9 * 9 * 1000;
#endif
#else
        const double GLOBAL_TLE = 29.9 * 1000;
#endif

        Timer g_timer;
        g_timer.start();

        vector<Node> stages[MAX_MOVES + 1];

        priority_queue<Node> stage_qs[NUM_Q];
        unordered_set<ull> pushed_board_hash[NUM_Q];
        stage_qs[0].push(Node(init_board, vector<Action>(), -1, -1));


        TimeCounter time_counter(100);
        unordered_set<ull> ignore(4 * ten(5));
        int beam_width = 21 * 15 * 15 / (max(10, n) * max(10, n));
        rep(moves, MAX_MOVES)
        {
            pushed_board_hash[moves % NUM_Q].clear();

            auto& stage = stages[moves];
            auto& stage_q = stage_qs[moves % NUM_Q];
            assert(stage.empty());

            while (stage_q.size() > beam_width)
                stage_q.pop();
            while (!stage_q.empty())
            {
                stage.push_back(stage_q.top());
                stage_q.pop();
            }

#if 0
            vector<int> scores;
            for (Node& node : stage)
                scores.push_back(node.board.get_score());
            sort(all(scores));
            fprintf(stderr, "%5d: %d\n", moves, stage.size());
            cerr << scores << endl;
#endif

            const double start_t = g_timer.get_elapsed();
            for (int node_i = sz(stage) - 1; node_i >= 0; --node_i)
            {
                if (g_timer.get_elapsed() > GLOBAL_TLE)
                {
                    cerr << "bad time adjusting" << endl;
                    goto End;
                }

                const Node& node = stage[node_i];

                int nexts = 0;
                for (int max_cost = 2; nexts == 0 && max_cost <= MAX_COST; ++max_cost)
                {
                    rep(ty, n - 1) rep(tx, n - 1)
                    {
                        const ull base = ten(9) + 9;
                        const ull sub_hash = node.board.sub_hash(tx, ty) * base + max_cost;
                        if (ignore.count(sub_hash))
                            continue;

                        int num_colors[6];
                        fill_n(num_colors, colors, 0);
                        rep(i, 4)
                            ++num_colors[node.board.at(tx + rect_dx[i], ty + rect_dy[i])];
                        static vector<int> use_colors;
                        use_colors.clear();
                        rep(color, colors)
                            if (num_colors[color] >= 2)
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
                                auto& next_q = stage_qs[next_moves % NUM_Q];
                                auto& next_hash = pushed_board_hash[next_moves % NUM_Q];
                                Node next_node(board, actions, moves, node_i);
                                if (next_moves <= MAX_MOVES && (next_q.size() < beam_width || next_node < next_q.top()))
                                {
                                    const ull board_hash = board.hash();
                                    if (!next_hash.count(board_hash))
                                    {
                                        next_hash.insert(board_hash);
                                        next_q.push(next_node);

                                        ++nexts;
                                    }
                                }
                            }
                            else
                            {
                                if (ignore.size() % ten(5) == 0)
                                    ignore.clear();
                                ignore.insert(sub_hash);
                            }
                        }
                    }
                }
            }
            if (moves + 1 == MAX_MOVES)
                break;

#ifdef USE_TIMER
            double cur_t = g_timer.get_elapsed();
            double taken_t = cur_t - start_t;
            time_counter.add(taken_t / beam_width);
            double ave_one_beam_t = time_counter.average();
            double remain_t = GLOBAL_TLE * 0.99 - cur_t;
            double one_move_t = remain_t / (MAX_MOVES - (moves + 1));
            int good_beam_width = max<int>(1, one_move_t / ave_one_beam_t);
            static int last_changed = 10;
            if (moves - last_changed >= 3 && abs(beam_width - good_beam_width) >= 2)
            {
                last_changed = moves;
                if (good_beam_width > beam_width)
                    ++beam_width;
                else
                    --beam_width;
            }
#endif
        }
End:
        ;

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
            Action* acts = node.actions;
            for (int i = node.actions_size - 1; i >= 0; --i)
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
    bool solve_actions(int tx, int ty, int color, int max_cost, Board& board, vector<Action>& res_actions)
    {
        assert(0 <= color && color < colors);
        assert(in_sq(tx, ty, n));

        res_actions.clear();

        bitset<256> fixed;

        int diffs = 4;
        rep(i, 4)
        {
            int sx = tx + rect_dx[i];
            int sy = ty + rect_dy[i];
            if (board.at(sx, sy) == color)
            {
                fixed.set(encode_pos(sx, sy));
                --diffs;
            }
        }

        const int ori_score = board.get_score();
        rep(i, 4)
        {
            const int sx = tx + rect_dx[i];
            const int sy = ty + rect_dy[i];
            const uchar spos = encode_pos(sx, sy);

            if (fixed[spos])
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

            fixed.set(spos);
            --diffs;

            if (res_actions.size() + diffs > max_cost)
                return false;
        }
        return true;
    }
    bool solve_min_actions(const Board& board, int sx, int sy, int color, const bitset<256>& fixed, int max_cost, vector<Action>& res_actions)
    {
        assert(in_sq(sx, sy, n));

        if (board.at(sx, sy) == color)
            return true;

        bitset<256> visit;
        Dir used_dir[256];

        Queue<uint, 16 * 16> q;
        uchar start_pos = encode_pos(sx, sy);
        visit.set(start_pos);
        q.push(pss(start_pos, 0));
        while (!q.empty())
        {
            int cx, cy;
            decode_pos(pss_first(q.front()), cx, cy);
            const int cost = pss_second(q.front());
            q.pop();

            const int ncost = cost + 1;
            if (ncost > max_cost)
                continue;

            rep(dir, 4)
            {
                int nx = cx + dir_dx[dir];
                int ny = cy + dir_dy[dir];
                uchar npos = encode_pos(nx, ny);
                if (in_sq(nx, ny, n) && !fixed[npos] && !visit[npos])
                {
                    visit.set(npos);
                    used_dir[npos] = Dir(dir);

                    if (board.at(nx, ny) == color)
                    {
                        for (int x = nx, y = ny; x != sx || y != sy; )
                        {
                            assert(visit[encode_pos(x, y)]);
                            Dir dir = rev_dir(used_dir[encode_pos(x, y)]);
                            res_actions.push_back(Action(x, y, dir));

                            x += dir_dx[dir];
                            y += dir_dy[dir];
                        }
                        return true;
                    }

                    q.push(pss(npos, ncost));
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
            assert(actions_size <= MAX_COST);
            rep(i, actions_size)
                this->actions[i] = actions[i];

            score = eval_board();
        }

        bool operator<(const Node& other) const
        {
            return score > other.score;
        }

        bool operator>(const Node& other) const
        {
            return score < other.score;
        }

        Board board;
        Action actions[MAX_COST];
        int actions_size;
        int prev_moves;
        int prev_index;

        int get_score() const
        {
            return score;
        }

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
        init_same_three_color_table();

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
