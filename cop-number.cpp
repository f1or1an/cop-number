#pragma clang diagnostic push
#pragma ide diagnostic ignored "misc-no-recursion"

#include <bits/stdc++.h>
using namespace std;

#define V(T) using v##T=vector<T>;
#define T(T, t...) using T=t; V(T) V(v##T) V(vv##T)
T(z, int)
T(u64, uint64_t)
T(u32, uint32_t)
T(u16, uint16_t)
T(u8, uint8_t)
T(ld, long double)


////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////// faster multiset (at least for very small size, which is all we need)
////////////////////////////////////////////////////////////////////

#define multiset mymultiset

template<typename T>
class multiset {
    vector<T> v;
public:
    void sort() { ranges::sort(v); }

    multiset() {}
    multiset(auto b, auto e): v(b, e) { sort(); }

    auto begin() { return v.begin(); }
    auto end() { return v.end(); }
    auto begin() const { return v.begin(); }
    auto end() const { return v.end(); }
    auto rbegin() { return v.rbegin(); }
    auto rend() { return v.rend(); }
    auto rbegin() const { return v.rbegin(); }
    auto rend() const { return v.rend(); }
    bool operator==(const multiset& o) const { return v==o.v; }
    auto size() const { return v.size(); }
    auto empty() const { return v.empty(); }
    bool contains(z e) const {return ranges::count(v, e);}
    auto find(z e) {return ranges::find(v, e);}
    void insert(auto a, auto b) { v.insert(v.end(), a, b); sort(); }
    auto insert(const z& e) {v.insert(ranges::lower_bound(v, e), e);}
    auto erase(vz::iterator e) { return v.erase(e);}
};


////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////// multiset_enumerator
////////////////////////////////////////////////////////////////////

class multiset_enumerator {
    vvu64 cnt; // cnt[k][n] = #multisets on 0..n-1 of size k

public:
    multiset_enumerator(z max_n, z max_k): cnt(max_k+1, vu64(max_n+1)) {
        cnt[0].assign(max_n+1, 1);
        for (z k = 1; k <= max_k; ++k) {
            for (z n = 1; n <= max_n; ++n) {
                __int128 tmp = cnt[k - 1][n] + cnt[k][n - 1];
                assert(tmp < numeric_limits<u64>::max());
                cnt[k][n] = tmp;
            }
        }
    }

    u64 count(z n, z k) const {
        return cnt[k][n];
    }

    // maps m to i if m is the i-th lexicographically smallest multiset on 0..n-1 of size |m|    //i starts with 0
    u64 multiset_to_id(const z n, const multiset<z>& m) const { // this should be fast as it is called very often. Time complexity is O(k)
        z min = 0;
        z k = m.size();
        u64 res = 0;
        for (z x: m) {
            //  #multisets on min..n-1 (of size k) with minimum < x
            // =#multisets on 0..n-1-min with minimum < x-min
            // =#multisets on 0..n-1-min  -  #multisets on 0..n-1-min with minimum >= x-min
            // =#multisets on 0..n-1-min  -  #multisets on 0..n-1-min-(x-min)
            // =#multisets on 0..n-1-min  -  #multisets on 0..n-1-x
            u64 smaller = cnt[k][n - min] - cnt[k][n - x];
            res += smaller;
            min = x;
            --k;
        }
        return res;
    }

    multiset<z> id_to_multiset(z n, z k, u64 id) const { // we don't need this to be fast; only called twice per R-state. Time complexity is O(k (n+k))
        if (k==0) return {};
        assert(id < cnt[k][n]);
        if (id < cnt[k-1][n]) {
            //0 in multiset
            multiset<z> res = id_to_multiset(n, k-1, id);
            res.insert(0);
            return res;
        }
        //0 not in multiset
        multiset<z> res;
        for (z x : id_to_multiset(n-1, k, id-cnt[k-1][n])) res.insert(x + 1);
        return res;
    }

    void foreach_multiset (z n, z k, const function<void(multiset<z>)>& fun) const { // returning all these multisets instead might require too much memory
        assert(n>0);
        if (k==0) fun({});
        else foreach_multiset(n, k-1, [&](auto m){
            for (z x = m.size() ? *m.rbegin() : 0; x < n; ++x) {
                m.insert(x);
                fun(m);
                m.erase(m.find(x));
            }
        });
    }

    vector<multiset<z>> all_multisets(z n, z k) const {
        vector<multiset<z>> res;
        foreach_multiset(n, k, [&](auto m){res.push_back(m);});
        return res;
    }
};


////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////// Actual C&R implementation
////////////////////////////////////////////////////////////////////

struct game;
struct state;


class state_enumerator {
    const game &gm;
    vu64 cntsum; // cntsum[k] = #states with #unmovedCops<k

public:
    const multiset_enumerator mset_enumerator;

    state_enumerator(const game &gm);

    u64 count_states(z max_unmoved_cops) const;
    u64 count_states() const;

    u64 state_to_id(const state &s) const;
    state id_to_state(u64 id) const;
};



/**
 * G: a simple (i.e. undirected, no loops, no duplicate edges) graph, given as adjacency lists
 * k: #cops
 *
 * Mechanics:
 * - each cop chooses a vertex on which it starts
 * - R chooses a vertex on which it starts
 * - forever:
 *   - each cop may move along an edge of G (or stand still)
 *   - if now a cop is on the same vertex as R, the cops win the game
 *   - R moves along an edge of G. If r_flexible is true: R may alternatively stand still
 *   - if attacking is true: if R moved to a vertex with cops on it, R may eliminate one of them
 *
 * This implementation uses dummy vertices:
 * - INITIAL_VERTEX, representing that the respective entity did not choose its starting position yet
 * - if attacking is true: GRAVE_VERTEX, representing that the respective cop has been eliminated
 *
 * n := number of vertices including dummy vertices <= |G|+2
 */
struct game {
    const vvz g;
    const z k; // #cops
    const bool attacking;
    const bool r_flexible;
    //const bool cops_flexible;

    // derived parameters
    const z normal_vertices = g.size();
    const z GRAVE_VERTEX = normal_vertices; // in attacking version: eliminated cops remain on this dummy vertex
    const z noninitial_vertices = g.size() + attacking;
    const z INITIAL_VERTEX = normal_vertices + attacking; // cops and R start on this dummy vertex (and must move from there)
    const z all_vertices = normal_vertices  + attacking + 1;

    const state_enumerator state_enumeratr;

    game(vvz g, z k, bool attacking = 0, bool r_flexible = 1);
    u64 count_states() const;
    u64 count_r_states() const;
    state initial_state() const;
    vu32 final_state_ids() const;
    void foreach_legal_state(function<void(const state&)> fun) const;
};



struct state {
    const game& gm;
    const multiset<z> unmoved_cops;
    const multiset<z> moved_cops;
    const z r;

    bool is_legal() const;
    bool is_final() const;
    bool is_r_turn() const; // We call those states R-states
    bool is_cop_turn() const;

    state move_cop(z old_pos, z new_pos, bool undo, bool attack=0) const;
    state move_r(z new_pos) const;

    // rule: a (yet) unmoved cop may not move to a position that is smaller than a position of a moved cop
    //       this does not restrict the cops' possible moves: they can order their moves (between two R-states) s.t. the target positions are increasing
    vector<state> next_states() const;
    vector<state> prev_states() const;

    bool operator==(const state& s) const;
};



state_enumerator::state_enumerator(const game &gm): mset_enumerator(gm.all_vertices, gm.k), gm(gm) {
    z n = gm.all_vertices, k = gm.k;
    cntsum.resize(k + 2);
    __int128 sum = 0;
    for (z unmoved = 0; unmoved <= k; ++unmoved) {
        cntsum[unmoved] = sum;

        sum += n * mset_enumerator.count(n, unmoved) * mset_enumerator.count(n, k - unmoved);
        assert(sum < numeric_limits<u64>::max());
    }
    cntsum[k + 1] = sum;
}

u64 state_enumerator::count_states(z max_unmoved_cops) const {
    return cntsum[max_unmoved_cops+1];
}
u64 state_enumerator::count_states() const {
    return cntsum.back();
}

u64 state_enumerator::state_to_id(const state &s) const {
    // in method analyze(game) in queue: R-states, i.e. states where it's R's turn, i.e. states where all cops moved, i.e. states with no unmoved cops
    // those states shall map to smallest numbers
    z unmoved = s.unmoved_cops.size(), moved = s.moved_cops.size();
    z n = s.gm.all_vertices;
    //tuple (#unmoved, unmoved, moved, r)
    __int128 id = cntsum[unmoved] + (mset_enumerator.multiset_to_id(n, s.unmoved_cops) * mset_enumerator.count(n, moved) + mset_enumerator.multiset_to_id(n, s.moved_cops)) * n + s.r;
    assert(id < cntsum[unmoved+1]);
    return id;
}

state state_enumerator::id_to_state(u64 id) const {
    z k = gm.k, n = gm.all_vertices;
    assert(id<cntsum[k+1]);
    z unmoved = 0;
    while (id >= cntsum[unmoved + 1]) ++unmoved;
    id -= cntsum[unmoved];
    z moved = k - unmoved;
    u64 unmoved_id = id / (mset_enumerator.count(n, moved) * n);
    id -= unmoved_id * mset_enumerator.count(n, moved) * n;
    u64 moved_id = id / n;
    z r = id - moved_id * n;
    return {gm, mset_enumerator.id_to_multiset(n, unmoved, unmoved_id), mset_enumerator.id_to_multiset(n, moved, moved_id), r};
}



game::game(vvz g, z k, bool attacking, bool r_flexible) : g(g), k(k), attacking(attacking), r_flexible(r_flexible), state_enumeratr(*this) {
}

// a (pretty tight) upper bound on the number of states that are reachable from the initial position
u64 game::count_states() const {
    return state_enumeratr.count_states();
}
u64 game::count_r_states() const { // states in which it's R's turn
    return state_enumeratr.count_states(0);
}
state game::initial_state() const {
    vz cops(k, INITIAL_VERTEX);
    return state{*this, multiset<z>(cops.begin(), cops.end()), {}, INITIAL_VERTEX};
}
vu32 game::final_state_ids() const {
    // only list R-states
    assert(count_r_states() < numeric_limits<u32>::max()); // if this fails, consider storing R-states in u64
    vu32 res;
    state_enumeratr.mset_enumerator.foreach_multiset(noninitial_vertices, k, [&](auto cops){ // for cops, all positions except INITIAL_VERTEX possible
        for (z r: set(cops.begin(), cops.end())) if (r < normal_vertices) { // for R, all positions except INITIAL_VERTEX and GRAVE_VERTEX possible
            res.push_back(state_enumeratr.state_to_id({*this, {}, cops, r}));
        }
    });
    return res;
}
void game::foreach_legal_state(function<void(const state&)> fun) const {
    for (u64 id = 0; id < count_states(); ++id) {
        state s = state_enumeratr.id_to_state(id);
        if (s.is_legal()) fun(s);
    }
}



bool state::is_legal() const {
    multiset<z> all_cops = unmoved_cops; all_cops.insert(moved_cops.begin(), moved_cops.end());
    assert(all_cops.size()==gm.k && (all_cops.empty() or (*all_cops.begin()>=0 && *all_cops.rbegin() < gm.all_vertices))); // this should never fail
    if (r < gm.normal_vertices) {
        return !all_cops.contains(gm.INITIAL_VERTEX);
    }
    if (r == gm.INITIAL_VERTEX) {
        return ranges::all_of(unmoved_cops, [&](z c) { return c == gm.INITIAL_VERTEX; })
               && ranges::all_of(moved_cops, [&](z c) { return c < gm.normal_vertices; });
    }
    if (r == gm.GRAVE_VERTEX) {
        return 0;
    }
    assert(0); // this should not happen
}
bool state::is_final() const {
    return is_r_turn() && moved_cops.contains(r);
}
bool state::is_r_turn() const {
    return unmoved_cops.empty();
}
bool state::is_cop_turn() const {
    return !is_r_turn();
}

state state::move_cop(z old_pos, z new_pos, bool undo, bool attack) const {
    auto u = unmoved_cops;
    auto m = moved_cops;
    if (undo) swap(u,m);
    assert(u.contains(old_pos));
    u.erase(u.find(old_pos));
    (attack?u:m).insert(new_pos);
    if (undo) swap(u, m);
    return {gm, u, m, r};
}
state state::move_r(z new_pos) const {
    assert(unmoved_cops.empty() or moved_cops.empty());
    // If R moves, all moved cops "become" unmoved again.
    // If R's move is undone, all unmoved cops "become" moved again.
    return {gm, moved_cops, unmoved_cops, new_pos};
}

// rule: a (yet) unmoved cop may not move to a position that is smaller than a position of a moved cop
//       this does not restrict the cops' possible moves: they can order their moves (between two R-states) s.t. the target positions are increasing
vector<state> state::next_states() const {
    vector<state> next_states;

    if (is_r_turn()) { // R's turn
        if (is_final()) return {};

        vz next_positions;
        if (r < gm.normal_vertices) {
            next_positions = gm.g[r];
            if (gm.r_flexible) next_positions.push_back(r);
        }
        else {
            assert(r == gm.INITIAL_VERTEX);
            for (z i = 0; i < gm.normal_vertices; ++i) next_positions.push_back(i);
        }

        for (z v: next_positions) {
            state s = move_r(v);
            next_states.push_back(s);
            if (gm.attacking && r!=gm.INITIAL_VERTEX && s.unmoved_cops.contains(v)) next_states.push_back(s.move_cop(v, gm.GRAVE_VERTEX, 0, 1));
        }
    }
    else {
        z max_moved_vertex = moved_cops.empty() ? 0 : *moved_cops.rbegin();

        for (auto c: set(unmoved_cops.begin(), unmoved_cops.end())) {
            vz next_positions;
            if (c < gm.normal_vertices) {
                next_positions = gm.g[c];
                next_positions.push_back(c);
            }
            else if (c == gm.INITIAL_VERTEX) {
                for (z i = 0; i < gm.normal_vertices; ++i) next_positions.push_back(i);
            }
            else {
                assert(c == gm.GRAVE_VERTEX);
                next_positions.push_back(gm.GRAVE_VERTEX);
            }
            for (z v: next_positions) {
                if (v >= max_moved_vertex) { // see rule above
                    next_states.push_back(move_cop(c, v, 0));
                }
            }
        }
    }
    return next_states;
}

vector<state> state::prev_states() const {
    vector<state> prev_states;
    if (moved_cops.empty()) { // previous turn was R's turn
        if (r == gm.INITIAL_VERTEX) return {};

        // R is on normal vtx
        // possibilities:
        // - R was on normal vertex (without a cop!) before. R possibly eliminated a cop
        // - R was on INITIAL_VERTEX before, and no cop *is* eliminated (and no cop is on INITIAL_VERTEX before)
        vz prev_positions = gm.g[r];
        if (gm.r_flexible) prev_positions.push_back(r);

        if (!gm.attacking or !unmoved_cops.contains(gm.GRAVE_VERTEX)) prev_positions.push_back(gm.INITIAL_VERTEX);

        for (z v:prev_positions) {
            if (unmoved_cops.contains(v)) continue; // prev state must have been non-final

            state s = move_r(v);
            prev_states.push_back(s);

            // possibly revive a cop
            if (gm.attacking && unmoved_cops.contains(gm.GRAVE_VERTEX)) {
                if (v != r) { // if R attacked a cop, the cop must have been on a different vertex than R (otherwise, prev state would be final)
                    prev_states.push_back(s.move_cop(gm.GRAVE_VERTEX, r, 1, 1));
                }
            }
        }
    }
    else { // previous turn was a cop's turn
        z c = *moved_cops.rbegin(); // ...in particular, c's turn (see rule above)
        vz prev_positions;
        if (r == gm.INITIAL_VERTEX) {
            prev_positions.push_back(gm.INITIAL_VERTEX);
        }
        else {
            if (c < gm.normal_vertices) {
                prev_positions = gm.g[c];
                prev_positions.push_back(c);
            }
            else if (c == gm.INITIAL_VERTEX) {
                assert(false); // bad state!
            }
            else {
                assert(c == gm.GRAVE_VERTEX);
                prev_positions.push_back(gm.GRAVE_VERTEX);
            }
        }
        for (z v:prev_positions) {
            prev_states.push_back(move_cop(c, v, 1));
        }
    }
    return prev_states;
}

bool state::operator==(const state& s) const { // the state's games must be the same of course. Since that would be expensive to check, we do not do that
    return unmoved_cops == s.unmoved_cops && moved_cops == s.moved_cops && r == s.r;
}



class result {
    const game& gm;
    const vector<bool> copwin_array;
    const vu32 queue;
public:
    // a result is only valid as long as the corresponding game is not destructed! i.e. do not destruct the game as long as you want to use the result
    result(const game& gm, vector<bool>& copwin, vu32& queue): gm(gm), copwin_array(move(copwin)), queue(move(queue)) {}

    /*
     * Only call this with legal, non-final states with no moved or no unmoved cops.
     * If the party whose turn it is can win, applies a winning move and returns the following state.
     * If it's the cops' turn and they can win, a move that minimizes the capture time is applied.
     *
     * This method may require much memory if the graph is very dense. (The required memory is of the same order of magnitude as for analyze(game).)
     */
    optional<state> winning_move(state s) const {
        assert(s.is_legal());
        assert(!s.is_final());
        assert(s.moved_cops.size() * s.unmoved_cops.size() == 0);
        u64 id = gm.state_enumeratr.state_to_id(s);
        if (copwin_array[id] != s.is_cop_turn()) return {};
        if (s.is_r_turn()) {
            for (auto n:s.next_states()) {
                if (!copwin_array[gm.state_enumeratr.state_to_id(n)]) return n;
            }
            assert(0);
        }
        else {
            // reason for this "dumb" algorithm instead of storing parent state pointers in analyze(game):
            //   is more memory efficient (at least for graphs that are not too dense; otherwise, can need roughly to 64(n+1)^k bits)
            // to reduce memory consumption further:
            // - use u32 instead of u64 to store states. (possible because r is fixed and in each iteration, #unmoved cops is fixed as well)
            // - use vector<bool> instead to store states (relatively small for the same reason as above)
            // - maybe think of smart algo to compute next_r_states (without using state::next_states)
            vu64 next_r_states{id};
            for (z i = 0; i < gm.k; ++i) {
                vu64 next;
                for (auto s:next_r_states)
                    for (auto n:gm.state_enumeratr.id_to_state(s).next_states())
                        next.push_back(gm.state_enumeratr.state_to_id(n));
                ranges::sort(next);
                next.erase(unique(next.begin(), next.end()), next.end());
                swap(next_r_states, next);
            }
            for (u64 id : queue) { // find the move(s) with the smallest capture time
                if (binary_search(next_r_states.begin(), next_r_states.end(), id)) {
                    return gm.state_enumeratr.id_to_state(id);
                }
            }
            assert(0);
        }
    }

    bool is_copwin(state s) const {
        assert(s.is_legal());
        return copwin_array[gm.state_enumeratr.state_to_id(s)];
    }
    bool can_current_player_win(state s) const {
        return is_copwin(s) == s.is_cop_turn();
    }
    bool is_copwin() const {
        return is_copwin(gm.initial_state());
    }
};

/*
 * An adaptation of
 * J. Petr, J. Portier, and L. Versteegen, “A faster algorithm for Cops and Robbers,” Discrete Applied Mathematics, vol. 320, pp. 11–14, 2022, doi: https://doi.org/10.1016/j.dam.2022.05.019.
 *
 *
 * Time complexity:
 * Let n be |G|+1+attacking, i.e. all vertices.
 *
 * Claim: #states <= n (n+k)^k 2^k / k!
 * Proof:
 * Let n multichoose k be the number of multisets containing k integers from 1 to n.
 *    #states
 * <= sum_moved=0^k (n multichoose moved) (n multichoose k-moved) n
 *  = n sum_moved=0^k (n+moved-1 choose moved) (n+k-moved-1 choose k-moved)
 *  = n sum_moved=0^k (n+k choose moved) (n+k choose k-moved)
 * <= n (n+k)^k sum_moved=0^k 1/moved! 1/(k-moved)!
 *  = n (n+k)^k / k! sum_moved=0^k k! 1/moved! 1/(k-moved)!
 *  = n (n+k)^k / k! sum_moved=0^k (k choose moved)
 *  = n (n+k)^k / k! 2^k
 *  = n (n+k)^k 2^k / k!
 *
 * The bfs and dfs together explore each state at most once.
 * One exploration consists of:
 * - calling id_to_state in time O(k (n+k))
 * - calling prev_states(). Because of the rule mentioned above next_states(), every state has at most n+k previous states.
 *   The time complexity of prev_states() is in O((n+k) k).
 * - visiting every previous state, in particular, calling state_to_id in time O(k). These visits take time O((n+k) k) in total.
 * In total, one exploration runs in time O((n+k) k).
 *
 * For each R-state, next_states is called at most once, taking time O(n). This is negligible.
 *
 * The overall time complexity is #states * exploration_time, i.e. in O((n+k)^(k+2) k 2^k/k!)
 *
 *
 * If we do not upper bound degrees of vertices by n, we can probably save a factor of ||G||/|G|.
 */
result analyze(const game& gm) { // better keep the const! otherwise one might try to call analyze(game(...))...

    cout<<"required memory: "<<gm.count_states()/8/1e9<<" (copwin)  +  "<<gm.count_r_states()/1e9<<" (copwin_countdown)  +  "<<gm.count_r_states()*4/1e9<<" (queue)  GB"<<endl;

    vector<bool> copwin(gm.count_states());
    vector<u8> copwin_countdown(gm.count_r_states());

    assert(gm.count_r_states() < numeric_limits<u32>::max()); // if this fails, consider storing R-states in u64
    vu32 queue = gm.final_state_ids();
    for (u32 id: queue) copwin[id] = 1;

    u64 progress = 0;
    cout << "starting search" << endl;

    // "outside", we use a bfs that can only explore R-states → can store state ids as u32 instead of u64 in queue → save factor 1/2
    // to visit non-R-states, we use dfs "between" R-states. The dfs has maximum depth k → dfs stack remains small; dfs only needs O(max indegree of a state * k) = O(all_vertices * k) memory
    for (u64 i = 0; i < queue.size(); ++i) {
        auto u = gm.state_enumeratr.id_to_state(queue[i]);

        auto dfs = [&](auto dfs, state& u) -> void {
            for (auto& v: u.prev_states()) {
                u64 id = gm.state_enumeratr.state_to_id(v);
                if (copwin[id]) {
                    assert(v.is_cop_turn());
                    continue;
                }
                if (v.is_cop_turn()) {
                    copwin[id] = 1;
                    if ((++progress%1000000)==0) cout<<"(lower bound for) progress: "<<progress*1.0/gm.count_states()<<" (=1/"<<gm.count_states()*1.0/progress<<")"<<endl;
                    dfs(dfs, v);
                } else {
                    if (!copwin_countdown[id]) { // first visit → initialize
                        u64 next = v.next_states().size();
                        assert(next < numeric_limits<u8>::max()); // if this ever fails, simply use u16 or u32 instead of u8 for copwin_countdown
                        copwin_countdown[id] = next;
                    }
                    if (--copwin_countdown[id] == 0) {
                        copwin[id] = 1;
                        if ((++progress%1000000)==0) cout<<"(lower bound for) progress: "<<progress*1.0/gm.count_states()<<" (=1/"<<gm.count_states()*1.0/progress<<")"<<endl;
                        queue.push_back(id);
                    }
                }
            }
        };

        dfs(dfs, u);
    }

    return result(gm, copwin, queue);
}


////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////// Interaction & stuff for debugging
////////////////////////////////////////////////////////////////////

const string INITIAL_VERTEX_NAME = "_", GRAVE_NAME = "+";
void print_state(ostream& os, const state& s, function<string(z)> vertex_names = [](z ix){return to_string(ix);}) {
    auto ix_to_str=[&](z ix)->string {
        if (ix<s.gm.normal_vertices) return vertex_names(ix);
        if (ix==s.gm.INITIAL_VERTEX) return INITIAL_VERTEX_NAME;
        assert(s.gm.attacking && ix==s.gm.GRAVE_VERTEX);
        return GRAVE_NAME;
    };
    os<<"unmoved:";
    for (z u:s.unmoved_cops) os<<" "<<ix_to_str(u);
    os<<",  moved:";
    for (z u:s.moved_cops) os<<" "<<ix_to_str(u);
    os<<", r: "<<ix_to_str(s.r);
}
ostream& operator<<(ostream& os, const state& s) {
    print_state(os, s);
    return os;
}


/*
 * Plays a game that has been analyzed against a human.
 * Starts in the initial state.
 * (Console) commands:
 * - start with cop turn in c_1 ... c_k r   (cops and r may be "_" (see below))    // Ask whether a state is winning, and if so, for an optimal move
 * - start with R turn in c_1 ... c_k r   (r may be "_" (see below))               // Ask whether a state is winning, and if so, for an optimal move
 * - c_1 ... c_k    // move cops and ask for another optimal move
 * - r              // move R and ask for another optimal move
 * - quit           // end the interaction
 *
 * "_" represents INITIAL_VERTEX, "+" represents GRAVE_VERTEX. Entities on such vertices must also be part of the input.
 */
void interact(const game& gm, const result& res, function<string(z)> vertex_names = [](z ix){return to_string(ix);}) {
    map<string, z> name_to_index;
    name_to_index[INITIAL_VERTEX_NAME] = gm.INITIAL_VERTEX;
    if (gm.attacking) name_to_index[GRAVE_NAME] = gm.GRAVE_VERTEX;
    for (z i = 0; i < gm.normal_vertices; ++i) {
        string name = vertex_names(i);
        assert(!name_to_index.contains(name)); // no two vertices may have the same name
        assert(ranges::count(name, ' ') == 0); // vertex names may not contain " "
        name_to_index[name] = i;
    }

    auto cur = make_unique<state>(gm.initial_state());
    auto set_cur = [&](state s) { cur = make_unique<state>(s); };

    auto move = [&](auto choose) -> void {
        if (cur->is_final()) {
            cout << "Game over (I won)." << endl << endl;
            cout << "Resetting current state to initial state." << endl;
            set_cur(gm.initial_state());
            choose(choose);
            return;
        }

        auto s = res.winning_move(*cur);
        if (!s) {
            cout << "The strategy seems to be inconsistent (due to a bug). Please report this." << endl;
            assert(0);
        }
        cout << "I move. New state: ";
        print_state(cout, *s, vertex_names);
        cout<<endl;
        set_cur(*s);

        if (cur->is_final()) {
            cout << "Game over (I won)." << endl << endl;
            cout << "Resetting current state to initial state." << endl;
            set_cur(gm.initial_state());
            choose(choose);
        }
    };
    auto choose = [&](auto choose) -> void {
        bool winning = res.can_current_player_win(*cur);
        string choice = winning == cur->is_r_turn() ? "R" : "cops";
        cout << "I choose " << choice << "." << endl;
        if (winning) {
            move(choose);
        }
    };

    cout << "Starting interaction with the initial state as current state." << endl;
    choose(choose);

    while (1) {
        string command;
        getline(cin, command);

        auto match = [&](string prefix, z positions) -> optional<vz> {
            if (prefix.size() && positions) prefix+=" ";
            if (!command.starts_with(prefix)) return {};
            vz vertices;
            string rem = command.substr(prefix.size());
            while (rem.size()) {
                z i = rem.find_first_of(' ');
                string name = rem.substr(0, i);
                if (!name_to_index.contains(name)) return {};
                vertices.push_back(name_to_index[name]);
                if (i==string::npos) break;
                rem = rem.substr(i + 1);
            }
            return vertices.size() == positions ? optional(vertices) : nullopt;
        };

        if (match( "quit",0)) {
            cout<<"ok"<<endl;
            break;
        }
        for (string party:{"cop", "R"}) {
            if (auto m = match("start with "+party+" turn in", gm.k+1)) {
                multiset<z> cops(m->begin(), --m->end());
                z r = (*m)[gm.k];
                state s(gm, party == "cop" ? cops : multiset<z>{}, party == "R" ? cops : multiset<z>{}, r);
                if (!s.is_legal()) { cout<<"Rejected; state not legal."<<endl; goto continu; }
                if (s.is_final()) { cout<<"Rejected; state final."<<endl; goto continu; }
                set_cur(s);
                choose(move);
                goto continu;
            }
        }
        if (cur->is_r_turn()) {
            if (auto m=match("", 1)) {
                z r = (*m)[0];
                state s(gm, cur->moved_cops, {}, r);
                if (!ranges::count(cur->next_states(), s)) { cout<<"Rejected; move is not possible."<<endl; continue; }
                if (gm.attacking && cur->r != gm.INITIAL_VERTEX && cur->moved_cops.contains(r)) // eliminate a cop if possible (for simpler I/O, we do not leave a choice here)
                    set_cur(s.move_cop(r, gm.GRAVE_VERTEX, 0, 1));
                else
                    set_cur(s);
                move(choose);
                continue;
            }
        }
        else {
            if (auto m = match("", gm.k)) {
                multiset<z> cops(m->begin(), m->end());
                state s(gm, {}, cops, cur->r);
                if (!ranges::count(cur->next_states(), s)) { cout<<"Rejected; move is not possible."<<endl; continue; }
                set_cur(s);
                move(choose);
                continue;
            }
        }
        cout << "Rejected; illegal command." << endl;
        continu:;
    }
}

void analyze_and_interact(const game& gm, function<string(z)> vertex_names = [](z ix){return to_string(ix);}) {
    auto res = analyze(gm);
    cout << "winner: " << (res.is_copwin() ? "cops" : "R") << endl;
    interact(gm, res, vertex_names);
}

////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////// graph utils
////////////////////////////////////////////////////////////////////

namespace graph_utils {
    // only works with simple (i.e. undirected, no loops, no duplicate edges) graphs

    vvz strong_prod(vvz g, vvz h) {
        z n = g.size(), m = h.size();
        vvz p(n*m);
        for (z u = 0; u < n; ++u) {
            for (z a = 0; a < m; ++a) {
                for(z v:g[u]) {
                    for(z b:h[a]) {
                        p[u*m+a].push_back(v*m+b);
                    }
                }
                for(z v:g[u]) {
                    p[u*m+a].push_back(v*m+a);
                }
                for(z b:h[a]) {
                    p[u*m+a].push_back(u*m+b);
                }
            }
        }
        return p;
    }

    vvz cart_prod(vvz g, vvz h) {
        z n = g.size(), m = h.size();
        vvz p(n*m);
        for (z u = 0; u < n; ++u) {
            for (z a = 0; a < m; ++a) {
                for(z v:g[u]) {
                    p[u*m+a].push_back(v*m+a);
                }
                for(z b:h[a]) {
                    p[u*m+a].push_back(u*m+b);
                }
            }
        }
        return p;
    }

    vvz partition_edges(vvz g) {
        z n = g.size();
        vvz h(n);
        for (z u = 0; u < n; ++u) {
            for(z v:g[u]) {
                if(u<v) {
                    h[u].push_back(h.size());
                    h[v].push_back(h.size());
                    h.push_back({u,v});
                }
            }
        }
        return h;
    }

    vvz line_graph(vvz g) {
        map<vz, z> edges;
        for (z u = 0; u < g.size(); ++u) {
            for (z v: g[u]) if (u<v) {
                z id = edges.size();
                edges[{u,v}] = id;
            }
        }
        vvz l(edges.size());
        for (auto [e,id]:edges)
            for (z u:e)
                for (z v:g[u]) if(!ranges::count(e, v))
                    l[id].push_back(edges[{min(u,v), max(u,v)}]);
        return l;
    }


    vvz path(z vertices) {
        vvz g(vertices);
        for (z i = 0; i < vertices-1; ++i) {
            z o = i+1;
            g[i].push_back(o);
            g[o].push_back(i);
        }
        return g;
    }

    vvz cycle(z len) {
        vvz g(len);
        for (z i = 0; i < len; ++i) {
            z o = (i+1)%len;
            g[i].push_back(o);
            g[o].push_back(i);
        }
        return g;
    }

    vvz grid(z a, z b) {
        return cart_prod(path(a), path(b));
    }

    vvz hypercube(z dim) {
        return dim == 0 ? vvz(1) : cart_prod(path(2), hypercube(dim - 1));
    }

    vvz petersen(z n=5, z k=2) { // https://en.wikipedia.org/wiki/Generalized_Petersen_graph
        vvz g(2*n);
        auto add_edge=[&](z u, z v) {
            assert(u!=v);
            assert(!ranges::count(g[u], v));
            g[u].push_back(v);
            g[v].push_back(u);
        };
        for (z i = 0; i < n; ++i) {
            add_edge(i, (i+1)%n); // outer cycle
            add_edge(n + i, n + (i+k)%n); // inner star
            add_edge(i, n + i); // connect inner+outer
        }
        return g;
    }
}

using namespace graph_utils;


////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////// Tests
////////////////////////////////////////////////////////////////////

void test_multiset_enumerator() {
    for (z n: vz{1, 7}) {
        for (z k: vz{1, 2, 5}) {
            multiset_enumerator e(n, k);
            auto ms = e.all_multisets(n, k);
            assert(e.count(n, k) == ms.size());
            for (auto m:ms) {
                u64 id = e.multiset_to_id(n, m);
                assert(id < e.count(n, k)); //i.e. multiset_to_id maps to 0..cnt[k][n]
                auto m2 = e.id_to_multiset(n, k, id);
                assert(m2==m); //i.e. multiset_to_id is injective
            }
        }
    }
}

void test_state_enumerator() {
    for (z normal_vertices: vz{1, 7}) {
        for (z k: vz{1, 2, 5}) {
            for (z attacking = 0; attacking < 2; ++attacking) {
                for (z r_flexible = 0; r_flexible < 2; ++r_flexible) {
                    vvz g(normal_vertices);
                    game gm(g, k);
                    z all_vertices = gm.all_vertices;
                    vector<state> states;
                    for (z unmoved = 0; unmoved <= k; ++unmoved) {
                        for (auto unmovedCops: gm.state_enumeratr.mset_enumerator.all_multisets(all_vertices, unmoved)) {
                            for (auto movedCops: gm.state_enumeratr.mset_enumerator.all_multisets(all_vertices, k - unmoved)) {
                                for (z r = 0; r < all_vertices; ++r) {
                                    states.emplace_back(gm, unmovedCops, movedCops, r);
                                }
                            }
                        }
                    }
                    assert(states.size() == gm.state_enumeratr.count_states());
                    for (auto s: states) {
                        u64 id = gm.state_enumeratr.state_to_id(s);
                        assert(id < gm.state_enumeratr.count_states());
                        auto s2 = gm.state_enumeratr.id_to_state(id);
                        assert(s2 == s);
                    }
                }
            }
        }
    }
}

void test_prev_states() {
    for (auto g:{path(1), path(6), cart_prod(cycle(5), path(4)), line_graph(petersen(7))}) {
        for (z attacking = 0; attacking < 2; ++attacking) {
            for (z r_flexible = 0; r_flexible < 2; ++r_flexible) {
                for (z k:{1,3}) {
                    game gm(g, k, attacking, r_flexible);
                    gm.foreach_legal_state([](state s) {
                        for (string direction : vector{"fwd", "bwd"}) {
                            for (auto o: direction == "fwd" ? s.next_states() : s.prev_states()) {
                                assert(o.is_legal());
                                auto o_back = direction == "fwd" ? o.prev_states() : o.next_states();
                                z cnt = ranges::count(o_back, s);
                                if (cnt != 1) {
                                    cerr<<s<<endl;
                                    cerr<<direction<<endl;
                                    cerr<<o<<endl;
                                    cerr<<cnt<<endl;
                                    auto for_debugging_fwd = direction == "fwd" ? s.next_states() : s.prev_states(); //this is a good place for a breakpoint
                                    auto for_debugging_bwd = direction == "fwd" ? o.prev_states() : o.next_states();
                                }
                                assert(cnt == 1); // ==1 (rather than >0) is important
                            }
                        }
                    });
                }
            }
        }
    }
}

void check_copnumber(vvz g, bool attacking, bool r_flexible, z copnumber) {
    for (z cops : {copnumber-1, copnumber}) {
        game gm(g, cops, attacking, r_flexible);
        auto res = analyze(gm);
        bool correct = res.is_copwin() == (cops >= copnumber);
        if (!correct) {
            cerr << "The cop number for a test instance does not match declared cop number; " << cops << " cops " << (cops<copnumber ? "can win" : "loose") << "." << endl;
            cerr << "The instance: " << "|g|=" << g.size() << ", attacking=" << attacking << ", r_flexible=" << r_flexible << "," << endl;
            cerr << "E(g) = { " << endl;
            for (z u = 0; u < g.size(); ++u) {
                for (z v : g[u]) {
                    if (u<=v) {
                        assert(u!=v);
                        cerr << u << "-" << v << " ";
                    }
                }
            }
            cerr << "}" << endl;
            cerr << "Starting interaction for debugging." << endl;
            interact(gm, res);
            assert(0);
        }
    }
}

void test_known_copnumbers() {
    check_copnumber(path(1), 0, 1, 1);
    check_copnumber(path(10), 0, 1, 1);
    check_copnumber(cycle(3), 0, 1, 1);
    check_copnumber(cycle(4), 0, 1, 2);
    check_copnumber(cycle(10), 0, 1, 2);
    check_copnumber(hypercube(3), 0, 1, 2);
    check_copnumber(petersen(), 0, 1, 3);
    check_copnumber(line_graph(petersen()), 0, 1, 2);
    check_copnumber(line_graph(petersen(7)), 0, 1, 2);

    check_copnumber(path(1), 0, 0, 1);
    check_copnumber(cycle(4), 0, 0, 1);
    check_copnumber(cycle(5), 0, 0, 2);

    check_copnumber(path(1), 1, 1, 1);
    check_copnumber(path(3), 1, 1, 1);
    check_copnumber(path(4), 1, 1, 2);
    check_copnumber(path(10), 1, 1, 2);
    check_copnumber(cycle(3), 1, 1, 1);
    check_copnumber(cycle(4), 1, 1, 2);
    check_copnumber(cycle(6), 1, 1, 2);
    check_copnumber(cycle(7), 1, 1, 3);
    check_copnumber(cycle(10), 1, 1, 3);
    check_copnumber(hypercube(3), 1, 1, 2);
    check_copnumber(line_graph(petersen()), 1, 1, 3);
    check_copnumber(line_graph(petersen(7)), 1, 1, 4);

    check_copnumber(path(1), 1, 0, 1);
    check_copnumber(path(10), 1, 0, 1);
    check_copnumber(cycle(4), 1, 0, 1);
    check_copnumber(cycle(5), 1, 0, 2);
}

void tests() {
    test_multiset_enumerator();
    cout<<"test_multiset_enumerator done"<<endl;
    test_state_enumerator();
    cout<<"test_state_enumerator done"<<endl;
    test_prev_states();
    cout<<"test_prev_states done"<<endl;
    test_known_copnumbers();
    cout<<"test_known_copnumbers done"<<endl;
    cout<<"==================================== all tests done ===================================="<<endl<<endl;
}


////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////// main()
////////////////////////////////////////////////////////////////////

signed main() {
    cout << setprecision(5) << fixed;
    cerr << setprecision(5) << fixed;

    tests();

    vvz g = cart_prod(line_graph(petersen()), cycle(3));
    auto vertex_names = [](z u) {
        return
                to_string(u / 3) // petersen graph part
                + "-"
                + to_string(u % 3); // K_3 part
    };
    analyze_and_interact({g, 4, 1}, vertex_names); // output: cops win
}

#pragma clang diagnostic pop
