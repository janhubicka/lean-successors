#!/usr/bin/env python3
"""Independent directed-L and E3 regression for a gated M3 middle clone.

Checks spacing, downward E, E3, old-atom transport, and projection of
every induced irreducible subset through the new clone. This supplements
but never replaces the Lean proof.
"""
from itertools import product, combinations
from collections import Counter
import json

def potential_cuts(v):
    return [0] + list(range(1, max(1, v-1)))

def insert_ell(x, ell):
    return x if x < ell else x + 1

def inserted_cut(cuts, ell, d, v):
    if v < ell:
        return cuts[v]
    if v == ell:
        return d
    f = cuts[v-1]
    return f if f < ell else f + 1

def bits(sample_code, pairs, size):
    result = [[False]*size for _ in range(size)]
    for i, (u,v) in enumerate(pairs):
        result[u][v] = bool((sample_code >> i) & 1)
    return result

def codes_for(count, size):
    end=(1<<count)-1
    if size <= 4 or count <= 9:
        return range(1<<count)
    return sorted({0,1,end,end-1,end//2,end//3,(2*end)//3,
                   end//7,(5*end)//7,(13*end)//23})

def check_case(cuts, old, n, ell, unary, diag, ctr):
    size=len(cuts)
    assert n < ell <= size
    d=cuts[n]
    N=size+1
    B=[[False]*N for _ in range(N)]
    upper=[False]*N
    diagonals=[False]*N
    for x in range(size):
        sx=insert_ell(x,ell)
        upper[sx]=unary[x]
        diagonals[sx]=diag[x]
        for y in range(size):
            B[sx][insert_ell(y,ell)] = old[x][y]
    upper[ell]=unary[n]
    diagonals[ell]=diag[n]
    B[ell][ell]=old[n][n]
    for x in range(size):
        sx=insert_ell(x,ell)
        if x < ell:
            B[ell][sx]=old[n][x] if x<d else False
            B[sx][ell]=old[x][n] if x<d else False
        else:
            gate=ell <= cuts[x]
            B[ell][sx]=old[n][x] if gate else False
            B[sx][ell]=old[x][n] if gate else False
    E=[[v<N and u<inserted_cut(cuts,ell,d,v) for v in range(N)]
       for u in range(N)]
    for u in range(N):
        for v in range(N):
            if E[u][v]:
                assert u+1<v, ('spacing',cuts,n,ell,u,v)
                assert all(E[w][v] for w in range(u)), ('downward',cuts,n,ell,u,v)
            if u<v and (B[u][v] or B[v][u]):
                assert E[u][v], ('E3',cuts,n,ell,u,v)
            ctr['E3_atoms']+=1
    assert all(B[insert_ell(x,ell)][insert_ell(y,ell)]==old[x][y]
               for x in range(size) for y in range(size))
    for m in range(1,N+1):
        for subset in combinations(range(N),m):
            if ell not in subset:
                continue
            if any(not(B[x][y] or B[y][x])
                   for x,y in combinations(subset,2)):
                continue
            def proj(x):
                return n if x==ell else (x if x<ell else x-1)
            mapped=list(map(proj,subset))
            assert all(mapped[i]<mapped[i+1] for i in range(len(mapped)-1)), (
                'order',cuts,n,ell,subset,mapped)
            assert all(upper[x]==unary[proj(x)] and
                       diagonals[x]==diag[proj(x)] for x in subset)
            assert all(B[x][y]==old[proj(x)][proj(y)]
                       for x in subset for y in subset), (
                'L',cuts,n,ell,subset,mapped)
            ctr['irreducible_projected']+=1
    ctr['insertions']+=1

def main():
    ctr=Counter()
    for size in range(2,7):
        for cuts in product(*(potential_cuts(v) for v in range(size))):
            pairs=[(u,v) for v in range(size) for u in range(v)
                   if u < cuts[v]]
            directed=[pair for u,v in pairs for pair in ((u,v),(v,u))]
            for code in codes_for(len(directed),size):
                old=bits(code,directed,size)
                for tag in range(2):
                    unary=[bool((v+tag+code)%2) for v in range(size)]
                    diag=[bool((v*3+tag+code//2)%2) for v in range(size)]
                    for ell in range(1,size+1):
                        for n in range(ell):
                            check_case(cuts,old,n,ell,unary,diag,ctr)
    print(json.dumps(dict(sorted(ctr.items())),sort_keys=True))

if __name__ == '__main__':
    main()
