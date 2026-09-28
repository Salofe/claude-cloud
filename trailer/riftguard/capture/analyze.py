import json, math, sys
for key in 'ABCD':
    d = json.load(open(f'scout_{key}.json'))
    log = d['log']; evs = d['evs']
    live = next(e[0] for e in evs if e[1]=='phase' and e[2]['ph']=='live')
    def snap(t):
        return min(log, key=lambda L: abs(L['t']-t))
    print(f'==== {key}  live at {live}')
    kills = [e for e in evs if e[1]=='kill']
    for e in evs:
        if e[1] != 'ult': continue
        t = e[0]; uid = e[2]['id']; S = snap(t)
        me = next((u for u in S['u'] if u[0]==uid), None)
        if not me: continue
        near = [u for u in S['u'] if u[0]!=uid and u[6] and math.hypot(u[3]-me[3], u[5]-me[5]) < 12]
        en = sum(1 for u in near if u[2]!=me[2])
        k3 = [k for k in kills if t <= k[0] <= t+4]
        kb = [k for k in k3 if k[2]['by']==uid]
        print(f"  ult t={t:7.2f} {e[2]['h']:9s} id={uid} pos=({me[3]},{me[4]},{me[5]}) near={len(near)} enemies={en} kills4s={len(k3)} byUlter={len(kb)}")
    # puppet kills
    pk = [k for k in kills if k[2]['by']==1]
    print('  puppet kills:', [(k[0], k[2]['th'], k[2]['ab'], k[2]['hd']) for k in pk])
    # kill clusters
    ts = sorted(k[0] for k in kills)
    cl = [(t, sum(1 for x in ts if t<=x<=t+3)) for t in ts]
    print('  busy 3s windows:', sorted(set((round(t,1),n) for t,n in cl if n>=3)))
