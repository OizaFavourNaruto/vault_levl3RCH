// Automatically generated with Reach 0.1.11 (578589af)
/* eslint-disable */
export const _version = '0.1.11';
export const _versionHash = '0.1.11 (578589af)';
export const _backendVersion = 17;

export function getExports(s) {
  const stdlib = s.reachStdlib;
  return {
    };
  };
export function _getEvents(s) {
  const stdlib = s.reachStdlib;
  return {
    };
  };
export function _getViews(s, viewlib) {
  const stdlib = s.reachStdlib;
  const ctc0 = stdlib.T_Address;
  const ctc1 = stdlib.T_UInt;
  const ctc2 = stdlib.T_Bool;
  
  return {
    infos: {
      },
    views: {
      1: [ctc0, ctc1, ctc1],
      2: [ctc0, ctc1, ctc1, ctc0, ctc1],
      5: [ctc0, ctc1, ctc0, ctc2, ctc1, ctc1, ctc2]
      }
    };
  
  };
export function _getMaps(s) {
  const stdlib = s.reachStdlib;
  const ctc0 = stdlib.T_Tuple([]);
  return {
    mapDataTy: ctc0
    };
  };
export async function Alice(ctcTop, interact) {
  if (typeof(ctcTop) !== 'object' || ctcTop._initialize === undefined) {
    return Promise.reject(new Error(`The backend for Alice expects to receive a contract as its first argument.`));}
  if (typeof(interact) !== 'object') {
    return Promise.reject(new Error(`The backend for Alice expects to receive an interact object as its second argument.`));}
  const ctc = ctcTop._initialize();
  const stdlib = ctc.stdlib;
  const ctc0 = stdlib.T_UInt;
  const ctc1 = stdlib.T_Bool;
  const ctc2 = stdlib.T_Tuple([ctc0]);
  const ctc3 = stdlib.T_Tuple([]);
  const ctc4 = stdlib.T_Null;
  const ctc5 = stdlib.T_Address;
  
  
  const v166 = stdlib.protect(ctc0, interact.deadline, 'for Alice\'s interact field deadline');
  const v167 = stdlib.protect(ctc0, interact.inheritance, 'for Alice\'s interact field inheritance');
  
  const txn1 = await (ctc.sendrecv({
    args: [v167, v166],
    evt_cnt: 2,
    funcNum: 0,
    lct: stdlib.checkedBigNumberify('./index.rsh:40:5:dot', stdlib.UInt_max, '0'),
    onlyIf: true,
    out_tys: [ctc0, ctc0],
    pay: [v167, []],
    sim_p: (async (txn1) => {
      const sim_r = { txns: [], mapRefs: [], maps: [] };
      let sim_txn_ctr = stdlib.UInt_max;
      const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
      
      
      const {data: [v171, v172], secs: v174, time: v173, didSend: v31, from: v170 } = txn1;
      
      sim_r.txns.push({
        amt: v171,
        kind: 'to',
        tok: undefined /* Nothing */
        });
      sim_r.isHalt = false;
      
      return sim_r;
      }),
    soloSend: true,
    timeoutAt: undefined /* mto */,
    tys: [ctc0, ctc0],
    waitIfNotPresent: false
    }));
  const {data: [v171, v172], secs: v174, time: v173, didSend: v31, from: v170 } = txn1;
  ;
  const txn2 = await (ctc.recv({
    didSend: false,
    evt_cnt: 1,
    funcNum: 1,
    out_tys: [ctc1],
    timeoutAt: undefined /* mto */,
    waitIfNotPresent: false
    }));
  const {data: [v181], secs: v183, time: v182, didSend: v40, from: v180 } = txn2;
  ;
  const v186 = stdlib.protect(ctc1, await interact.getChoice(), {
    at: './index.rsh:63:54:application',
    fs: ['at ./index.rsh:62:9:application call to [unknown function] (defined at: ./index.rsh:62:13:function exp)'],
    msg: 'getChoice',
    who: 'Alice'
    });
  
  const txn3 = await (ctc.sendrecv({
    args: [v170, v171, v172, v180, v182, v186],
    evt_cnt: 1,
    funcNum: 2,
    lct: v182,
    onlyIf: true,
    out_tys: [ctc1],
    pay: [stdlib.checkedBigNumberify('./index.rsh:65:5:decimal', stdlib.UInt_max, '0'), []],
    sim_p: (async (txn3) => {
      const sim_r = { txns: [], mapRefs: [], maps: [] };
      let sim_txn_ctr = stdlib.UInt_max;
      const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
      
      
      const {data: [v188], secs: v190, time: v189, didSend: v50, from: v187 } = txn3;
      
      ;
      const v198 = stdlib.add(v182, v172);
      const v200 = v171;
      const v201 = true;
      const v203 = v189;
      
      if (await (async () => {
        const v213 = v201 ? false : true;
        
        return v213;})()) {
        sim_r.isHalt = false;
        }
      else {
        const v258 = v188 ? v170 : v180;
        sim_r.txns.push({
          kind: 'from',
          to: v258,
          tok: undefined /* Nothing */
          });
        sim_r.txns.push({
          kind: 'halt',
          tok: undefined /* Nothing */
          })
        sim_r.isHalt = true;
        }
      return sim_r;
      }),
    soloSend: true,
    timeoutAt: undefined /* mto */,
    tys: [ctc5, ctc0, ctc0, ctc5, ctc0, ctc1],
    waitIfNotPresent: false
    }));
  const {data: [v188], secs: v190, time: v189, didSend: v50, from: v187 } = txn3;
  ;
  const v191 = stdlib.addressEq(v170, v187);
  stdlib.assert(v191, {
    at: './index.rsh:65:5:dot',
    fs: [],
    msg: 'sender correct',
    who: 'Alice'
    });
  const v198 = stdlib.add(v182, v172);
  let v200 = v171;
  let v201 = true;
  let v203 = v189;
  
  while (await (async () => {
    const v213 = v201 ? false : true;
    
    return v213;})()) {
    const txn4 = await (ctc.recv({
      didSend: false,
      evt_cnt: 1,
      funcNum: 4,
      out_tys: [ctc2],
      timeoutAt: ['time', v198],
      waitIfNotPresent: false
      }));
    if (txn4.didTimeout) {
      const txn5 = await (ctc.recv({
        didSend: false,
        evt_cnt: 1,
        funcNum: 5,
        out_tys: [ctc3],
        timeoutAt: undefined /* mto */,
        waitIfNotPresent: false
        }));
      const {data: [v248], secs: v250, time: v249, didSend: v134, from: v247 } = txn5;
      undefined /* setApiDetails */;
      ;
      const v251 = null;
      await txn5.getOutput('Bobs_informTimeout', 'v251', ctc4, v251);
      const cv200 = v200;
      const cv201 = false;
      const cv203 = v249;
      
      v200 = cv200;
      v201 = cv201;
      v203 = cv203;
      
      continue;
      }
    else {
      const {data: [v222], secs: v224, time: v223, didSend: v103, from: v221 } = txn4;
      undefined /* setApiDetails */;
      ;
      const v226 = v222[stdlib.checkedBigNumberify('./index.rsh:135:7:spread', stdlib.UInt_max, '0')];
      const v227 = stdlib.eq(v226, v200);
      if (v227) {
        const v228 = true;
        await txn4.getOutput('Bobs_acceptTerms', 'v228', ctc1, v228);
        const cv200 = v200;
        const cv201 = v201;
        const cv203 = v223;
        
        v200 = cv200;
        v201 = cv201;
        v203 = cv203;
        
        continue;}
      else {
        const v236 = false;
        await txn4.getOutput('Bobs_acceptTerms', 'v236', ctc1, v236);
        const cv200 = v200;
        const cv201 = v201;
        const cv203 = v223;
        
        v200 = cv200;
        v201 = cv201;
        v203 = cv203;
        
        continue;}}
    
    }
  const v258 = v188 ? v170 : v180;
  ;
  return;
  
  
  
  
  
  
  };
export async function Bob(ctcTop, interact) {
  if (typeof(ctcTop) !== 'object' || ctcTop._initialize === undefined) {
    return Promise.reject(new Error(`The backend for Bob expects to receive a contract as its first argument.`));}
  if (typeof(interact) !== 'object') {
    return Promise.reject(new Error(`The backend for Bob expects to receive an interact object as its second argument.`));}
  const ctc = ctcTop._initialize();
  const stdlib = ctc.stdlib;
  const ctc0 = stdlib.T_UInt;
  const ctc1 = stdlib.T_Bool;
  const ctc2 = stdlib.T_Tuple([ctc0]);
  const ctc3 = stdlib.T_Tuple([]);
  const ctc4 = stdlib.T_Null;
  const ctc5 = stdlib.T_Address;
  
  
  const txn1 = await (ctc.recv({
    didSend: false,
    evt_cnt: 2,
    funcNum: 0,
    out_tys: [ctc0, ctc0],
    timeoutAt: undefined /* mto */,
    waitIfNotPresent: false
    }));
  const {data: [v171, v172], secs: v174, time: v173, didSend: v31, from: v170 } = txn1;
  ;
  const v179 = stdlib.protect(ctc1, await interact.acceptTerms(v171), {
    at: './index.rsh:45:49:application',
    fs: ['at ./index.rsh:44:9:application call to [unknown function] (defined at: ./index.rsh:44:13:function exp)'],
    msg: 'acceptTerms',
    who: 'Bob'
    });
  
  const txn2 = await (ctc.sendrecv({
    args: [v170, v171, v172, v179],
    evt_cnt: 1,
    funcNum: 1,
    lct: v173,
    onlyIf: true,
    out_tys: [ctc1],
    pay: [stdlib.checkedBigNumberify('./index.rsh:47:5:decimal', stdlib.UInt_max, '0'), []],
    sim_p: (async (txn2) => {
      const sim_r = { txns: [], mapRefs: [], maps: [] };
      let sim_txn_ctr = stdlib.UInt_max;
      const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
      
      
      const {data: [v181], secs: v183, time: v182, didSend: v40, from: v180 } = txn2;
      
      ;
      sim_r.isHalt = false;
      
      return sim_r;
      }),
    soloSend: true,
    timeoutAt: undefined /* mto */,
    tys: [ctc5, ctc0, ctc0, ctc1],
    waitIfNotPresent: false
    }));
  const {data: [v181], secs: v183, time: v182, didSend: v40, from: v180 } = txn2;
  ;
  const txn3 = await (ctc.recv({
    didSend: false,
    evt_cnt: 1,
    funcNum: 2,
    out_tys: [ctc1],
    timeoutAt: undefined /* mto */,
    waitIfNotPresent: false
    }));
  const {data: [v188], secs: v190, time: v189, didSend: v50, from: v187 } = txn3;
  ;
  const v191 = stdlib.addressEq(v170, v187);
  stdlib.assert(v191, {
    at: './index.rsh:65:5:dot',
    fs: [],
    msg: 'sender correct',
    who: 'Bob'
    });
  const v198 = stdlib.add(v182, v172);
  let v200 = v171;
  let v201 = true;
  let v203 = v189;
  
  while (await (async () => {
    const v213 = v201 ? false : true;
    
    return v213;})()) {
    const txn4 = await (ctc.recv({
      didSend: false,
      evt_cnt: 1,
      funcNum: 4,
      out_tys: [ctc2],
      timeoutAt: ['time', v198],
      waitIfNotPresent: false
      }));
    if (txn4.didTimeout) {
      const txn5 = await (ctc.recv({
        didSend: false,
        evt_cnt: 1,
        funcNum: 5,
        out_tys: [ctc3],
        timeoutAt: undefined /* mto */,
        waitIfNotPresent: false
        }));
      const {data: [v248], secs: v250, time: v249, didSend: v134, from: v247 } = txn5;
      undefined /* setApiDetails */;
      ;
      const v251 = null;
      await txn5.getOutput('Bobs_informTimeout', 'v251', ctc4, v251);
      const cv200 = v200;
      const cv201 = false;
      const cv203 = v249;
      
      v200 = cv200;
      v201 = cv201;
      v203 = cv203;
      
      continue;
      }
    else {
      const {data: [v222], secs: v224, time: v223, didSend: v103, from: v221 } = txn4;
      undefined /* setApiDetails */;
      ;
      const v226 = v222[stdlib.checkedBigNumberify('./index.rsh:135:7:spread', stdlib.UInt_max, '0')];
      const v227 = stdlib.eq(v226, v200);
      if (v227) {
        const v228 = true;
        await txn4.getOutput('Bobs_acceptTerms', 'v228', ctc1, v228);
        const cv200 = v200;
        const cv201 = v201;
        const cv203 = v223;
        
        v200 = cv200;
        v201 = cv201;
        v203 = cv203;
        
        continue;}
      else {
        const v236 = false;
        await txn4.getOutput('Bobs_acceptTerms', 'v236', ctc1, v236);
        const cv200 = v200;
        const cv201 = v201;
        const cv203 = v223;
        
        v200 = cv200;
        v201 = cv201;
        v203 = cv203;
        
        continue;}}
    
    }
  const v258 = v188 ? v170 : v180;
  ;
  return;
  
  
  
  
  
  
  };
export async function _Bobs_acceptTerms5(ctcTop, interact) {
  if (typeof(ctcTop) !== 'object' || ctcTop._initialize === undefined) {
    return Promise.reject(new Error(`The backend for _Bobs_acceptTerms5 expects to receive a contract as its first argument.`));}
  if (typeof(interact) !== 'object') {
    return Promise.reject(new Error(`The backend for _Bobs_acceptTerms5 expects to receive an interact object as its second argument.`));}
  const ctc = ctcTop._initialize();
  const stdlib = ctc.stdlib;
  const ctc0 = stdlib.T_Address;
  const ctc1 = stdlib.T_UInt;
  const ctc2 = stdlib.T_Bool;
  const ctc3 = stdlib.T_Tuple([ctc1]);
  const ctc4 = stdlib.T_Null;
  
  
  const [v170, v171, v180, v188, v198, v200, v201] = await ctc.getState(stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '5'), [ctc0, ctc1, ctc0, ctc2, ctc1, ctc1, ctc2]);
  const v216 = stdlib.protect(ctc3, await interact.in(), {
    at: './index.rsh:1:23:application',
    fs: ['at ./index.rsh:135:7:application call to [unknown function] (defined at: ./index.rsh:135:7:function exp)', 'at ./index.rsh:135:7:application call to [unknown function] (defined at: ./index.rsh:135:7:function exp)'],
    msg: 'in',
    who: 'Bobs_acceptTerms'
    });
  
  const txn1 = await (ctc.sendrecv({
    args: [v170, v171, v180, v188, v198, v200, v201, v216],
    evt_cnt: 1,
    funcNum: 4,
    lct: stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '0'),
    onlyIf: true,
    out_tys: [ctc3],
    pay: [stdlib.checkedBigNumberify('./index.rsh:135:7:decimal', stdlib.UInt_max, '0'), []],
    sim_p: (async (txn1) => {
      const sim_r = { txns: [], mapRefs: [], maps: [] };
      let sim_txn_ctr = stdlib.UInt_max;
      const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
      
      
      const {data: [v222], secs: v224, time: v223, didSend: v103, from: v221 } = txn1;
      
      sim_r.txns.push({
        kind: 'api',
        who: "Bobs_acceptTerms"
        });
      ;
      const v226 = v222[stdlib.checkedBigNumberify('./index.rsh:135:7:spread', stdlib.UInt_max, '0')];
      const v227 = stdlib.eq(v226, v200);
      if (v227) {
        const v228 = true;
        const v229 = await txn1.getOutput('Bobs_acceptTerms', 'v228', ctc2, v228);
        
        const v415 = v200;
        const v416 = v201;
        if (v201) {
          const v419 = v188 ? v170 : v180;
          sim_r.txns.push({
            kind: 'from',
            to: v419,
            tok: undefined /* Nothing */
            });
          sim_r.txns.push({
            kind: 'halt',
            tok: undefined /* Nothing */
            })
          sim_r.isHalt = true;
          }
        else {
          sim_r.isHalt = false;
          }}
      else {
        const v236 = false;
        const v237 = await txn1.getOutput('Bobs_acceptTerms', 'v236', ctc2, v236);
        
        const v420 = v200;
        const v421 = v201;
        if (v201) {
          const v424 = v188 ? v170 : v180;
          sim_r.txns.push({
            kind: 'from',
            to: v424,
            tok: undefined /* Nothing */
            });
          sim_r.txns.push({
            kind: 'halt',
            tok: undefined /* Nothing */
            })
          sim_r.isHalt = true;
          }
        else {
          sim_r.isHalt = false;
          }}
      return sim_r;
      }),
    soloSend: false,
    timeoutAt: undefined /* mto */,
    tys: [ctc0, ctc1, ctc0, ctc2, ctc1, ctc1, ctc2, ctc3],
    waitIfNotPresent: false
    }));
  const {data: [v222], secs: v224, time: v223, didSend: v103, from: v221 } = txn1;
  undefined /* setApiDetails */;
  ;
  const v226 = v222[stdlib.checkedBigNumberify('./index.rsh:135:7:spread', stdlib.UInt_max, '0')];
  const v227 = stdlib.eq(v226, v200);
  if (v227) {
    const v228 = true;
    const v229 = await txn1.getOutput('Bobs_acceptTerms', 'v228', ctc2, v228);
    if (v103) {
      stdlib.protect(ctc4, await interact.out(v222, v229), {
        at: './index.rsh:135:8:application',
        fs: ['at ./index.rsh:135:8:application call to [unknown function] (defined at: ./index.rsh:135:8:function exp)', 'at ./index.rsh:137:8:application call to "k" (defined at: ./index.rsh:135:31:function exp)', 'at ./index.rsh:135:31:application call to [unknown function] (defined at: ./index.rsh:135:31:function exp)'],
        msg: 'out',
        who: 'Bobs_acceptTerms'
        });
      }
    else {
      }
    
    const v415 = v200;
    const v416 = v201;
    if (v201) {
      const v419 = v188 ? v170 : v180;
      ;
      return;
      }
    else {
      return;
      }}
  else {
    const v236 = false;
    const v237 = await txn1.getOutput('Bobs_acceptTerms', 'v236', ctc2, v236);
    if (v103) {
      stdlib.protect(ctc4, await interact.out(v222, v237), {
        at: './index.rsh:135:8:application',
        fs: ['at ./index.rsh:135:8:application call to [unknown function] (defined at: ./index.rsh:135:8:function exp)', 'at ./index.rsh:139:8:application call to "k" (defined at: ./index.rsh:135:31:function exp)', 'at ./index.rsh:135:31:application call to [unknown function] (defined at: ./index.rsh:135:31:function exp)'],
        msg: 'out',
        who: 'Bobs_acceptTerms'
        });
      }
    else {
      }
    
    const v420 = v200;
    const v421 = v201;
    if (v201) {
      const v424 = v188 ? v170 : v180;
      ;
      return;
      }
    else {
      return;
      }}
  
  
  };
export async function _Bobs_informTimeout5(ctcTop, interact) {
  if (typeof(ctcTop) !== 'object' || ctcTop._initialize === undefined) {
    return Promise.reject(new Error(`The backend for _Bobs_informTimeout5 expects to receive a contract as its first argument.`));}
  if (typeof(interact) !== 'object') {
    return Promise.reject(new Error(`The backend for _Bobs_informTimeout5 expects to receive an interact object as its second argument.`));}
  const ctc = ctcTop._initialize();
  const stdlib = ctc.stdlib;
  const ctc0 = stdlib.T_Address;
  const ctc1 = stdlib.T_UInt;
  const ctc2 = stdlib.T_Bool;
  const ctc3 = stdlib.T_Tuple([]);
  const ctc4 = stdlib.T_Null;
  
  
  const [v170, v171, v180, v188, v198, v200, v201] = await ctc.getState(stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '5'), [ctc0, ctc1, ctc0, ctc2, ctc1, ctc1, ctc2]);
  const v246 = stdlib.protect(ctc3, await interact.in(), {
    at: './index.rsh:144:5:application',
    fs: ['at ./index.rsh:144:5:application call to [unknown function] (defined at: ./index.rsh:144:5:function exp)', 'at ./index.rsh:143:29:application call to [unknown function] (defined at: ./index.rsh:143:29:function exp)'],
    msg: 'in',
    who: 'Bobs_informTimeout'
    });
  
  const txn1 = await (ctc.sendrecv({
    args: [v170, v171, v180, v188, v198, v200, v201, v246],
    evt_cnt: 1,
    funcNum: 5,
    lct: stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '0'),
    onlyIf: true,
    out_tys: [ctc3],
    pay: [stdlib.checkedBigNumberify('./index.rsh:144:5:decimal', stdlib.UInt_max, '0'), []],
    sim_p: (async (txn1) => {
      const sim_r = { txns: [], mapRefs: [], maps: [] };
      let sim_txn_ctr = stdlib.UInt_max;
      const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
      
      
      const {data: [v248], secs: v250, time: v249, didSend: v134, from: v247 } = txn1;
      
      sim_r.txns.push({
        kind: 'api',
        who: "Bobs_informTimeout"
        });
      ;
      const v251 = null;
      const v252 = await txn1.getOutput('Bobs_informTimeout', 'v251', ctc4, v251);
      
      const v425 = v200;
      const v426 = false;
      sim_r.isHalt = false;
      
      return sim_r;
      }),
    soloSend: false,
    timeoutAt: undefined /* mto */,
    tys: [ctc0, ctc1, ctc0, ctc2, ctc1, ctc1, ctc2, ctc3],
    waitIfNotPresent: false
    }));
  const {data: [v248], secs: v250, time: v249, didSend: v134, from: v247 } = txn1;
  undefined /* setApiDetails */;
  ;
  const v251 = null;
  const v252 = await txn1.getOutput('Bobs_informTimeout', 'v251', ctc4, v251);
  stdlib.protect(ctc4, await interact.out(v248, v252), {
    at: './index.rsh:144:5:application',
    fs: ['at ./index.rsh:144:5:application call to [unknown function] (defined at: ./index.rsh:144:5:function exp)', 'at ./index.rsh:145:6:application call to "k" (defined at: ./index.rsh:144:5:function exp)', 'at ./index.rsh:143:29:application call to [unknown function] (defined at: ./index.rsh:143:29:function exp)'],
    msg: 'out',
    who: 'Bobs_informTimeout'
    });
  
  const v425 = v200;
  const v426 = false;
  return;
  
  
  
  };
export async function Bobs_acceptTerms(ctcTop, interact) {
  if (typeof(ctcTop) !== 'object' || ctcTop._initialize === undefined) {
    return Promise.reject(new Error(`The backend for Bobs_acceptTerms expects to receive a contract as its first argument.`));}
  if (typeof(interact) !== 'object') {
    return Promise.reject(new Error(`The backend for Bobs_acceptTerms expects to receive an interact object as its second argument.`));}
  const ctc = ctcTop._initialize();
  const stdlib = ctc.stdlib;
  const step = await ctc.getCurrentStep()
  if (step == 5) {return _Bobs_acceptTerms5(ctcTop, interact);}
  throw stdlib.apiStateMismatchError({ _stateSourceMap }, [stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '5')], stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, step))
  };
export async function Bobs_informTimeout(ctcTop, interact) {
  if (typeof(ctcTop) !== 'object' || ctcTop._initialize === undefined) {
    return Promise.reject(new Error(`The backend for Bobs_informTimeout expects to receive a contract as its first argument.`));}
  if (typeof(interact) !== 'object') {
    return Promise.reject(new Error(`The backend for Bobs_informTimeout expects to receive an interact object as its second argument.`));}
  const ctc = ctcTop._initialize();
  const stdlib = ctc.stdlib;
  const step = await ctc.getCurrentStep()
  if (step == 5) {return _Bobs_informTimeout5(ctcTop, interact);}
  throw stdlib.apiStateMismatchError({ _stateSourceMap }, [stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '5')], stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, step))
  };
const _ALGO = {
  ABI: {
    impure: [`Bobs_acceptTerms(uint64)byte`, `Bobs_informTimeout()byte[0]`],
    pure: [],
    sigs: [`Bobs_acceptTerms(uint64)byte`, `Bobs_informTimeout()byte[0]`]
    },
  appApproval: `BiAKAAEFAiAIutmiiwhJUSgmAgEAACI1ADEYQQMYKWRJIls1ASEFWzUCNhoAF0lBACMiNQQjNQZJIQYMQAAKIQYSRDYaAUIAj4G7/fvrBhJEKUIAIzYaAhc1BDYaAzYaARdJJQxAAW1JgQQMQAELSSQMQABiJBJEJDQBEkQ0BEkiEkw0AhIRRChkSTUDIQdbNf9JNQU1/oAEaJJkYzT+ULAyBjT/D0SACAAAAAAAAAD7sCk1BzQDVwAgNAMhBFs0A1coIDQDV0gBFzT/NAMhCFsiMgZCAbdIJDQBEkQ0BEkiEkw0AhIRRChkSTUDSUpKSVcAIDX/IQRbNf5XKCA1/VdIARc1/CEHWzX7IQhbNfpXWQEXNflJNQU1+IAEzjxwZjT4ULAyBjT7DEQ0+Bc0+hJBACSACQAAAAAAAADkAbCAAQE1BzT/NP40/TT8NPs0+jT5MgZCATaACQAAAAAAAADsALAoNQc0/zT+NP00/DT7NPo0+TIGQgEUJRJEJTQBEkQ0BEkiEkw0AhIRRChkSTUDSVcAIDX/IQRbNf5JNQUXNf2ABGoROgg0/RZRBwhQsDT/MQASRDT/NP40A1cwIDT9NAOBUFs0AyEJWwg0/iMyBkIAuUkjDEAAXkgjNAESRDQESSISTDQCEhFEKGRJNQNJSVcAIDX/IQRbNf4hCVs1/Uk1BRc1/IAED7/GNDT8FlEHCFCwNP80/hZQNP0WUDEAUDIGFlAoSwFXAFhnSCU1ATIGNQJCAMlIgaCNBogBEiI0ARJENARJIhJMNAISEURJNQVJIls1/yEFWzX+gASs0R/DNP8WUDT+FlCwNP+IAOExADT/FlA0/hZQKEsBVwAwZ0gjNQEyBjUCQgB0Nf81/jX9Nfw1+zX6Nfk1+DT+QQAYsSKyATT5sggjshA0+jT4NPtNsgezQgAsNPg0+RZQNPpQNPsWUQcIUDT8FlA0/RZQKFAoSwFXAFpnSCQ1ATIGNQJCABsxGSQSRLEisgEisggjshAyCbIJMgqyB7NCAAUxGSISRCk0ARY0AhZQZzQGQQAKgAQVH3x1NAdQsDQASSMIMgQSRDEWEkQjQzEZIhJEQv/fIjE0EkQlMTUSRCIxNhJEIjE3EkQiNQEiNQJC/680AElKIwg1ADgHMgoSRDgQIxJEOAgSRIk=`,
  appClear: `Bg==`,
  companionInfo: null,
  extraPages: 0,
  mapDataKeys: 0,
  mapDataSize: 0,
  stateKeys: 1,
  stateSize: 90,
  unsupported: [],
  version: 10,
  warnings: []
  };
const _ETH = {
  ABI: `[
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v171",
                "type": "uint256"
              },
              {
                "internalType": "uint256",
                "name": "v172",
                "type": "uint256"
              }
            ],
            "internalType": "struct T1",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "internalType": "struct T2",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "stateMutability": "payable",
    "type": "constructor"
  },
  {
    "inputs": [
      {
        "internalType": "uint256",
        "name": "msg",
        "type": "uint256"
      }
    ],
    "name": "ReachError",
    "type": "error"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v171",
                "type": "uint256"
              },
              {
                "internalType": "uint256",
                "name": "v172",
                "type": "uint256"
              }
            ],
            "internalType": "struct T1",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "indexed": false,
        "internalType": "struct T2",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e0",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "bool",
                "name": "v181",
                "type": "bool"
              }
            ],
            "internalType": "struct T4",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "indexed": false,
        "internalType": "struct T5",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e1",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "bool",
                "name": "v188",
                "type": "bool"
              }
            ],
            "internalType": "struct T9",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "indexed": false,
        "internalType": "struct T10",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e2",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "components": [
                  {
                    "internalType": "uint256",
                    "name": "elem0",
                    "type": "uint256"
                  }
                ],
                "internalType": "struct T12",
                "name": "v222",
                "type": "tuple"
              }
            ],
            "internalType": "struct T13",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "indexed": false,
        "internalType": "struct T14",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e4",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "bool",
                "name": "v248",
                "type": "bool"
              }
            ],
            "internalType": "struct T16",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "indexed": false,
        "internalType": "struct T17",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e5",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "bool",
        "name": "v0",
        "type": "bool"
      }
    ],
    "name": "_reach_oe_v228",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "bool",
        "name": "v0",
        "type": "bool"
      }
    ],
    "name": "_reach_oe_v236",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "bool",
        "name": "v0",
        "type": "bool"
      }
    ],
    "name": "_reach_oe_v251",
    "type": "event"
  },
  {
    "stateMutability": "payable",
    "type": "fallback"
  },
  {
    "inputs": [
      {
        "internalType": "uint256",
        "name": "_a0",
        "type": "uint256"
      }
    ],
    "name": "Bobs_acceptTerms",
    "outputs": [
      {
        "internalType": "bool",
        "name": "",
        "type": "bool"
      }
    ],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "inputs": [],
    "name": "Bobs_informTimeout",
    "outputs": [
      {
        "internalType": "bool",
        "name": "",
        "type": "bool"
      }
    ],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "inputs": [],
    "name": "_reachCreationTime",
    "outputs": [
      {
        "internalType": "uint256",
        "name": "",
        "type": "uint256"
      }
    ],
    "stateMutability": "view",
    "type": "function"
  },
  {
    "inputs": [],
    "name": "_reachCurrentState",
    "outputs": [
      {
        "internalType": "uint256",
        "name": "",
        "type": "uint256"
      },
      {
        "internalType": "bytes",
        "name": "",
        "type": "bytes"
      }
    ],
    "stateMutability": "view",
    "type": "function"
  },
  {
    "inputs": [],
    "name": "_reachCurrentTime",
    "outputs": [
      {
        "internalType": "uint256",
        "name": "",
        "type": "uint256"
      }
    ],
    "stateMutability": "view",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "bool",
                "name": "v181",
                "type": "bool"
              }
            ],
            "internalType": "struct T4",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "internalType": "struct T5",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m1",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "bool",
                "name": "v188",
                "type": "bool"
              }
            ],
            "internalType": "struct T9",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "internalType": "struct T10",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m2",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "components": [
                  {
                    "internalType": "uint256",
                    "name": "elem0",
                    "type": "uint256"
                  }
                ],
                "internalType": "struct T12",
                "name": "v222",
                "type": "tuple"
              }
            ],
            "internalType": "struct T13",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "internalType": "struct T14",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m4",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "bool",
                "name": "v248",
                "type": "bool"
              }
            ],
            "internalType": "struct T16",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "internalType": "struct T17",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m5",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "stateMutability": "payable",
    "type": "receive"
  }
]`,
  Bytecode: `0x6080604052604051620015c9380380620015c9833981016040819052620000269162000235565b6000805543600355604080513381528251602080830191909152808401518051838501520151606082015290517fa736757a943474ef5983bb0422ab3a1e64bcd39e99635f4430c7765118231f959181900360800190a16020810151516200009290341460076200012e565b620000c0604051806060016040528060006001600160a01b0316815260200160008152602001600081525090565b338082526020838101805151828501908152905182015160408086019182526001600081905543905580518085019590955291518483015251606080850191909152815180850390910181526080909301905281516200012592600292019062000158565b505050620002d2565b81620001545760405163100960cb60e01b81526004810182905260240160405180910390fd5b5050565b828054620001669062000295565b90600052602060002090601f0160209004810192826200018a5760008555620001d5565b82601f10620001a557805160ff1916838001178555620001d5565b82800160010185558215620001d5579182015b82811115620001d5578251825591602001919060010190620001b8565b50620001e3929150620001e7565b5090565b5b80821115620001e35760008155600101620001e8565b604080519081016001600160401b03811182821017156200022f57634e487b7160e01b600052604160045260246000fd5b60405290565b600081830360608112156200024957600080fd5b62000253620001fe565b835181526040601f19830112156200026a57600080fd5b62000274620001fe565b60208581015182526040909501518582015293810193909352509092915050565b600181811c90821680620002aa57607f821691505b60208210811415620002cc57634e487b7160e01b600052602260045260246000fd5b50919050565b6112e780620002e26000396000f3fe6080604052600436106100845760003560e01c80639a3e3912116100565780639a3e3912146100ec578063ab53f2c6146100ff578063ad9fa3d814610122578063bd2dd51414610135578063c179aa2c1461015857005b80630cf4bd231461008d5780631e93b0f1146100a05780633e59bac4146100c457806383230757146100d757005b3661008b57005b005b61008b61009b366004610e3f565b610160565b3480156100ac57600080fd5b506003545b6040519081526020015b60405180910390f35b61008b6100d2366004610e3f565b610190565b3480156100e357600080fd5b506001546100b1565b61008b6100fa366004610e3f565b6101bc565b34801561010b57600080fd5b506101146101e8565b6040516100bb929190610e62565b61008b610130366004610e3f565b610285565b610148610143366004610ebf565b6102b1565b60405190151581526020016100bb565b6101486102ed565b604080518082019091526000808252602082015261018c61018636849003840184610f0f565b82610328565b5050565b604080518082019091526000808252602082015261018c6101b63684900384018461104c565b8261056c565b604080518082019091526000808252602082015261018c6101e23684900384018461104c565b8261071c565b6000606060005460028080546101fd90611068565b80601f016020809104026020016040519081016040528092919081815260200182805461022990611068565b80156102765780601f1061024b57610100808354040283529160200191610276565b820191906000526020600020905b81548152906001019060200180831161025957829003601f168201915b50505050509050915091509091565b604080518082019091526000808252602082015261018c6102ab3684900384018461104c565b82610922565b60006102bb610ca7565b60208082015151849052604080518082019091526000808252918101919091526102e58282610328565b519392505050565b60006102f7610cd9565b602080820151600090819052604080518082019091528181529182015261031e8282610922565b6020015192915050565b6103386005600054146010610af9565b815161035390158061034c57508251600154145b6011610af9565b60008080556002805461036590611068565b80601f016020809104026020016040519081016040528092919081815260200182805461039190611068565b80156103de5780601f106103b3576101008083540402835291602001916103de565b820191906000526020600020905b8154815290600101906020018083116103c157829003601f168201915b50505050508060200190518101906103f691906110b9565b9050610409816080015143106012610af9565b60408051338152845160208083019190915285015151518183015290517f20e0220c6adfa181ccdf66a11a035e7ee7bc6900d5aa40894042309f10f8f0f99181900360600190a161045c3415600f610af9565b60a081015160208401515151141561052757604051600181527f9802431ed045d2c169076167047ff35ac79bd90d5148d6712e285d5b5d3f03089060200160405180910390a1600182526104ae610d03565b815181516001600160a01b03918216905260208084015183518201526040808501518451931692810192909252606080850151845190151591015260808085015184519091015260a084015181840180519190915260c08501518151901515920191909152514391015261052181610b1e565b50505050565b604051600081527fa80f9bcbccdf21f18dc80ef3a1185b3fd9e3817f49441ef1395f0a67831806ef9060200160405180910390a1600082526104ae610d03565b505050565b61057c600260005414600d610af9565b815161059790158061059057508251600154145b600e610af9565b6000808055600280546105a990611068565b80601f01602080910402602001604051908101604052809291908181526020018280546105d590611068565b80156106225780601f106105f757610100808354040283529160200191610622565b820191906000526020600020905b81548152906001019060200180831161060557829003601f168201915b505050505080602001905181019061063a9190611168565b90507fea301fa16f4bb7851ebe70b97d841398dfcfaffcc5b90514d4df21d88b62c5bd338460405161066d9291906111f2565b60405180910390a16106813415600b610af9565b8051610699906001600160a01b03163314600c610af9565b6106a1610d03565b815181516001600160a01b0391821690526020808401518351820152606080850151845193166040938401529086015151835190151591015282015160808301516106ec919061121c565b81516080015260208083015181830180519190915280516001920191909152514360409091015261052181610b1e565b61072c6001600054146009610af9565b815161074790158061074057508251600154145b600a610af9565b60008080556002805461075990611068565b80601f016020809104026020016040519081016040528092919081815260200182805461078590611068565b80156107d25780601f106107a7576101008083540402835291602001916107d2565b820191906000526020600020905b8154815290600101906020018083116107b557829003601f168201915b50505050508060200190518101906107ea9190611242565b90507fb6eea004ef7895e3731d4318847f013244765590bcd89a0cdcf6f1db231f4915338460405161081d9291906111f2565b60405180910390a161083134156008610af9565b6108756040518060a0016040528060006001600160a01b03168152602001600081526020016000815260200160006001600160a01b03168152602001600081525090565b81516001600160a01b03168152602080830151818301526040808401518184015233606084015243608084018190526002600055600155516108f79183910181516001600160a01b0390811682526020808401519083015260408084015190830152606080840151909116908201526080918201519181019190915260a00190565b6040516020818303038152906040526002908051906020019061091b929190610d58565b5050505050565b6109326005600054146014610af9565b815161094d90158061094657508251600154145b6015610af9565b60008080556002805461095f90611068565b80601f016020809104026020016040519081016040528092919081815260200182805461098b90611068565b80156109d85780601f106109ad576101008083540402835291602001916109d8565b820191906000526020600020905b8154815290600101906020018083116109bb57829003601f168201915b50505050508060200190518101906109f091906110b9565b9050610a0481608001514310156016610af9565b7f663356c9bc60432e38c96f881aa1e2828a9a5648f65169c66c8c7722e9c213653384604051610a359291906111f2565b60405180910390a1610a4934156013610af9565b604051600081527f59cd07daa480307f48b975df217034b64065edf410e27135caad35a6b9f297089060200160405180910390a160006020830152610a8c610d03565b815181516001600160a01b03918216905260208084015183518201526040808501518451931692810192909252606080850151845190151591015260808085015184519091015260a084015181840180519190915280516000920191909152514391015261052181610b1e565b8161018c5760405163100960cb60e01b81526004810182905260240160405180910390fd5b80602001516020015115610b9c57805160600151610b4157805160400151610b45565b8051515b8151602001516040516001600160a01b03929092169181156108fc0291906000818181858888f19350505050158015610b82573d6000803e3d6000fd5b5060008080556001819055610b9990600290610ddc565b50565b6040805160e081018252600080825260208201819052918101829052606081018290526080810182905260a0810182905260c08101919091528151516001600160a01b03908116808352835160209081015181850190815285516040908101518516818701908152875160609081015115158189019081528951608090810151818b01908152878c01515160a0808d01918252600060c0808f0182815260059092554360015589519b8c019c909c529851978a0197909752945190991692870192909252511515908501529451908301529251918101919091529051151560e08201526101000160405160208183030381529060405260029080519060200190610567929190610d58565b604051806040016040528060008152602001610cd460408051808201909152600060208201908152815290565b905290565b604051806040016040528060008152602001610cd460405180602001604052806000151581525090565b6040805160e0810182526000918101828152606082018390526080820183905260a0820183905260c0820192909252908190815260408051606081018252600080825260208281018290529282015291015290565b828054610d6490611068565b90600052602060002090601f016020900481019282610d865760008555610dcc565b82601f10610d9f57805160ff1916838001178555610dcc565b82800160010185558215610dcc579182015b82811115610dcc578251825591602001919060010190610db1565b50610dd8929150610e12565b5090565b508054610de890611068565b6000825580601f10610df8575050565b601f016020900490600052602060002090810190610b9991905b5b80821115610dd85760008155600101610e13565b600060408284031215610e3957600080fd5b50919050565b600060408284031215610e5157600080fd5b610e5b8383610e27565b9392505050565b82815260006020604081840152835180604085015260005b81811015610e9657858101830151858201606001528201610e7a565b81811115610ea8576000606083870101525b50601f01601f191692909201606001949350505050565b600060208284031215610ed157600080fd5b5035919050565b6040516020810167ffffffffffffffff81118282101715610f0957634e487b7160e01b600052604160045260246000fd5b60405290565b60008183036040811215610f2257600080fd5b6040516040810181811067ffffffffffffffff82111715610f5357634e487b7160e01b600052604160045260246000fd5b604052833581526020601f1983011215610f6c57600080fd5b610f74610ed8565b9150610f7e610ed8565b602094850135815282529283015250919050565b8015158114610b9957600080fd5b6000818303604080821215610fb457600080fd5b805181810167ffffffffffffffff8282108183111715610fe457634e487b7160e01b600052604160045260246000fd5b818452829550863583526020601f198601121561100057600080fd5b83519450602085019150848210818311171561102c57634e487b7160e01b600052604160045260246000fd5b5090915260208401359061103f82610f92565b9082526020015292915050565b60006040828403121561105e57600080fd5b610e5b8383610fa0565b600181811c9082168061107c57607f821691505b60208210811415610e3957634e487b7160e01b600052602260045260246000fd5b80516001600160a01b03811681146110b457600080fd5b919050565b600060e082840312156110cb57600080fd5b60405160e0810181811067ffffffffffffffff821117156110fc57634e487b7160e01b600052604160045260246000fd5b6040526111088361109d565b8152602083015160208201526111206040840161109d565b6040820152606083015161113381610f92565b806060830152506080830151608082015260a083015160a082015260c083015161115c81610f92565b60c08201529392505050565b600060a0828403121561117a57600080fd5b60405160a0810181811067ffffffffffffffff821117156111ab57634e487b7160e01b600052604160045260246000fd5b6040526111b78361109d565b815260208301516020820152604083015160408201526111d96060840161109d565b6060820152608083015160808201528091505092915050565b6001600160a01b038316815260608101610e5b602083018480518252602090810151511515910152565b6000821982111561123d57634e487b7160e01b600052601160045260246000fd5b500190565b60006060828403121561125457600080fd5b6040516060810181811067ffffffffffffffff8211171561128557634e487b7160e01b600052604160045260246000fd5b6040526112918361109d565b81526020830151602082015260408301516040820152809150509291505056fea2646970667358221220e6a849c4e0393ab9aea1171d1c8131b835122798ab8651ce4b9564f33990c33164736f6c634300080c0033`,
  BytecodeLen: 5577,
  Which: `oD`,
  version: 7,
  views: {
    }
  };
export const _stateSourceMap = {
  1: {
    at: './index.rsh:41:11:after expr stmt semicolon',
    fs: [],
    msg: null,
    who: 'Module'
    },
  2: {
    at: './index.rsh:48:11:after expr stmt semicolon',
    fs: [],
    msg: null,
    who: 'Module'
    },
  4: {
    at: './index.rsh:151:11:after expr stmt semicolon',
    fs: [],
    msg: null,
    who: 'Module'
    },
  5: {
    at: './index.rsh:132:17:after expr stmt semicolon',
    fs: [],
    msg: null,
    who: 'Module'
    }
  };
export const _Connectors = {
  ALGO: _ALGO,
  ETH: _ETH
  };
export const _Participants = {
  "Alice": Alice,
  "Bob": Bob,
  "Bobs_acceptTerms": Bobs_acceptTerms,
  "Bobs_informTimeout": Bobs_informTimeout
  };
export const _APIs = {
  Bobs: {
    acceptTerms: Bobs_acceptTerms,
    informTimeout: Bobs_informTimeout
    }
  };
