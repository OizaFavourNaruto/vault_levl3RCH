'reach 0.1';

const COUNTDOWNTIMER = 2;

const Shared = {
  showTime: Fun([UInt], Null),
  informTimeout: Fun([], Null),
  seeOutcome: Fun([Bool], Null),
}


export const main = Reach.App(() => {
  // setOptions({ untrustworthyMaps: true });
  const A = Participant('Alice', {
    ...Shared,
    // Specify Alice's interact interface here
    inheritance: UInt,
    getChoice: Fun([], Bool),
    deadline: UInt, // time delta (blocks/rounds)
  });
  const B = Participant('Bob', {
    ...Shared,
    // Specify Bob's interact interface here
    acceptTerms: Fun([UInt], Bool)
  });

  const C = API('Bobs', {
    informTimeout: Fun([], Null),
    // Specify Bob's interact interface here
    acceptTerms: Fun([UInt], Bool)
  })
  init();

  A.only(() =>{
    const amt = declassify(interact.inheritance)
    const timeLeft = declassify(interact.deadline);
  })
  // Alice deploys the contract and pays the contract the inheritance
  A.publish(amt, timeLeft).pay(amt);
  commit();
  
  // The second one to publish always attaches
  B.only(() => {
   const terms = declassify(interact.acceptTerms(amt)) 
  })
  B.publish(terms);
  commit();

  const informTimeout = () => {
    each([A, B], () => {
      // interact.showTime(lastConsensusTime() + COUNTDOWNTIMER)
      interact.informTimeout();
    });
  };

  // each([A, B ], () => {
  //   interact.showTime(COUNTDOWNTIMER)
  //   interact.informTimeout()
  // })

  A.only(() => {
    const aliceChoice = declassify(interact.getChoice())
  })
  A.publish(aliceChoice)
  // if(aliceChoice){
  //   transfer(amt).to(A)
  // }else{
  //   transfer(amt).to(B)
  // }
  // A.publish()

  // A.only(() => {
  //   const aliceChoice = declassify(interact.getChoice())
  // })
  // A.publish(aliceChoice)
  //   .timeout(relativeTime(COUNTDOWNTIMER), () => closeTo(B, informTimeout));
  // A.publish()

  // Level 2 
  // var outcome = true;
  // invariant( balance() == amt);
  // while ( outcome ) {
  //   commit();
  //   A.only(() => {
  //     const aliceChoice = declassify(interact.getChoice())
  //   })
  //   A.publish(aliceChoice)
  //     .timeout(relativeTime(COUNTDOWNTIMER), () =>  closeTo(A, informTimeout))
  //   outcome = aliceChoice;
  //   continue;
  // }
  // // outcome ? transfer(amt).to(A) : transfer(amt).to(B)
  // transfer(amt).to(outcome ? A : B);
  // commit();

  // each([A, B], () => {
  //   interact.showTime(lastConsensusTime() + COUNTDOWNTIMER);
  //   interact.seeOutcome(outcome);
  //   // interact.informTimeout();
  // });


  // LEVEL 3
  const bobDeadline = relativeTime(timeLeft);
  // const bobArray = new Set();

  // const [ timedOut, howmany] =
  // parallelReduce([ true, 0 ])
  // .invariant(balance() == amt)
  // .invariant(bobArray.Map.size() == howmany)
  // .while(!timedOut)
  // .api_(C.acceptTerms, (t) => {
  //   // check(t == amt);
  //   check(!bobArray.member(this));
  //   return [(k) => {
  //     bobArray.insert(this);
  //     k(aliceChoice);
  //     // transfer(amt).to(this);
  //     return [ timedOut, howmany + 1 ];
  //   }]; 
  // })
  // .timeout( bobDeadline, () => {
  //   const [ [], k ] = call(C.informTimeout);
  //   k(null);
  //   return [ false, howmany ]
  // });
  // transfer(amt).to(aliceChoice ? A : B);
  // commit()

  const [ done, x, an ] =
  parallelReduce([ true, 0, amt ])
  .invariant(balance() == amt)
  .while(!done )
  .api(C.acceptTerms, (nx, k) => {
    if(nx == an){
      k(true);
    }else{
      k(false);
    }
    return [ done, nx, an ];
  })
  .timeout( bobDeadline, () => {
    const [ [], k ] = call(C.informTimeout);
    k(null);
    return [ false, x, an ]
  });


 transfer(amt).to(aliceChoice ? A : B);
  commit();
  exit();
});
