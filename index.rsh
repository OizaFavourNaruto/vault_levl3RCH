'reach 0.1';

const TIMER = 3;

const Shared = {
  showTime: Fun([UInt], Null),
  informTimeout: Fun([], Null),
  seeOutcome: Fun([Bool], Null),
};

export const main = Reach.App(() => {
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

 
  const V = View("Main", {
    amount : UInt
  })
  const C = API('Bobs', {
    ...Shared,
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
  V.amount.set(amt)
  commit();
  each([A, B], () => {
    interact.showTime(lastConsensusTime() + TIMER);
    interact.seeOutcome(true);
    // interact.informTimeout();
  });
  
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
 

 
  A.publish()
  // Level 2 
  var outcome = true;

  invariant( balance() == amt);
  while ( outcome ) {
    commit();
    A.only(() => {
      const aliceChoice = declassify(interact.getChoice())
    })
    A.publish(aliceChoice)
      .timeout(relativeTime(TIMER), () =>  closeTo(A, informTimeout))
    outcome = aliceChoice;
    continue;
  }
  // outcome ? transfer(amt).to(A) : transfer(amt).to(B)
  transfer(amt).to(outcome == true ? A : B);


  



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
  .timeout( timeLeft, () => {
    const [ [], k ] = call(C.informTimeout);
    k(null);
    return [ false, x, an ]
  });
   transfer(amt).to(outcome ? A : B);
  commit();
 
  exit();
});
