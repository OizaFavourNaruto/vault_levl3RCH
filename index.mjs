import {loadStdlib, ask} from '@reach-sh/stdlib';
import * as backend from './build/index.main.mjs';
const stdlib = loadStdlib(process.env);

const startingBalance = stdlib.parseCurrency(100);

// Alice and Bob account
const accAlice= await stdlib.newTestAccount(stdlib.parseCurrency(7000));
const accBob = await stdlib.newTestAccount(startingBalance)

console.log('Hello, Alice and Bob!');
console.log('Launching...');

// Alice deploys the contract
const ctcAlice = accAlice.contract(backend);
// Bob attaches to the contract
const ctcBob = accBob.contract(backend, ctcAlice.getInfo());

const Shared = (who) =>({
  showTime: (t) =>{
    console.log(`Time is ${t}`)
  },
  informTimeout: () =>{
    console.log(`${who} Observed a timeout`)
    process.exit(1); 
  },
  seeOutcome: (outcome) =>{
    console.log(`Outcome is ${outcome ? "Alice won" : "Bob won"}`)
  }
})

const choiceArray = ["I’m not here", "I’m still here”"]
const fmt = (x) => stdlib.formatCurrency(x, 4);
const getAccountBalance = async (who) => await stdlib.balanceOf(who)

console.log(`Starting account balance of Alice is ${await getAccountBalance(accAlice)}`)
console.log(`Starting account balance of Bob is ${await getAccountBalance(accBob)}`)


  const aliceChoice = await ask.ask(
    `Alice are you still here`,
    ask.yesno
  );

  const bobResponse = await ask.ask(
    `Bob do you accept the terms of the vault?`,
    ask.yesno
  )

  // Exit the program if bob rejects the terms
  if(!bobResponse){
    process.exit(0)
  }

console.log('Starting backends...');
await Promise.all([
  backend.Alice(ctcAlice, {
    // implement Alice's interact object here
    ...stdlib.hasRandom,
    ...Shared("Alice"),
    inheritance: stdlib.parseCurrency(5000),
    deadline: { ETH: 1, ALGO: 1, CFX: 1000 }[stdlib.connector],
    getChoice: () => {
    //  const choice = Math.floor(Math.random() * 2)
    //  console.log(`Alice choice is ${choiceArray[choice]}`)
      console.log(`Alice choice is ${aliceChoice ? "I'am still here" : "I'm not here"}`)
      return aliceChoice
    }
  }),
  backend.Bob(ctcBob, {
    // implement Bob's interact object here
    ...stdlib.hasRandom,
    ...Shared("Bob"),
    acceptTerms: (amt) =>{
      // console.log(`Bob accept the terms of the vault for  ${fmt(stdlib.parseCurrency(amt))}`)
      console.log(`Bob  ${bobResponse ? "accept" : "reject"} the terms of the vault for ${stdlib.parseCurrency(amt)}`)
      return bobResponse
    }
  }),
]);
const price = await ctcAlice.views.Main.amount();
  console.log(`The inheritance is ${price[0] == 'None' ? '0' : stdlib.parseCurrency(price[1])}.`);
  
//Third level implementation
const users = await stdlib.newTestAccounts(2, startingBalance);

const ctcWho = (whoi) =>  users[whoi].contract(backend, ctcAlice.getInfo());

const bob = async (whoi) => {
  const who = users[whoi];
  const ctc = ctcWho(whoi);
  console.log('Address of', stdlib.formatAddress(who));
  console.log(`Before account balance of ${who} is ${await getAccountBalance(ctc)}`)
  await ctc.apis.Bobs.acceptTerms(5000);  
    console.log(`After account balance of ${who} is ${await getAccountBalance(ctc)}`)
  }

await bob(0)
await bob(1)

console.log(`Alice account balance after is ${await getAccountBalance(accAlice)}`)
console.log(`Bob account balance after is ${await getAccountBalance(accBob)}`)
console.log('Goodbye, Alice and Bob!');
ask.done();