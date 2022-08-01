import React, { useState } from 'react'
import { Modal, Button, Form } from 'react-bootstrap'
import * as backend from '../build/index.main.mjs';
import { loadStdlib } from '@reach-sh/stdlib'
const stdlib = loadStdlib("ALGO")


export default function Deployer(props){
  const [showAttacher, setAttacher] = useState(false)
  const [amount, setAmount] = useState(0)
  const [contractInfo, setContractInfo] = useState("")
  const [showInfo, setInfo] = useState(false)

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

  const deployContract = async () =>{
    const acc = await stdlib.getDefaultAccount();
    const ctc = acc.contract(backend);
    try {
      await ctc.p.Alice({
            // implement Alice's interact object here
    ...stdlib.hasRandom,
    ...Shared("Alice"),
    inheritance: stdlib.parseCurrency(amount),
    deadline: stdlib.bigNumberify(5),
    getChoice: () => {
    //  const choice = Math.floor(Math.random() * 2)
    //  console.log(`Alice choice is ${choiceArray[choice]}`)
      // console.log(`Alice choice is ${aliceChoice ? "I'am still here" : "I'm not here"}`)
      return true
    }
      });
    } catch (e) {
      if ( e !== 42 ) {
        throw e;
      }
    }
    // const ctcInfoStr = JSON.stringify(await ctc.getInfo(), null, 2);
    // if(ctcInfoStr !== ""){
    //   setInfo(true)
    //   setContractInfo(ctcInfoStr)
    // }

    ctc.getInfo().then((info) => {
      setContractInfo(JSON.stringify(info))
      setInfo(true)
      console.log(`The contract is deployed as = ${JSON.stringify(info)}`); });
    
    // console.log(ctcInfoStr)
  }
  return(
    <div>
       <Modal
      {...props}
      size="lg"
      aria-labelledby="contained-modal-title-vcenter"
      centered
    >
      <Modal.Header closeButton>
        <Modal.Title id="contained-modal-title-vcenter">
          Deployer
        </Modal.Title>
      </Modal.Header>
      <Modal.Body>
        {showInfo ? <h3>The deployed contract info is {contractInfo}</h3> :
        <div>
          <p>
            Pays the contract the inheritance and deploys the contract
          </p>
            <Form>
            <Form.Group className="mb-3" controlId="formBasicEmail">
              <Form.Label>Inheritance to deposit to the contract</Form.Label>
              <Form.Control type="number" placeholder="Enter amount" required value={amount} onChange={(e) => setAmount(e.target.value)}/>
            </Form.Group>
            <Button onClick={deployContract}>Deploy</Button>
          </Form>
        </div>
        }   
      </Modal.Body>
      {/* <Modal.Footer>
        <Button onClick={deployContract}>Deploy</Button>
      </Modal.Footer> */}

    </Modal>
    </div>
  )
}