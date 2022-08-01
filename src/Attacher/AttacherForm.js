import React, { useState } from 'react'
import { Modal, Button, Form } from 'react-bootstrap'
import * as backend from '../build/index.main.mjs';

export default function AttacherForm(props){
  const [contractInfo, setContractInfo] = useState("")

  const handleAttach = async (ctcInfoStr) => {
    const ctcInfo = JSON.parse(ctcInfoStr);
    const ctc = this.props.acc.contract(backend, ctcInfo);
    this.setState({mode: 'Wait', ctc});
    await ctc.apis.Bobs.acceptTerms(1);
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
          Attach to the Contract
        </Modal.Title>
      </Modal.Header>
      <Modal.Body>
        <Form>
        <Form.Group className="mb-3" controlId="formBasicEmail">
          <Form.Label>Contract address or app Id</Form.Label>
          <Form.Control type="email" placeholder="Enter the contract address" required value={contractInfo} onChange={(e) => setContractInfo(e.currentTarget.value)} />
        </Form.Group>
      </Form>
      </Modal.Body>
      <Modal.Footer>
        <Button onClick={handleAttach}>Submit</Button>
      </Modal.Footer>
    </Modal>
    </div>
  )
}