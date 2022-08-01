import React, { useState } from 'react'
import { Modal, Button } from 'react-bootstrap'
import AttacherForm from './AttacherForm'

export default function Attacher(props){
  const [showAttacher, setAttacher] = useState(false)

  const handleOpenAttacherForm = () =>{
    setAttacher(true)
    props.onHide()
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
          Vault
        </Modal.Title>
      </Modal.Header>
      <Modal.Body>
        <p>
          Do you accept terms to the vault of 5,000 Algos
        </p>
      </Modal.Body>
      <Modal.Footer>
        <Button onClick={handleOpenAttacherForm}>Yes</Button>
        <Button onClick={props.onHide}>No</Button>
      </Modal.Footer>
    </Modal>
    <AttacherForm show={showAttacher} onHide={() => setAttacher(false)}/>
    </div>
  )
}