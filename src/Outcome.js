import { Modal, Button } from 'react-bootstrap'

export default function Outcome(props){
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
          <p>
            The outcome of the vault is that Attacher won
          </p>
        </Modal.Body>
        <Modal.Footer>
          <Button onClick={props.onHide}>Close</Button>
        </Modal.Footer>
        <p>Message</p>
      </Modal>
    </div>
  )
}