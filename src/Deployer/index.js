import { Form, Modal,  Button } from "react-bootstrap"

export default function DeployerResponse(props){
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
      <h2>Deployer</h2>
        <h3>Are you still here?</h3>
          <Form>
            {['radio'].map((type) => (
              <div key={`inline-${type}`} className="mb-3">
                <Form.Check
                  inline
                  label="Yes"
                  name="group1"
                  type={type}
                  id={`inline-${type}-1`}
                />
                <Form.Check
                  inline
                  label="No"
                  name="group1"
                  type={type}
                  id={`inline-${type}-2`}
                />
              </div>
            ))}
          </Form>
      </Modal.Body>
      <Modal.Footer>
        <Button onClick={props.onHide}>Close</Button>
      </Modal.Footer>
      </Modal>    
    </div>
  )
}