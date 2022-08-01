import React, {useState, useEffect} from 'react'
import { StyleSheet, css } from 'aphrodite'
import { Container,Button } from 'react-bootstrap'
import { loadStdlib, ALGO_MyAlgoConnect as MyAlgoConnect } from '@reach-sh/stdlib'
import Attacher from '../Attacher'
import Deployer from '../Deployer/Deployer'
const stdlib = loadStdlib("ALGO")

stdlib.setWalletFallback(stdlib.walletFallback({
  providerEnv: 'TestNet', MyAlgoConnect }));


const styles = StyleSheet.create({
  wrapper: {
    background: "black",
    height: "100vh"
  },
  title: {
    color: "red",
  },
  header: {
    display: "flex",
    justifyContent: "space-between",
    paddingTop: "24px"
  },
  role: {
    position: "absolute",
    top: "50%",
    left: "45%",
  },
  roleButton: {
    display: "flex",
    justifyContent: "center"
  },
  btn: {
    margin: "8px"
  }
})

export default function Home(){

  const [showAttacherModal, setAttacherModal] = useState(false)
  const [walletAddress, setWalletAddress] = useState(null)
  const isConnected = !!walletAddress
  const [showDeployer, setDeployer] = useState(false)

  const connectWallet = async () =>{
    const acc = await stdlib.getDefaultAccount();
    console.log(acc.networkAccount.addr)
    setWalletAddress(acc.networkAccount.addr)
    localStorage.setItem("address", acc.networkAccount.addr)
  }

  const disconnectWallet = () =>{
    localStorage.clear("address")
    setWalletAddress(null)
  }

  const hideModal = () => setAttacherModal(false)

  useEffect(() =>{
    const value = localStorage.getItem("address")
    if(value){
      setWalletAddress(value)
    }
  }, [])

  return (
    <div className={css(styles.wrapper)}>
        <Container>
          <div className={css(styles.header)}>
            <h1 className={css(styles.title)}>Reach Vault</h1>
            <Button onClick={isConnected ? disconnectWallet : connectWallet}>{isConnected ? "Disconnect" : "Connect Wallet"}</Button>
          </div>

          <div className={css(styles.role)}>
            <h2>What is your role?</h2>
            <div className={css(styles.roleButton)}>
              <Button className={css(styles.btn)} onClick={() => setDeployer(true)}>Deployer</Button>
              <Button className={css(styles.btn)} onClick={() => setAttacherModal(true)}>Attacher</Button>
            </div>
          </div>
          <Attacher show={showAttacherModal} onHide={hideModal}/>
          <Deployer show={showDeployer} onHide={() => setDeployer(false)}/>
      </Container>
    </div>   
  )
}