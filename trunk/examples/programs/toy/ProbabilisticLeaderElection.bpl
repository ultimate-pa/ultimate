//#Safe
/*
 * Author: Matthias Heizmann
 * Date: 2020-04-09
 * 
 * Computer program that models the a probabilistic leader election in an
 * anonymous ring.
 * 
 * We have three processors that are arranged in a directed ring.
 * Each processor has a token. In each round a processor may pass
 * his token to the next processor (with probability 0.5) or keep the 
 * token (with probability 0.5).
 * If at the end of a round a processor has several tokens all but
 * one of the processor's tokens are removed. (In fact a processor
 * can have maximally two tokens in the case that its predecessor
 * did pass the token but it did keep the token.)
 * If there is only one token left in the ring then the processor
 * which has the token is the elected leader.
 * 
 * Question: How can we prove that the probability that a leader
 * is elected (and we do not always have two or more tokens)
 * converges towards one?
 * 
 * Preferrably, we would like to find a proof that works for
 * any number of processors and also for other probabilities
 * than 0.5 that was used here.
 * 
 * In this model, I have one real-valued variable for each
 * state. E.g., the variable pXTT represents the probability
 * that the ring is in a state where the first processor
 * does not have a token but the other processors do each
 * have a token.
 * 
 */

procedure main() returns () {
  var pXXT, pXTX, pXTT, pTXX, pTXT, pTTX, pTTT : real;
  // The variable d measures the distance between the probability
  // that a leader is elected to the probability one.
  // The variable dOld stores this probability for the last round.
  var d, dOld : real;
  pTTT := 1.0;
  pXXT := 0.0;
  pXTX := 0.0;
  pXTT := 0.0;
  pTXX := 0.0;
  pTXT := 0.0;
  pTTX := 0.0;
  d := 1.0 - pXXT - pXTX - pTXX;
  while(*)
  {
	  // Check that the sum of all probabilities is always one.
      assert pTTT + pXXT + pXTX + pXTT + pTXX + pTXT + pTTX == 1.0;
      pTTT,
	  pXXT,
	  pXTX,
	  pXTT,
	  pTXX,
	  pTXT,
	  pTTX
	  := 
	  (2.0/8.0) * pTTT, // pTTT
	  (1.0/2.0) * pXXT + (1.0/4.0) * pXTT + (1.0/2.0) * pXTX, // pXXT
	  (1.0/2.0) * pXTX + (1.0/4.0) * pTTX + (1.0/2.0) * pTXX, // pXTX
	  (1.0/4.0) * pXTT + (2.0/8.0) * pTTT + (1.0/4.0) * pTTX + (1.0/4.0) * pTXT, // pXTT
	  (1.0/2.0) * pTXX + (1.0/4.0) * pTXT + (1.0/2.0) * pXXT, // pTXX
	  (1.0/4.0) * pTXT + (2.0/8.0) * pTTT + (1.0/4.0) * pXTT + (1.0/4.0) * pTTX, // pTXT
	  (1.0/4.0) * pTTX + (2.0/8.0) * pTTT + (1.0/4.0) * pTXT + (1.0/4.0) * pXTT;// pTTX
	  dOld := d;
	  d := 1.0 - pXXT - pXTX - pTXX;
	  // Check that the distance is decreasing by a constant factor
	  // which would imply convergence.
	  assert dOld == 1.0 || d < dOld / 1.1;
  }
}


