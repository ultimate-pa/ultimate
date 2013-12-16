package de.uni_freiburg.informatik.ultimate.automata;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;


/**
 * Interface for operations for automata.
 * If possible,
 * <ul>
 *  <li> each operation is defined in its own class
 *  <li> for every application of the operation a new instance of this class is
 *      constructed
 *  <li> the result is returned via the getResult() method
 *  <li> start and end of the operation are reported to the logger using log
 *   level info
 *  <li> correctness checks for this operation are implemented in the
 *  checkResult method. Whoever executes this operation should add an
 *  assert checkResult()
 *  in his code.
 * </ul>
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public interface IOperation<LETTER,STATE> {
	
	/**
	 * Name of the operation..
	 * This name should also be used in the test grammar. 
	 */
	String operationName();
	
	/**
	 * Message that should be logged when the operation is stated.
	 * Use some information like: "starting operation intersection. First
	 * operand has 2394 states, second operand has 9374 states" 
	 */
	String startMessage();
	
	/**
	 * Message that should be logged when the operation is finished.
	 * Use some information like: "finished operation intersection result has
	 * 345 states"
	 */
	String exitMessage();
	
	/**
	 * Return the result of the operation. 
	 * @throws OperationCanceledException 
	 */
	Object getResult() throws OperationCanceledException;
	
	
	/**
	 * Run some checks to test correctness of the result. If therefore new
	 * automata have to be build use stateFactory.
	 * @return true iff all tests succeeded.
	 * @throws AutomataLibraryException 
	 */
	boolean checkResult(StateFactory<STATE> stateFactory) 
			throws AutomataLibraryException;

}
