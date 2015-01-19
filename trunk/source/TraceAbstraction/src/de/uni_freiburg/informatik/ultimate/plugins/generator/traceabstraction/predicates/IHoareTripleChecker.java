package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Object that implement this interface check if Hoare Triples are valid.
 * Hoare triples that we check are of the form
 * { P } cb { Q }
 * where P and Q are given by IPredicates, cb has to be a single CodeBlock.
 * Note that for return statements we have to check a quadruple                                                              
 * @author Matthias Heizmann
 *
 */
public interface IHoareTripleChecker {
	
	/**
	 * Hoare Triple Truth Value. This is the result of a Hoare triple check.
	 */
	public enum HTTV { VALID, INVALID, UNKNOWN, NOT_CHECKED };
	
	
	/**
	 * Check if the Hoare triple 
	 *     {pre} cb {succ}
	 * is valid for an internal transition cb. Internal transition means that
	 * the program is in the same procedure before and after the CodeBlock cb
	 * was executed.
	 */
	public HTTV checkInternal(IPredicate pre, CodeBlock cb, IPredicate succ);
	
	/**
	 * Check if the Hoare triple 
	 *     {pre} call {succ}
	 * is valid for a call transition. Here, the CodeBlock has to be a call 
	 * statement.
	 */
	public HTTV checkCall(IPredicate pre, CodeBlock cb, IPredicate succ);
	
	/**
	 * Check if the Hoare quadruple 
	 *     {preLin} {preHier} return {succ}
	 * is valid for a return transition. Here, the CodeBlock has to be a return,
	 * preLin is the IPredicate that describes a set of states of the called
	 * procedure before the return, preHier is the IPredicate that describes
	 * a set of states of the calling procedure before the call, and succ
	 * is the IPredicate that describes a set of states of the called procedure.
	 */
	public HTTV checkReturn(IPredicate preLin, IPredicate preHier, CodeBlock cb, IPredicate succ); 


	
	
	

}
