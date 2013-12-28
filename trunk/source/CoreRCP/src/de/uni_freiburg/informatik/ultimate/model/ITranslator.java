package de.uni_freiburg.informatik.ultimate.model;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;

/**
 * Object translate traces and expressions from one format to another.
 * In ULTIMATE generator plugins may transform one program model into another.
 * A program analysis constructs results (e.g., traces or expressions) for some 
 * program model, but a user wants to see the results for the initial program 
 * model (e.g., C programming language).
 * We use ITranslater objects for a backtranslation of the program 
 * transformations that were done by plugins. 
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <STE> Source Trace Element. Type of trace elements (e.g., Statements,
 *  CodeBlocks, AstNodes) in the source program model.
 * @param <TTE> Target Trace Elment. Type of trace elements (e.g., Statements,
 *  CodeBlocks, AstNodes) in the target program model.
 * @param <SE> Source Expression. Type of expression in the source program 
 * 	model.
 * @param <TE> Target Expression. Type of expression in the target program 
 * 	model.
 */
public interface ITranslator<STE, TTE, SE, TE> {
	
	public TE translateExpression(SE expression);
	
	/**
	 * Translate trace that is represented as a list of Source Trace Elements
	 * (resp. list of Target Trace Elements).
	 */
	public List<TTE> translateTrace(List<STE> trace);
	

	public IProgramExecution<TTE, TE> translateProgramExecution(
			IProgramExecution<STE, SE> programExecution);

	
	
	/**
	 * Translate an expression of an arbitrary type E to the target expression 
	 * type of this ITranslator.
	 * @param iTranslators is a sequence of ITranslaters itrans_0,...,itrans_n
	 * such that
	 * <ul> 
	 * <li> the target expression type of itrans_0 is the source expression type of
	 * this ITranslator,  
	 * <li> for 0<i<n the source expression type of iTrans_i coincides
	 * with the target expression type of iTrans_{i+1}, and 
	 * <li> the source expression type of itrans_n is E (the type of the 
	 * expression expr)
	 * </ul>  
	 */
	public <E> TE translateExpressionIteratively(E expr, ITranslator<?,?,?,?>...iTranslators);
	
	public List<TTE> translateTraceIteratively(List<STE> trace, ITranslator<?,?,?,?>...iTranslators);
	
	public IProgramExecution<TTE, TE> translateProgramExecutionIteratively(
			IProgramExecution<STE, SE> programExecution, ITranslator<?,?,?,?>...iTranslators);

	
	
	


}
