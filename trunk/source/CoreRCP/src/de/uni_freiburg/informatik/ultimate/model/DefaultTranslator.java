package de.uni_freiburg.informatik.ultimate.model;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;


/**
 * Translator which just passes the input along, i.e., the mapping from input
 * to output is the identity. If types of source and target differ 
 * ClassCastExceptions are thrown during the translation. 
 * 
 * @author heizmann@informatik.uni-freiburg.de.
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
public class DefaultTranslator<STE, TTE, SE, TE> 
									implements ITranslator<STE, TTE, SE, TE> {

	@SuppressWarnings("unchecked")
	@Override
	public List<TTE> translateTrace(List<STE> trace) {
		List<TTE> result = null;
		try {
			result = (List<TTE>) trace;
			assert (consistsOfTargetTraceElements(trace));
		} catch (ClassCastException e) {
			String message = "Type of source trace element and type of target" 
					+ " trace element are different. DefaultTranslator can"
					+ " only be applied to traces of same type.";
			throw new AssertionError(message);
		}
		return result;
	}

	@SuppressWarnings("unchecked")
	@Override
	public TE translateExpression(SE expression) {
		TE result;
		try {
			result = (TE) expression;
		} catch (ClassCastException e) {
			String message = "Type of SourceExpression and type of"
					+ " TargetExpression are different. DefaultTranslator can"
					+ " only be applied to expression of same type.";
			throw new AssertionError(message);
		}
		return result;
	}
	
	/**
	 * Returns true if all elements of trace are of type TTE, throws a
	 * ClassCastException otherwise.
	 */
	@SuppressWarnings("unchecked")
	private boolean consistsOfTargetTraceElements(List<STE> trace) {
		List<TTE> auxilliaryList = new ArrayList<TTE>(trace.size());
		for (STE ste : trace) {
			try {
				auxilliaryList.add((TTE) ste);
			} catch (ClassCastException e) {
				return false;
			}
		}
		return true;
	}

	@SuppressWarnings("unchecked")
	@Override
	public <E> TE translateExpressionIteratively(E expr,
			ITranslator<?, ?, ?, ?>... iTranslators) {
		TE result;
		SE expressionOfSourceType;
		if (iTranslators.length == 0) {
			expressionOfSourceType = (SE) expr;
		} else {
			ITranslator<?, ?, E, ?> last = 
					(ITranslator<?, ?, E, ?>) iTranslators[iTranslators.length-1];
			ITranslator<?, ?, ?, ?>[] allButLast = 
					Arrays.copyOf(iTranslators, iTranslators.length-1);
			expressionOfSourceType = (SE) last.translateExpressionIteratively(expr, allButLast);
		}
		result = translateExpression(expressionOfSourceType);
		return result;
	}
	
	public IProgramExecution<TTE, TE> translateProgramExecution(
			IProgramExecution<STE, SE> programExecution) {
		return (IProgramExecution<TTE, TE>) programExecution;
	}

	public IProgramExecution<TTE, TE> translateProgramExecutionIteratively(
			IProgramExecution<STE, SE> programExecution, ITranslator<?,?,?,?>...iTranslators) {
		IProgramExecution<TTE, TE> result;
		IProgramExecution<STE, SE> programExecutionOfSourceType;
		if (iTranslators.length == 0) {
			programExecutionOfSourceType = (IProgramExecution<STE, SE>) programExecution;
		} else {
			ITranslator<?, ?, TE, TTE> last = 
					(ITranslator<?, ?, TE, TTE>) iTranslators[iTranslators.length-1];
			ITranslator<?, ?, ?, ?>[] allButLast = 
					Arrays.copyOf(iTranslators, iTranslators.length-1);
			programExecutionOfSourceType = (IProgramExecution<STE, SE>) 
					last.translateExpressionIteratively(programExecution, allButLast);
		}
		result = translateProgramExecution(programExecutionOfSourceType);
		return result;
	}

}
