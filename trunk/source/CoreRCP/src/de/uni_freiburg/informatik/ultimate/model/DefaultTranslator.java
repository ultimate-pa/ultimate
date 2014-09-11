package de.uni_freiburg.informatik.ultimate.model;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;

/**
 * Translator which just passes the input along, i.e., the mapping from input to
 * output is the identity. If types of source and target differ
 * ClassCastExceptions are thrown during the translation. <br>
 * Because {@link DefaultTranslator} is used for <b>back-translation</b>,
 * <i>Source</i> describes the output of a tool and <i>Target</i> the input of a
 * tool.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * @author dietsch@informatik.uni-freiburg.de
 * 
 * @param <STE>
 *            Source Trace Element. Type of trace elements (e.g., Statements,
 *            CodeBlocks, BoogieASTNodes) in the source program model.
 * @param <TTE>
 *            Target Trace Elment. Type of trace elements (e.g., Statements,
 *            CodeBlocks, BoogieASTNodes) in the target program model.
 * @param <SE>
 *            Source Expression. Type of expression in the source program model.
 * @param <TE>
 *            Target Expression. Type of expression in the target program model.
 */
public class DefaultTranslator<STE, TTE, SE, TE> implements ITranslator<STE, TTE, SE, TE> {

	private final Class<STE> mSourceTraceElementType;
	private final Class<TTE> mTargetTraceElementType;
	private final Class<SE> mSourceExpressionType;
	private final Class<TE> mTargetExpressionType;

	public DefaultTranslator(Class<STE> sourceTraceElementType, Class<TTE> targetTraceElementType,
			Class<SE> sourceExpressionType, Class<TE> targetExpressionType) {
		mSourceTraceElementType = sourceTraceElementType;
		mTargetTraceElementType = targetTraceElementType;
		mSourceExpressionType = sourceExpressionType;
		mTargetExpressionType = targetExpressionType;
		assert mTargetExpressionType != null;
		assert mTargetTraceElementType != null;
		assert mSourceExpressionType != null;
		assert mSourceTraceElementType != null;
	}

	@Override
	public Class<STE> getSourceTraceElementClass() {
		return mSourceTraceElementType;
	}

	@Override
	public Class<TTE> getTargetTraceElementClass() {
		return mTargetTraceElementType;
	}

	@Override
	public Class<SE> getSourceExpressionClass() {
		return mSourceExpressionType;
	}

	@Override
	public Class<TE> getTargetExpressionClass() {
		return mTargetExpressionType;
	}

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

	@Override
	public List<String> targetTraceToString(List<?> trace) {
		List<String> rtr = new ArrayList<>();
		for (Object elem : trace) {
			rtr.add(elem.toString());
		}
		return rtr;
	}

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

	@Override
	public String targetExpressionToString(Object expression) {
		return expression.toString();
	}

	@Override
	public IProgramExecution<TTE, TE> translateProgramExecution(IProgramExecution<STE, SE> programExecution) {
		IProgramExecution<TTE, TE> result = null;
		try {
			result = (IProgramExecution<TTE, TE>) programExecution;
			assert (consistsOfTargetTraceElements(programExecution));
		} catch (ClassCastException e) {
			String message = "Type of source trace element and type of target"
					+ " trace element are different. DefaultTranslator can"
					+ " only be applied to traces of same type.";
			throw new AssertionError(message);
		}
		return result;
	}

	/**
	 * Returns true if all elements of IProgramExecution are of type TTE, throws
	 * a ClassCastException otherwise.
	 */
	private boolean consistsOfTargetTraceElements(IProgramExecution<STE, SE> programExecution) {
		List<TTE> auxilliaryList = new ArrayList<TTE>(programExecution.getLength());
		for (int i = 0; i < programExecution.getLength(); i++) {
			auxilliaryList.add((TTE) programExecution.getTraceElement(i));
		}
		return true;
	}

	/**
	 * Returns true if all elements of trace are of type TTE, throws a
	 * ClassCastException otherwise.
	 */
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

	/**
	 * Translate an expression of an arbitrary type E to the target expression
	 * type of this ITranslator.
	 * 
	 * @param iTranslators
	 *            is a sequence of ITranslaters itrans_0,...,itrans_n such that
	 *            <ul>
	 *            <li>the target expression type of itrans_0 is the source
	 *            expression type of this ITranslator,
	 *            <li>for 0<i<n the source expression type of iTrans_i coincides
	 *            with the target expression type of iTrans_{i+1}, and
	 *            <li>the source expression type of itrans_n is E (the type of
	 *            the expression expr)
	 *            </ul>
	 */
	public static <STE, TTE, SE, TE> TE translateExpressionIteratively(SE expr, ITranslator<?, ?, ?, ?>... iTranslators) {
		TE result;

		if (iTranslators.length == 0) {
			result = (TE) expr;
		} else {
			ITranslator<STE, ?, SE, ?> last = (ITranslator<STE, ?, SE, ?>) iTranslators[iTranslators.length - 1];
			ITranslator<?, ?, ?, ?>[] allButLast = Arrays.copyOf(iTranslators, iTranslators.length - 1);
			Object expressionOfIntermediateType = last.translateExpression(expr);
			result = (TE) translateExpressionIteratively(expressionOfIntermediateType, allButLast);
		}
		return result;
	}

	public static <STE, TTE, SE, TE> List<TTE> translateTraceIteratively(List<STE> trace,
			ITranslator<?, ?, ?, ?>... iTranslators) {
		List<TTE> result;
		List<STE> traceOfSourceType;
		if (iTranslators.length == 0) {
			result = (List<TTE>) trace;
		} else {
			ITranslator<STE, ?, SE, ?> last = (ITranslator<STE, ?, SE, ?>) iTranslators[iTranslators.length - 1];
			ITranslator<?, ?, ?, ?>[] allButLast = Arrays.copyOf(iTranslators, iTranslators.length - 1);
			List<?> traceOfIntermediateType = last.translateTrace(trace);
			result = (List<TTE>) translateTraceIteratively(trace, allButLast);
		}
		return result;
	}

	public static <STE, TTE, SE, TE> IProgramExecution<TTE, TE> translateProgramExecutionIteratively(
			IProgramExecution<STE, SE> programExecution, ITranslator<?, ?, ?, ?>... iTranslators) {
		IProgramExecution<TTE, TE> result;
		IProgramExecution<STE, SE> programExecutionOfSourceType;
		if (iTranslators.length == 0) {
			result = (IProgramExecution<TTE, TE>) programExecution;
		} else {
			ITranslator<STE, ?, SE, ?> last = (ITranslator<STE, ?, SE, ?>) iTranslators[iTranslators.length - 1];
			ITranslator<?, ?, ?, ?>[] allButLast = Arrays.copyOf(iTranslators, iTranslators.length - 1);
			IProgramExecution<?, ?> peOfIntermediateType = last.translateProgramExecution(programExecution);
			result = (IProgramExecution<TTE, TE>) translateProgramExecutionIteratively(peOfIntermediateType, allButLast);
		}
		return result;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(getClass().getSimpleName());
		sb.append(" SourceExp=");
		sb.append(getSourceExpressionClass().getSimpleName());
		sb.append(" TargetExp=");
		sb.append(getTargetExpressionClass().getSimpleName());
		sb.append(" SourceTraceELement=");
		sb.append(getSourceTraceElementClass().getSimpleName());
		sb.append(" TargetTraceELement=");
		sb.append(getTargetTraceElementClass().getSimpleName());
		return sb.toString();
	}

}
