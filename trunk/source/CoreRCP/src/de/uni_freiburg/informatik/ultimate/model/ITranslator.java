package de.uni_freiburg.informatik.ultimate.model;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;

/**
 * Object translate traces and expressions from one format to another. In
 * ULTIMATE generator plugins may transform one program model into another. A
 * program analysis constructs results (e.g., traces or expressions) for some
 * program model, but a user wants to see the results for the initial program
 * model (e.g., C programming language). We use ITranslater objects for a
 * backtranslation of the program transformations that were done by plugins. <br>
 * Because {@link ITranslator} is used for <b>back-translation</b>,
 * <i>Source</i> describes the output of a tool and <i>Target</i> the input of a
 * tool.
 * 
 * @author heizmann@informatik.uni-freiburg.de,
 * @author dietsch@informatik.uni-freiburg.de
 * 
 * @param <STE>
 *            Source Trace Element. Type of trace elements (e.g., Statements,
 *            CodeBlocks, BoogieASTNodes) in the source program model.
 * @param <TTE>
 *            Target Trace Element. Type of trace elements (e.g., Statements,
 *            CodeBlocks, BoogieASTNodes) in the target program model.
 * @param <SE>
 *            Source Expression. Type of expression in the source program model.
 * @param <TE>
 *            Target Expression. Type of expression in the target program model.
 */
public interface ITranslator<STE, TTE, SE, TE> {

	public TE translateExpression(SE expression);

	public String targetExpressionToString(TE expression);

	/**
	 * Translate trace that is represented as a list of Source Trace Elements
	 * (resp. list of Target Trace Elements).
	 */
	public List<TTE> translateTrace(List<STE> trace);

	public List<String> targetTraceToString(List<TTE> trace);

	public IProgramExecution<TTE, TE> translateProgramExecution(IProgramExecution<STE, SE> programExecution);

	public Class<STE> getSourceTraceElementClass();

	public Class<TTE> getTargetTraceElementClass();

	public Class<SE> getSourceExpressionClass();

	public Class<TE> getTargetExpressionClass();
}
