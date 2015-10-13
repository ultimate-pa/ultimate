/*
 * Copyright (C) 2015 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BoogieProcedureInliner plug-in.
 * 
 * The ULTIMATE BoogieProcedureInliner plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BoogieProcedureInliner plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogieProcedureInliner plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogieProcedureInliner plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BoogieProcedureInliner plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.backtranslation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.Activator;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.BackTransValue;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.InlineVersionTransformer;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.util.IToString;
import de.uni_freiburg.informatik.ultimate.model.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieProgramExecution;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.result.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.result.AtomicTraceElement.StepInfo;
import de.uni_freiburg.informatik.ultimate.result.GenericResult;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.result.IResultWithSeverity.Severity;

/**
 * Backtranslates an inlined boogie program.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class InlinerBacktranslator extends DefaultTranslator<BoogieASTNode, BoogieASTNode, Expression, Expression> {

	private IUltimateServiceProvider mServices;
	private Logger mLogger;

	/**
	 * Backtranslation mapping for statements, specifications (and expressions,
	 * for trace element step). If there is no mapping for a node, then it
	 * wasn't affected by the inlining process.
	 */
	private Map<BoogieASTNode, BackTransValue> mBackTransMap = new HashMap<>();

	private ExpressionBacktranslation mExprBackTrans = new ExpressionBacktranslation();

	public InlinerBacktranslator(IUltimateServiceProvider services) {
		super(BoogieASTNode.class, BoogieASTNode.class, Expression.class, Expression.class);
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	/**
	 * Updates the mapping, using an used InlineVersionTransformer.
	 * 
	 * @param transformer
	 *            InlinerVersionTransformer, which already transformed a
	 *            procedure.
	 */
	public void addBacktranslation(InlineVersionTransformer transformer) {
		mBackTransMap.putAll(transformer.getBacktranslationMap());
		mExprBackTrans.reverseAndAddMapping(transformer.getVariableMap());
	}

	// Does not need to preserve instances
	public Collection<Expression> translateExpressions(Collection<Expression> exprs) {
		Collection<Expression> translatedExprs = new ArrayList<>();
		for (Expression expr : exprs) {
			translatedExprs.add(translateExpression(expr));
		}
		return translatedExprs;
	}

	// Does not need to preserve instances
	@Override
	public Expression translateExpression(Expression expr) {
		return mExprBackTrans.processExpression(expr);
	}

	// Should preserve instances
	@Override
	public List<BoogieASTNode> translateTrace(List<BoogieASTNode> trace) {
		Set<CallStatement> knownCalls = new HashSet<>();
		List<BoogieASTNode> translatedTrace = new ArrayList<>();
		CallReinserter callReinserter = new CallReinserter();
		final IToString<BoogieASTNode> stringProvider = BoogiePrettyPrinter.getBoogieToStringProvider();
		for (BoogieASTNode traceElem : trace) {
			AtomicTraceElement<BoogieASTNode> atomicTraceElem;
			if (traceElem instanceof CallStatement) {
				CallStatement call = (CallStatement) traceElem;
				if (knownCalls.contains(call)) {
					reportUnfinishedBacktranslation("Cannot reconstruct StepInfo (either call or return): " + call);
				}
				knownCalls.add(call);
				atomicTraceElem = new AtomicTraceElement<BoogieASTNode>(call, call, StepInfo.PROC_CALL, stringProvider);
			} else {
				atomicTraceElem = new AtomicTraceElement<BoogieASTNode>(traceElem, stringProvider);
			}
			BackTransValue traceElemMapping = mBackTransMap.get(traceElem);
			List<AtomicTraceElement<BoogieASTNode>> recoveredCalls = callReinserter.recoverInlinedCallsBefore(
					atomicTraceElem, traceElemMapping);
			for (AtomicTraceElement<BoogieASTNode> insertedCall : recoveredCalls) {
				translatedTrace.add(insertedCall.getTraceElement());
			}
			if (traceElemMapping == null) {
				translatedTrace.add(traceElem);
			} else {
				BoogieASTNode originalNode = traceElemMapping.getOriginalNode();
				if (originalNode != null) {
					translatedTrace.add(originalNode);
				}
			}
		}
		return translatedTrace;
	}

	public IProgramExecution<BoogieASTNode, Expression> translateProgramExecution(
			IProgramExecution<BoogieASTNode, Expression> exec) {
		final int length = exec.getLength();
		final IToString<BoogieASTNode> stringProvider = BoogiePrettyPrinter.getBoogieToStringProvider();
		CallReinserter callReinserter = new CallReinserter();
		Map<Integer, ProgramState<Expression>> translatedStates = new HashMap<>();
		List<AtomicTraceElement<BoogieASTNode>> translatedTrace = new ArrayList<>();
		for (int i = 0; i < length; ++i) {
			AtomicTraceElement<BoogieASTNode> traceElem = exec.getTraceElement(i);
			BackTransValue traceElemMapping = mBackTransMap.get(traceElem.getTraceElement());
			translatedTrace.addAll(callReinserter.recoverInlinedCallsBefore(traceElem, traceElemMapping));
			if (traceElemMapping == null) {
				translatedTrace.add(traceElem); // traceElem wasn't affected by
												// inlining
			} else {
				BoogieASTNode translatedTraceElem = traceElemMapping.getOriginalNode();
				if (translatedTraceElem != null) {
					BackTransValue stepMapping = mBackTransMap.get(traceElem.getStep());
					BoogieASTNode translatedStep;
					if (stepMapping == null || stepMapping.getOriginalNode() == null) {
						translatedStep = translatedTraceElem;
					} else {
						translatedStep = stepMapping.getOriginalNode();
					}
					translatedTrace.add(new AtomicTraceElement<BoogieASTNode>(translatedTraceElem, translatedStep,
							traceElem.getStepInfo(), stringProvider));
				} else {
					continue; // discards the associated ProgramState (State
								// makes no sense, without Statement)
				}
			}
			ProgramState<Expression> progState = exec.getProgramState(i);
			if (progState != null) {
				Set<String> inlinedActiveProcs = callReinserter.unreturnedInlinedProcedures();
				Map<Expression, Collection<Expression>> translatedVar2Values = new HashMap<>();
				for (Expression variable : progState.getVariables()) {
					mExprBackTrans.setInlinedActiveProcedures(inlinedActiveProcs);
					Expression translatedVar = mExprBackTrans.processExpression(variable);
					if (mExprBackTrans.processedExprWasActive()) {
						translatedVar2Values.put(translatedVar, translateExpressions(progState.getValues(variable)));
					}
				}
				translatedStates.put(translatedTrace.size() - 1, new ProgramState<>(translatedVar2Values));
			}
		}
		BoogieProgramExecution translatedExec = new BoogieProgramExecution(translatedStates, translatedTrace);
		return translatedExec;
	}

	@Override
	public String targetExpressionToString(Expression expression) {
		return BoogiePrettyPrinter.print(expression);
	}

	@Override
	public List<String> targetTraceToString(List<BoogieASTNode> trace) {
		List<String> rtr = new ArrayList<>();
		for (BoogieASTNode node : trace) {
			if (node instanceof Statement) {
				rtr.add(BoogiePrettyPrinter.print((Statement) node));
			} else {
				return super.targetTraceToString(trace);
			}
		}
		return rtr;
	}

	private void reportUnfinishedBacktranslation(String message) {
		mLogger.warn(message);
		mServices.getResultService().reportResult(Activator.PLUGIN_ID,
				new GenericResult(Activator.PLUGIN_ID, "Unfinished Backtranslation", message, Severity.WARNING));
	}

}
