package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.backtranslation;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.Activator;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.BackTransValue;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.InlineVersionTransformer;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieProgramExecution;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.result.GenericResult;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.result.IResultWithSeverity.Severity;

/**
 * Backtranslates an inlined boogie program.
 * 
 * Still a work in progress, therefore no final comments.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class InlinerBacktranslator extends DefaultTranslator<BoogieASTNode, BoogieASTNode, Expression, Expression> {

	private IUltimateServiceProvider mServices;
	private Logger mLogger;
	
	/**
	 * ...
	 * If there is no mapping for a node, then it wasn't affected by the inlining process.
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
	 * @param transformer InlinerVersionTransformer, which already transformed a procedure.
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
		throw new UnsupportedOperationException();
//		List<BoogieASTNode> translatedTrace = new ArrayList<>();
//		CallReinserter callReinserter = new CallReinserter();
//		for (BoogieASTNode traceElem : trace) {
//			BackTransValue mapping = mBackTransMap.get(traceElem);
//			for (AtomicTraceElement<BoogieASTNode> insertedCall : callReinserter.recoverInlinedCallsBefore(mapping)) {
//				translatedTrace.add(insertedCall.getTraceElement());
//			}
//			if (mapping == null) {
//				translatedTrace.add(traceElem);
//			} else {
//				BoogieASTNode originalNode = mapping.getOriginalNode();
//				if (originalNode != null) {
//					translatedTrace.add(originalNode);
//				}
//			}
//		}
//		return translatedTrace;
	}

	public IProgramExecution<BoogieASTNode, Expression> translateProgramExecution(
			IProgramExecution<BoogieASTNode, Expression> exec) {
		final int length = exec.getLength();
		CallReinserter callReinserter = new CallReinserter();
		Map<Integer, ProgramState<Expression>> translatedStates = new HashMap<>();
		List<AtomicTraceElement<BoogieASTNode>> translatedTrace = new ArrayList<>();
		for (int i = 0; i < length; ++i) {
			AtomicTraceElement<BoogieASTNode> traceElem = exec.getTraceElement(i);
			BackTransValue mapping = mBackTransMap.get(traceElem.getTraceElement());
			translatedTrace.addAll(callReinserter.recoverInlinedCallsBefore(traceElem, mapping));
			if (mapping == null) {
				translatedTrace.add(traceElem); // traceElem wasn't affected by inlining
			} else {
				BoogieASTNode originalNode = mapping.getOriginalNode();
				if (originalNode != null) {
					BoogieASTNode translatedStep = originalNode; //TODO translate step! traceElem.getStep()
					translatedTrace.add(new AtomicTraceElement<BoogieASTNode>(originalNode, translatedStep, traceElem.getStepInfo()));
				} else {
					continue; // discards the associated ProgramState (State makes no sense, without Statement)
				}
			}
			ProgramState<Expression> progState = exec.getProgramState(i);
			if (progState != null) {
				Map<Expression, Collection<Expression>> translatedVar2Values = new HashMap<>();
				for (Expression variable : progState.getVariables()) {
					Expression translatedVar = translateExpression(variable);
					if (keepVariable(translatedVar, null /*<-- replace*/)) { // TODO
						translatedVar2Values.put(translatedVar, translateExpressions(progState.getValues(variable)));						
					}
				}
				translatedStates.put(translatedTrace.size()-1, new ProgramState<>(translatedVar2Values));
			}
		}
		BoogieProgramExecution translatedExec =  new BoogieProgramExecution(translatedStates, translatedTrace);
		return translatedExec;
	}	
	
	private boolean keepVariable(Expression translatedVar, String curProcId) {
		// TODO implement
		return true;
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
