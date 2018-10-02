/*
 * Copyright (C) 2012-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.lib.translation;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.models.Multigraph;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.core.model.models.IMultigraphEdge;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.StepInfo;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslatedCFG;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.core.model.translation.ITranslator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Translator which just passes the input along, i.e., the mapping from input to output is the identity. If types of
 * source and target differ ClassCastExceptions are thrown during the translation. <br>
 * Because {@link DefaultTranslator} is used for <b>back-translation</b>, <i>Source</i> describes the output of a tool
 * and <i>Target</i> the input of a tool.
 *
 * @author heizmann@informatik.uni-freiburg.de
 * @author dietsch@informatik.uni-freiburg.de
 *
 * @param <STE>
 *            Source Trace Element. Type of trace elements (e.g., Statements, CodeBlocks, BoogieASTNodes) in the source
 *            program model.
 * @param <TTE>
 *            Target Trace Elment. Type of trace elements (e.g., Statements, CodeBlocks, BoogieASTNodes) in the target
 *            program model.
 * @param <SE>
 *            Source Expression. Type of expression in the source program model.
 * @param <TE>
 *            Target Expression. Type of expression in the target program model.
 * @param <SVL>
 *            Source vertex label. Type of the vertex label of a {@link IBacktranslatedCFG} in the source program model.
 * @param <TVL>
 *            Target vertex label. Type of the vertex label of a {@link IBacktranslatedCFG} in the target program model.
 */
public class DefaultTranslator<STE, TTE, SE, TE, SVL, TVL> implements ITranslator<STE, TTE, SE, TE, SVL, TVL> {

	private final Class<? extends STE> mSourceTraceElementType;
	private final Class<? extends TTE> mTargetTraceElementType;
	private final Class<SE> mSourceExpressionType;
	private final Class<TE> mTargetExpressionType;

	public DefaultTranslator(final Class<? extends STE> sourceTraceElementType,
			final Class<? extends TTE> targetTraceElementType, final Class<SE> sourceExpressionType,
			final Class<TE> targetExpressionType) {
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
	public Class<? extends STE> getSourceTraceElementClass() {
		return mSourceTraceElementType;
	}

	@Override
	public Class<? extends TTE> getTargetTraceElementClass() {
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

	@SuppressWarnings("unchecked")
	@Override
	public List<TTE> translateTrace(final List<STE> trace) {
		List<TTE> result = null;
		try {
			result = (List<TTE>) trace;
			assert consistsOfTargetTraceElements(trace);
		} catch (final ClassCastException e) {
			final String message = "Type of source trace element and type of target"
					+ " trace element are different. DefaultTranslator can"
					+ " only be applied to traces of same type.";
			throw new AssertionError(message);
		}
		return result;
	}

	@Override
	public List<String> targetTraceToString(final List<TTE> trace) {
		final List<String> rtr = new ArrayList<>();
		for (final Object elem : trace) {
			rtr.add(elem.toString());
		}
		return rtr;
	}

	@SuppressWarnings("unchecked")
	@Override
	public TE translateExpression(final SE expression) {
		TE result;
		try {
			result = (TE) expression;
		} catch (final ClassCastException e) {
			final String message =
					"Type of SourceExpression and type of" + " TargetExpression are different. DefaultTranslator can"
							+ " only be applied to expression of same type.";
			throw new AssertionError(message);
		}
		return result;
	}

	@Override
	public String targetExpressionToString(final TE expression) {
		if (expression == null) {
			return "NULL";
		}
		return expression.toString();
	}

	@SuppressWarnings("unchecked")
	@Override
	public IProgramExecution<TTE, TE> translateProgramExecution(final IProgramExecution<STE, SE> programExecution) {
		try {
			final IProgramExecution<TTE, TE> result = (IProgramExecution<TTE, TE>) programExecution;
			assert consistsOfTargetTraceElements(programExecution);
			return result;
		} catch (final ClassCastException e) {
			final String message = "Type of source trace element and type of target"
					+ " trace element are different. DefaultTranslator can"
					+ " only be applied to traces of same type.";
			throw new AssertionError(message);
		}
	}

	@SuppressWarnings("unchecked")
	@Override
	public IBacktranslatedCFG<TVL, TTE> translateCFG(final IBacktranslatedCFG<SVL, STE> cfg) {
		try {
			return (IBacktranslatedCFG<TVL, TTE>) cfg;
		} catch (final ClassCastException e) {
			final String message = "Type of source trace element and type of target"
					+ " trace element are different. DefaultTranslator can only be applied to the same type.";
			throw new AssertionError(message);
		}
	}

	/**
	 * Returns true if all elements of IProgramExecution are of type TTE, throws a ClassCastException otherwise.
	 */
	@SuppressWarnings("unchecked")
	private boolean consistsOfTargetTraceElements(final IProgramExecution<STE, SE> programExecution) {
		final List<TTE> auxilliaryList = new ArrayList<>(programExecution.getLength());
		for (int i = 0; i < programExecution.getLength(); i++) {
			auxilliaryList.add((TTE) programExecution.getTraceElement(i));
		}
		return true;
	}

	/**
	 * Returns true if all elements of trace are of type TTE, throws a ClassCastException otherwise.
	 */
	@SuppressWarnings("unchecked")
	private boolean consistsOfTargetTraceElements(final List<STE> trace) {
		final List<TTE> auxilliaryList = new ArrayList<>(trace.size());
		for (final STE ste : trace) {
			try {
				auxilliaryList.add((TTE) ste);
			} catch (final ClassCastException e) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Translate an expression of an arbitrary type E to the target expression type of this ITranslator.
	 *
	 * @param iTranslators
	 *            is a sequence of ITranslaters itrans_0,...,itrans_n such that
	 *            <ul>
	 *            <li>the target expression type of itrans_0 is the source expression type of this ITranslator,
	 *            <li>for 0<i<n the source expression type of iTrans_i coincides with the target expression type of
	 *            iTrans_{i+1}, and
	 *            <li>the source expression type of itrans_n is E (the type of the expression expr)
	 *            </ul>
	 */
	@SuppressWarnings("unchecked")
	public static <STE, TTE, SE, TE, SVL, TVL> TE translateExpressionIteratively(final SE expr,
			final ITranslator<?, ?, ?, ?, ?, ?>... iTranslators) {
		TE result;

		if (iTranslators.length == 0) {
			result = (TE) expr;
		} else {
			final ITranslator<STE, ?, SE, ?, SVL, ?> last =
					(ITranslator<STE, ?, SE, ?, SVL, ?>) iTranslators[iTranslators.length - 1];
			final ITranslator<?, ?, ?, ?, ?, ?>[] allButLast = Arrays.copyOf(iTranslators, iTranslators.length - 1);
			final Object expressionOfIntermediateType = last.translateExpression(expr);
			result = (TE) translateExpressionIteratively(expressionOfIntermediateType, allButLast);
		}
		return result;
	}

	@SuppressWarnings("unchecked")
	public static <STE, TTE, SE, TE, SVL, TVL> List<TTE> translateTraceIteratively(final List<STE> trace,
			final ITranslator<?, ?, ?, ?, ?, ?>... iTranslators) {
		List<TTE> result;
		if (iTranslators.length == 0) {
			result = (List<TTE>) trace;
		} else {
			final ITranslator<?, ?, ?, ?, ?, ?>[] allButLast = Arrays.copyOf(iTranslators, iTranslators.length - 1);
			result = (List<TTE>) translateTraceIteratively(trace, allButLast);
		}
		return result;
	}

	@SuppressWarnings("unchecked")
	public static <STE, TTE, SE, TE, SVL, TVL> IProgramExecution<TTE, TE> translateProgramExecutionIteratively(
			final IProgramExecution<STE, SE> programExecution, final ITranslator<?, ?, ?, ?, ?, ?>... iTranslators) {
		final IProgramExecution<TTE, TE> result;
		if (iTranslators.length == 0) {
			result = (IProgramExecution<TTE, TE>) programExecution;
		} else {
			final ITranslator<STE, ?, SE, ?, SVL, ?> last =
					(ITranslator<STE, ?, SE, ?, SVL, ?>) iTranslators[iTranslators.length - 1];
			final ITranslator<?, ?, ?, ?, ?, ?>[] allButLast = Arrays.copyOf(iTranslators, iTranslators.length - 1);
			final IProgramExecution<?, ?> peOfIntermediateType = last.translateProgramExecution(programExecution);
			result = (IProgramExecution<TTE, TE>) translateProgramExecutionIteratively(peOfIntermediateType,
					allButLast);
		}
		return result;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(getClass().getSimpleName());
		sb.append(" SE=");
		sb.append(getSourceExpressionClass().getName());
		sb.append(" TE=");
		sb.append(getTargetExpressionClass().getName());
		sb.append(" STE=");
		sb.append(getSourceTraceElementClass().getName());
		sb.append(" TTE=");
		sb.append(getTargetTraceElementClass().getName());
		return sb.toString();
	}

	protected IBacktranslatedCFG<TVL, TTE> translateCFG(final IBacktranslatedCFG<SVL, STE> cfg,
			final IFunction<Map<IExplicitEdgesMultigraph<?, ?, SVL, ? extends STE, ?>, Multigraph<TVL, TTE>>, IMultigraphEdge<?, ?, SVL, STE, ?>, Multigraph<TVL, TTE>, Multigraph<TVL, TTE>> funTranslateEdge,
			final IFunction<String, List<Multigraph<TVL, TTE>>, Class<? extends TTE>, IBacktranslatedCFG<TVL, TTE>> funCreateBCFG) {

		final List<IExplicitEdgesMultigraph<?, ?, SVL, STE, ?>> oldRoots = cfg.getCFGs();
		final List<Multigraph<TVL, TTE>> newRoots = new ArrayList<>();

		for (final IExplicitEdgesMultigraph<?, ?, SVL, STE, ?> oldRoot : oldRoots) {
			final Multigraph<TVL, TTE> newRoot = createUnlabeledWitnessNode(oldRoot);
			final Map<IExplicitEdgesMultigraph<?, ?, SVL, ? extends STE, ?>, Multigraph<TVL, TTE>> nodeCache =
					new HashMap<>();
			final Deque<Pair<IExplicitEdgesMultigraph<?, ?, SVL, STE, ?>, Multigraph<TVL, TTE>>> worklist =
					new ArrayDeque<>();
			final Set<IExplicitEdgesMultigraph<?, ?, SVL, STE, ?>> closed = new HashSet<>();

			newRoots.add(newRoot);
			nodeCache.put(oldRoot, newRoot);
			worklist.add(new Pair<>(oldRoot, newRoot));

			while (!worklist.isEmpty()) {
				final Pair<IExplicitEdgesMultigraph<?, ?, SVL, STE, ?>, Multigraph<TVL, TTE>> current =
						worklist.remove();
				final IExplicitEdgesMultigraph<?, ?, SVL, STE, ?> oldSourceNode = current.getFirst();
				final Multigraph<TVL, TTE> newSourceNode = current.getSecond();
				if (!closed.add(oldSourceNode)) {
					continue;
				}

				for (final IMultigraphEdge<?, ?, SVL, STE, ?> edge : oldSourceNode.getOutgoingEdges()) {
					final Multigraph<TVL, TTE> newTargetNode = funTranslateEdge.create(nodeCache, edge, newSourceNode);
					if (newTargetNode != null) {
						worklist.add(new Pair<>(edge.getTarget(), newTargetNode));
					}
				}

			}
		}
		return funCreateBCFG.create(cfg.getFilename(), newRoots, mTargetTraceElementType);
	}

	/**
	 * Helper function for backtranslation of CFG. Just supply the CFG and a function that translates edges.
	 *
	 * @param cfg
	 *            The CFG that should be backtranslated.
	 * @param funTranslateEdge
	 *            A function f: (nodecache X old edge X new source node) -> new target node of the edge. This function
	 *            should translate the old edge, use the new source node as source node of the resulting subgraph, and
	 *            return one node as the target node of the new graph. The nodecache should be used to prevent the
	 *            unrolling of the graph.
	 * @return A backtranslated CFG.
	 */
	protected IBacktranslatedCFG<TVL, TTE> translateCFG(final IBacktranslatedCFG<SVL, STE> cfg,
			final IFunction<Map<IExplicitEdgesMultigraph<?, ?, SVL, ? extends STE, ?>, Multigraph<TVL, TTE>>, IMultigraphEdge<?, ?, SVL, STE, ?>, Multigraph<TVL, TTE>, Multigraph<TVL, TTE>> funTranslateEdge) {
		return translateCFG(cfg, funTranslateEdge, (a, b, c) -> new BacktranslatedCFG<>(a, b, c));
	}

	protected <VL> Multigraph<VL, TTE> createLabeledWitnessNode(final IExplicitEdgesMultigraph<?, ?, VL, STE, ?> old) {
		final Multigraph<VL, TTE> rtr = new Multigraph<>(old.getLabel());
		ModelUtils.copyAnnotations(old, rtr);
		return rtr;
	}

	protected <VL> Multigraph<VL, TTE> createUnlabeledWitnessNode(final IElement old) {
		final Multigraph<VL, TTE> rtr = new Multigraph<>(null);
		ModelUtils.copyAnnotations(old, rtr);
		return rtr;
	}

	protected void printCFG(final IBacktranslatedCFG<?, ?> cfg, final Consumer<String> printer) {
		for (final IExplicitEdgesMultigraph<?, ?, ?, ?, ?> root : cfg.getCFGs()) {
			final Deque<IExplicitEdgesMultigraph<?, ?, ?, ?, ?>> worklist = new ArrayDeque<>();
			final Set<IExplicitEdgesMultigraph<?, ?, ?, ?, ?>> closed = new HashSet<>();
			worklist.add(root);

			while (!worklist.isEmpty()) {
				final IExplicitEdgesMultigraph<?, ?, ?, ?, ?> current = worklist.remove();
				if (!closed.add(current)) {
					continue;
				}
				printer.accept(current.toString());
				for (final IMultigraphEdge<?, ?, ?, ?, ?> out : current.getOutgoingEdges()) {
					printer.accept("  --" + out + "--> " + out.getTarget());
					worklist.add(out.getTarget());
				}
			}
		}
	}

	protected void printHondas(final IBacktranslatedCFG<?, ?> cfg, final Consumer<String> printer) {
		for (final IExplicitEdgesMultigraph<?, ?, ?, ?, ?> graph : cfg.getCFGs()) {
			final Set<?> set = getHondas(graph);
			if (set.isEmpty()) {
				printer.accept("No Hondas");
			}
			for (final Object entry : set) {
				printer.accept("Honda: " + entry);
			}
		}
	}

	protected <VL, EL> Set<VL> getHondas(final IExplicitEdgesMultigraph<?, ?, VL, EL, ?> root) {
		final Deque<IExplicitEdgesMultigraph<?, ?, VL, EL, ?>> worklist = new ArrayDeque<>();
		final Set<IExplicitEdgesMultigraph<?, ?, VL, EL, ?>> closed = new HashSet<>();
		final Set<IExplicitEdgesMultigraph<?, ?, VL, EL, ?>> hondas = new HashSet<>();
		worklist.add(root);

		while (!worklist.isEmpty()) {
			final IExplicitEdgesMultigraph<?, ?, VL, EL, ?> current = worklist.remove();
			if (!closed.add(current)) {
				hondas.add(current);
				continue;
			}
			for (final IMultigraphEdge<?, ?, VL, EL, ?> out : current.getOutgoingEdges()) {
				worklist.add(out.getTarget());
			}
		}
		return hondas.stream().map(a -> a.getLabel()).collect(Collectors.toSet());
	}

	/**
	 * Check if source trace element and target trace element of a translation have the same procedure labels.
	 */
	protected boolean checkProcedureNames(final AtomicTraceElement<STE> ate, final AtomicTraceElement<TTE> newAte) {
		return ate.getSucceedingProcedure() == newAte.getSucceedingProcedure()
				&& ate.getPrecedingProcedure() == newAte.getPrecedingProcedure();
	}

	/**
	 * Check if the call stack of the source program execution is correct (according to procedure labels and step
	 * infos).
	 */
	protected boolean checkCallStackSourceProgramExecution(final ILogger logger,
			final IProgramExecution<STE, SE> sourceProgramExecution) {
		final List<AtomicTraceElement<STE>> rtr = new ArrayList<>();
		sourceProgramExecution.iterator().forEachRemaining(rtr::add);
		return checkCallStackSource(logger, rtr);
	}

	/**
	 * Check if the call stack of the source program execution is correct (according to procedure labels and step
	 * infos).
	 */
	protected boolean checkCallStackTargetProgramExecution(final ILogger logger,
			final IProgramExecution<TTE, TE> sourceProgramExecution) {
		final List<AtomicTraceElement<TTE>> rtr = new ArrayList<>();
		sourceProgramExecution.iterator().forEachRemaining(rtr::add);
		return checkCallStackTarget(logger, rtr);
	}

	/**
	 * Check if the call stack of a sequence of source atomic trace elements is consistent (according to procedure
	 * labels and step infos). If it is not consistent, print a fatal message.
	 */
	protected boolean checkCallStackSource(final ILogger logger, final List<AtomicTraceElement<STE>> trace) {
		final int index = getBrokenCallStackIndexForTrace(logger, trace);
		if (index == -1) {
			return true;
		}
		printBrokenCallStackSource(trace, index);
		return false;
	}

	/**
	 * Check if the call stack of a sequence of target atomic trace elements is consistent (according to procedure
	 * labels and step infos). If it is not consistent, print a fatal message.
	 */
	protected boolean checkCallStackTarget(final ILogger logger, final List<AtomicTraceElement<TTE>> trace) {
		final int index = getBrokenCallStackIndexForTrace(logger, trace);
		if (index == -1) {
			return true;
		}
		printBrokenCallStackTarget(trace, index);
		return false;
	}

	/**
	 * Check if the call stack of a sequence of atomic trace elements is broken and return the index of the element that
	 * indicates the breakage or -1 if the callstack is not broken.
	 *
	 * Also print a fatal log message if breakage is detected.
	 */
	private static int getBrokenCallStackIndexForTrace(final ILogger logger,
			final List<? extends AtomicTraceElement<?>> trace) {
		final Deque<String> callStack = new ArrayDeque<>();
		int i = 0;
		for (final AtomicTraceElement<?> elem : trace) {
			i++;
			if (elem.hasStepInfo(StepInfo.PROC_CALL)) {
				callStack.push(elem.getSucceedingProcedure());
			}
			if (elem.hasStepInfo(StepInfo.PROC_RETURN)) {
				if (callStack.isEmpty()) {
					logger.fatal("Callstack is empty and returning with " + elem);
					return i;
				}
				final String lastCall = callStack.pop();
				if (!lastCall.equals(elem.getPrecedingProcedure())) {
					logger.fatal("Callstack is " + lastCall + " but returning with " + elem);
					return i;
				}
			}
		}
		return -1;
	}

	/**
	 * Print a sequence of source atomic trace elements with an inconsistent call stack. Can be overridden by clients to
	 * implement printing.
	 */
	protected void printBrokenCallStackSource(final List<AtomicTraceElement<STE>> trace, final int breakpointIndex) {
		// do nothing by default
	}

	/**
	 * Print a sequence of target atomic trace elements with an inconsistent call stack. Can be overridden by clients to
	 * implement printing.
	 */
	protected void printBrokenCallStackTarget(final List<AtomicTraceElement<TTE>> trace, final int breakpointIndex) {
		// do nothing by default
	}

	@Override
	public ProgramState<TE> translateProgramState(final ProgramState<SE> oldProgramState) {
		if (oldProgramState == null) {
			return null;
		}
		final Map<TE, Collection<TE>> variable2Values = new HashMap<>();
		for (final SE oldVariable : oldProgramState.getVariables()) {
			final Collection<TE> newValues = new ArrayList<>();
			for (final SE oldValue : oldProgramState.getValues(oldVariable)) {
				newValues.add(translateExpression(oldValue));
			}
			final TE newVariable = translateExpression(oldVariable);
			variable2Values.put(newVariable, newValues);
		}
		return new ProgramState<>(variable2Values);
	}

	@FunctionalInterface
	public interface IFunction<P1, P2, P3, R> {
		R create(P1 p1, P2 p2, P3 p3);
	}
}
