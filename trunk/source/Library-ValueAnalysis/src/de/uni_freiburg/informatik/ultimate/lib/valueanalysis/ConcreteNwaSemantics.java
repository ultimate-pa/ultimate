/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE ValueAnalysis Library.
 *
 * The ULTIMATE ValueAnalysis Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ValueAnalysis Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ValueAnalysis Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ValueAnalysis Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ValueAnalysis Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.valueanalysis;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.ConcreteConfiguration.Frame;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.ConcreteConfiguration.LetterKind;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.ConcreteTransFormulaExecutor.StepKind;

/**
 * The concrete semantics of a program, given as its nested word automaton: the initial abstraction of the CEGAR loop,
 * whose states are program locations and whose letters are the program's transitions. Searches use it to explore the
 * program's concrete configurations.
 * <p>
 * Calls and returns follow the semantics the trace check gives them. A call keeps the global variables and the
 * program constants, passes the arguments to the callee's parameters, and sets {@code old(g)} to {@code g} for every
 * global {@code g} the callee may modify. A return restores the caller's valuation from the call, keeps the current
 * values of the global variables and the program constants, and assigns the returned values.
 *
 * @param <L>
 *            the type of letters
 * @author Max Barth (max.barth@lmu.de)
 */
public final class ConcreteNwaSemantics<L extends IIcfgTransition<?>> {
	private final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mAutomaton;
	private final ModifiableGlobalsTable mModifiableGlobals;
	private final ConcreteTransFormulaExecutor mExecutor;

	/**
	 * @param automaton
	 *            the program as nested word automaton whose accepting states are the error locations; its letters'
	 *            transition formulas are only read
	 * @param modifiableGlobals
	 *            the global variables each procedure may modify, of the same script as the letters
	 * @param executor
	 *            executes the letters' transition formulas
	 */
	public ConcreteNwaSemantics(final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> automaton,
			final ModifiableGlobalsTable modifiableGlobals, final ConcreteTransFormulaExecutor executor) {
		mAutomaton = automaton;
		mModifiableGlobals = modifiableGlobals;
		mExecutor = executor;
	}

	public List<ConcreteConfiguration<L>> initialConfigurations() {
		final List<ConcreteConfiguration<L>> result = new ArrayList<>();
		for (final IPredicate state : mAutomaton.getInitialStates()) {
			result.add(ConcreteConfiguration.initial(state));
		}
		return result;
	}

	/**
	 * @return whether {@code configuration} is at an error location
	 */
	public boolean isError(final ConcreteConfiguration<L> configuration) {
		return mAutomaton.isFinal(configuration.getState());
	}

	/**
	 * @return the configurations reachable from {@code configuration} by one letter
	 */
	public List<ConcreteConfiguration<L>> successors(final ConcreteConfiguration<L> configuration) {
		final List<ConcreteConfiguration<L>> result = new ArrayList<>();
		final IPredicate state = configuration.getState();
		final Map<IProgramVarOrConst, IConcreteValue> valuation = configuration.getValuation();
		for (final OutgoingInternalTransition<L, IPredicate> transition : mAutomaton.internalSuccessors(state)) {
			final L letter = transition.getLetter();
			for (final Map<IProgramVarOrConst, IConcreteValue> post : mExecutor.execute(letter.getTransformula(),
					valuation, valuation, StepKind.INTERNAL)) {
				result.add(configuration.successor(transition.getSucc(), post, configuration.getCallStack(), letter,
						LetterKind.INTERNAL));
			}
		}
		for (final OutgoingCallTransition<L, IPredicate> transition : mAutomaton.callSuccessors(state)) {
			addCallSuccessors(configuration, transition, result);
		}
		final Frame frame = configuration.getCallStack();
		if (frame != null) {
			for (final OutgoingReturnTransition<L, IPredicate> transition : mAutomaton
					.returnSuccessorsGivenHier(state, frame.hierarchicalPredecessor())) {
				addReturnSuccessors(configuration, transition, frame, result);
			}
		}
		return result;
	}

	private void addCallSuccessors(final ConcreteConfiguration<L> configuration,
			final OutgoingCallTransition<L, IPredicate> transition, final List<ConcreteConfiguration<L>> result) {
		final L letter = transition.getLetter();
		final Map<IProgramVarOrConst, IConcreteValue> valuation = configuration.getValuation();
		// The caller's valuation from before the call: with recursion, the callee's parameters are the caller's.
		final Frame frame = new Frame(configuration.getState(), valuation, configuration.getCallStack());
		for (final Map<IProgramVarOrConst, IConcreteValue> post : mExecutor.execute(letter.getTransformula(),
				valuation, valuation, StepKind.CALL_OR_RETURN)) {
			final Map<IProgramVarOrConst, IConcreteValue> callee = globalPart(post);
			// The arguments, assigned to the callee's parameters.
			for (final IProgramVarOrConst parameter : letter.getTransformula().getOutVars().keySet()) {
				final IConcreteValue value = post.get(parameter);
				if (value != null) {
					callee.put(parameter, value);
				}
			}
			for (final IProgramNonOldVar global : mModifiableGlobals
					.getModifiedBoogieVars(letter.getSucceedingProcedure())) {
				final IConcreteValue value = callee.get(global);
				if (value == null) {
					callee.remove(global.getOldVar());
				} else {
					callee.put(global.getOldVar(), value);
				}
			}
			result.add(configuration.successor(transition.getSucc(), callee, frame, letter, LetterKind.CALL));
		}
	}

	private void addReturnSuccessors(final ConcreteConfiguration<L> configuration,
			final OutgoingReturnTransition<L, IPredicate> transition, final Frame frame,
			final List<ConcreteConfiguration<L>> result) {
		final L letter = transition.getLetter();
		final Map<IProgramVarOrConst, IConcreteValue> callee = configuration.getValuation();
		// The caller's locals and old variables as at the call, the globals and constants as they are now.
		final Map<IProgramVarOrConst, IConcreteValue> caller = new HashMap<>(frame.callerValuation());
		caller.keySet().removeIf(ConcreteNwaSemantics::isGlobalPart);
		caller.putAll(globalPart(callee));
		for (final Map<IProgramVarOrConst, IConcreteValue> post : mExecutor.execute(letter.getTransformula(), callee,
				caller, StepKind.CALL_OR_RETURN)) {
			result.add(configuration.successor(transition.getSucc(), post, frame.next(), letter, LetterKind.RETURN));
		}
	}

	/**
	 * @return the values of the global variables (not their old versions) and the program constants
	 */
	private static Map<IProgramVarOrConst, IConcreteValue>
			globalPart(final Map<IProgramVarOrConst, IConcreteValue> valuation) {
		final Map<IProgramVarOrConst, IConcreteValue> result = new HashMap<>();
		for (final Entry<IProgramVarOrConst, IConcreteValue> entry : valuation.entrySet()) {
			if (isGlobalPart(entry.getKey())) {
				result.put(entry.getKey(), entry.getValue());
			}
		}
		return result;
	}

	private static boolean isGlobalPart(final IProgramVarOrConst var) {
		return var instanceof IProgramNonOldVar || var instanceof IProgramConst;
	}

	/**
	 * @return the run of the automaton that leads to {@code configuration}
	 */
	public NestedRun<L, IPredicate> toNestedRun(final ConcreteConfiguration<L> configuration) {
		final List<ConcreteConfiguration<L>> path = new ArrayList<>(configuration.getLength() + 1);
		for (ConcreteConfiguration<L> current = configuration; current != null; current = current.getPredecessor()) {
			path.add(current);
		}
		Collections.reverse(path);
		final int length = path.size() - 1;
		@SuppressWarnings("unchecked")
		final L[] word = (L[]) new IIcfgTransition<?>[length];
		final int[] nesting = new int[length];
		final List<IPredicate> states = new ArrayList<>(path.size());
		states.add(path.get(0).getState());
		final Deque<Integer> openCalls = new ArrayDeque<>();
		for (int i = 0; i < length; i++) {
			final ConcreteConfiguration<L> step = path.get(i + 1);
			word[i] = step.getLetter();
			states.add(step.getState());
			switch (step.getLetterKind()) {
			case CALL:
				openCalls.push(i);
				nesting[i] = NestedWord.PLUS_INFINITY;
				break;
			case RETURN:
				// The search starts with an empty call stack, so every return has its call in the run.
				final int call = openCalls.pop();
				nesting[call] = i;
				nesting[i] = call;
				break;
			case INTERNAL:
				nesting[i] = NestedWord.INTERNAL_POSITION;
				break;
			default:
				throw new AssertionError("unknown letter kind " + step.getLetterKind());
			}
		}
		return new NestedRun<>(new NestedWord<>(word, nesting), states);
	}
}
