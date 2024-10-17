/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.core.coreplugin.services;

import java.util.ArrayDeque;
import java.util.List;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.core.model.models.ProcedureContract;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslatedCFG;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.core.model.translation.ITranslator;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
class ModelTranslationContainer implements IBacktranslationService {
	private final ArrayDeque<ITranslator<?, ?, ?, ?, ?, ?, ?>> mTranslationSequence;

	protected ModelTranslationContainer() {
		mTranslationSequence = new ArrayDeque<>();
	}

	protected ModelTranslationContainer(final ModelTranslationContainer other) {
		mTranslationSequence = new ArrayDeque<>(other.mTranslationSequence);
	}

	@Override
	public <STE, TTE, SE, TE, SVL, TVL, LOC> void
			addTranslator(final ITranslator<STE, TTE, SE, TE, SVL, TVL, LOC> translator) {
		// enforce type compatibility
		if (mTranslationSequence.size() > 0) {
			final ITranslator<?, ?, ?, ?, ?, ?, ?> last = mTranslationSequence.getLast();
			if (!isAllowedNext(last, translator)) {
				throw new IllegalArgumentException(
						"The supplied ITranslator is not compatible with the existing ones. It has to be compatible with "
								+ last + ", but it is " + translator);
			}
		}
		mTranslationSequence.addLast(translator);
	}

	private static boolean isAllowedNext(final ITranslator<?, ?, ?, ?, ?, ?, ?> current,
			final ITranslator<?, ?, ?, ?, ?, ?, ?> next) {
		// source is e.g. RcfgElement, target is e.g. BoogieASTNode
		// meaning, source is the output of the tool, target the input
		return current.getSourceExpressionClass() == next.getTargetExpressionClass()
				&& current.getSourceTraceElementClass() == next.getTargetTraceElementClass();
	}

	@Override
	public <SE, TE> TE translateExpression(final SE expression, final Class<SE> clazz) {
		final Stack<ITranslator<?, ?, ?, ?, ?, ?, ?>> current = prepareTranslatorStackAndCheckSourceExpression(clazz);
		return translateExpression(current, expression);
	}

	@Override
	public <SE, CTX> String translateExpressionWithContextToString(final SE expression, final CTX context,
			final Class<SE> clazz) {
		final Stack<ITranslator<?, ?, ?, ?, ?, ?, ?>> current = prepareTranslatorStackAndCheckSourceExpression(clazz);
		final ITranslator<?, ?, ?, ?, ?, ?, CTX> last = (ITranslator<?, ?, ?, ?, ?, ?, CTX>) current.firstElement();
		return translateExpressionToString(translateExpressionWithContext(current, expression, context), last);
	}

	@SuppressWarnings("unchecked")
	private <TE, SE, CTX> TE translateExpressionWithContext(final Stack<ITranslator<?, ?, ?, ?, ?, ?, ?>> remaining,
			final SE expression, final CTX context) {
		if (remaining.isEmpty()) {
			return (TE) expression;
		}
		final ITranslator<?, ?, SE, TE, ?, ?, CTX> tmp = (ITranslator<?, ?, SE, TE, ?, ?, CTX>) remaining.pop();
		return translateExpressionWithContext(remaining, tmp.translateExpressionWithContext(expression, context),
				context);
	}

	@Override
	public <SE> String translateExpressionToString(final SE expression, final Class<SE> clazz) {
		final Stack<ITranslator<?, ?, ?, ?, ?, ?, ?>> current = prepareTranslatorStackAndCheckSourceExpression(clazz);
		final ITranslator<?, ?, ?, ?, ?, ?, ?> last = current.firstElement();
		return translateExpressionToString(translateExpression(current, expression), last);
	}

	@SuppressWarnings("unchecked")
	private static <TE> String translateExpressionToString(final TE expression,
			final ITranslator<?, ?, ?, ?, ?, ?, ?> trans) {
		final ITranslator<?, ?, ?, TE, ?, ?, ?> last = (ITranslator<?, ?, ?, TE, ?, ?, ?>) trans;
		return last.targetExpressionToString(expression);
	}

	@SuppressWarnings("unchecked")
	private <TE, SE> TE translateExpression(final Stack<ITranslator<?, ?, ?, ?, ?, ?, ?>> remaining,
			final SE expression) {
		if (remaining.isEmpty()) {
			return (TE) expression;
		}
		final ITranslator<?, ?, SE, TE, ?, ?, ?> tmp = (ITranslator<?, ?, SE, TE, ?, ?, ?>) remaining.pop();
		return translateExpression(remaining, tmp.translateExpression(expression));
	}

	@Override
	public <STE> List<?> translateTrace(final List<STE> trace, final Class<STE> clazz) {
		final Stack<ITranslator<?, ?, ?, ?, ?, ?, ?>> current = prepareTranslatorStackAndCheckSourceTraceElement(clazz);
		return translateTrace(current, trace);
	}

	@Override
	public <STE> List<String> translateTraceToHumanReadableString(final List<STE> trace, final Class<STE> clazz) {
		final Stack<ITranslator<?, ?, ?, ?, ?, ?, ?>> current = prepareTranslatorStackAndCheckSourceTraceElement(clazz);
		final ITranslator<?, ?, ?, ?, ?, ?, ?> last = current.firstElement();
		return translateTraceToString(translateTrace(current, trace), last);
	}

	@SuppressWarnings("unchecked")
	private static <TTE> List<String> translateTraceToString(final List<TTE> trace,
			final ITranslator<?, ?, ?, ?, ?, ?, ?> trans) {
		final ITranslator<?, TTE, ?, ?, ?, ?, ?> last = (ITranslator<?, TTE, ?, ?, ?, ?, ?>) trans;
		return last.targetTraceToString(trace);
	}

	private <STE> Stack<ITranslator<?, ?, ?, ?, ?, ?, ?>>
			prepareTranslatorStackAndCheckSourceTraceElement(final Class<STE> classOfSourceElement) {
		final Stack<ITranslator<?, ?, ?, ?, ?, ?, ?>> current = new Stack<>();
		boolean canTranslate = false;
		for (final ITranslator<?, ?, ?, ?, ?, ?, ?> trans : mTranslationSequence) {
			current.push(trans);
			if (trans.getSourceTraceElementClass().isAssignableFrom(classOfSourceElement)) {
				canTranslate = true;
			}
		}
		if (!canTranslate) {
			throw new IllegalArgumentException("You cannot translate " + classOfSourceElement.getSimpleName()
					+ " with this backtranslation service, as there is no compatible ITranslator available");
		}
		if (!current.peek().getSourceTraceElementClass().isAssignableFrom(classOfSourceElement)) {
			throw new IllegalArgumentException("You cannot translate " + classOfSourceElement.getSimpleName()
					+ " with this backtranslation service, as the last ITranslator in this chain is not compatible");
		}
		return current;
	}

	private <STE> Stack<ITranslator<?, ?, ?, ?, ?, ?, ?>>
			prepareTranslatorStackAndCheckSourceExpression(final Class<STE> classOfSourceExpression) {
		final Stack<ITranslator<?, ?, ?, ?, ?, ?, ?>> current = new Stack<>();
		boolean canTranslate = false;
		for (final ITranslator<?, ?, ?, ?, ?, ?, ?> trans : mTranslationSequence) {
			current.push(trans);
			if (trans.getSourceExpressionClass().isAssignableFrom(classOfSourceExpression)) {
				canTranslate = true;
			}
		}
		if (!canTranslate) {
			throw new IllegalArgumentException("You cannot translate " + classOfSourceExpression.getSimpleName()
					+ " with this backtranslation service, as there is no compatible ITranslator available");
		}
		if (!current.peek().getSourceExpressionClass().isAssignableFrom(classOfSourceExpression)) {
			throw new IllegalArgumentException("You cannot translate " + classOfSourceExpression.getSimpleName()
					+ " with this backtranslation service, as the last ITranslator in this chain is not compatible");
		}
		return current;
	}

	@SuppressWarnings("unchecked")
	private <TTE, STE> List<TTE> translateTrace(final Stack<ITranslator<?, ?, ?, ?, ?, ?, ?>> remaining,
			final List<STE> trace) {
		if (remaining.isEmpty()) {
			return (List<TTE>) trace;
		}
		final ITranslator<STE, TTE, ?, ?, ?, ?, ?> translator = (ITranslator<STE, TTE, ?, ?, ?, ?, ?>) remaining.pop();
		return translateTrace(remaining, translator.translateTrace(trace));
	}

	@Override
	public <STE, SE> IProgramExecution<?, ?>
			translateProgramExecution(final IProgramExecution<STE, SE> programExecution) {
		final ArrayDeque<ITranslator<?, ?, ?, ?, ?, ?, ?>> current = new ArrayDeque<>();
		boolean canTranslate = false;
		for (final ITranslator<?, ?, ?, ?, ?, ?, ?> trans : mTranslationSequence) {
			current.push(trans);
			if (trans.getSourceTraceElementClass().isAssignableFrom(programExecution.getTraceElementClass())
					&& trans.getSourceExpressionClass().isAssignableFrom(programExecution.getExpressionClass())) {
				canTranslate = true;
			}
		}
		if (!canTranslate) {
			throw new IllegalArgumentException("You cannot translate " + programExecution
					+ " with this backtranslation service, as there is no compatible ITranslator available");
		}

		if (!current.peek().getSourceTraceElementClass().isAssignableFrom(programExecution.getTraceElementClass())
				|| !current.peek().getSourceExpressionClass().isAssignableFrom(programExecution.getExpressionClass())) {
			throw new IllegalArgumentException("You cannot translate " + programExecution
					+ " with this backtranslation service, as the last ITranslator in this chain is not compatible");
		}
		return translateProgramExecution(current, programExecution);
	}

	@SuppressWarnings("unchecked")
	private <STE, TTE, SE, TE> IProgramExecution<TTE, TE> translateProgramExecution(
			final ArrayDeque<ITranslator<?, ?, ?, ?, ?, ?, ?>> remainingBefore,
			final IProgramExecution<STE, SE> programExecution) {
		if (remainingBefore.isEmpty()) {
			return (IProgramExecution<TTE, TE>) programExecution;
		}
		final ArrayDeque<ITranslator<?, ?, ?, ?, ?, ?, ?>> remainingAfter = new ArrayDeque<>(remainingBefore);
		final ITranslator<STE, TTE, SE, TE, ?, ?, ?> translator =
				(ITranslator<STE, TTE, SE, TE, ?, ?, ?>) remainingAfter.pop();
		final IProgramExecution<TTE, TE> translated = translator.translateProgramExecution(programExecution);

		// System.out.println("-----");
		// System.out.println(translator.getClass());
		// System.out.println(programExecution);
		// System.out.println();
		// System.out.println(translated);
		// System.out.println("-----");

		return translateProgramExecution(remainingAfter, translated);
	}

	@Override
	public <SE> ProgramState<?> translateProgramState(final ProgramState<SE> programState) {
		final Stack<ITranslator<?, ?, ?, ?, ?, ?, ?>> current = new Stack<>();
		boolean canTranslate = false;
		for (final ITranslator<?, ?, ?, ?, ?, ?, ?> trans : mTranslationSequence) {
			current.push(trans);
			// TODO: check if we can translate
			canTranslate = true;
			// if (trans.getSourceTraceElementClass().isAssignableFrom(programExecution.getTraceElementClass())
			// && trans.getSourceExpressionClass().isAssignableFrom(programExecution.getExpressionClass())) {
			// canTranslate = true;
			// }
		}
		if (!canTranslate) {
			throw new IllegalArgumentException("You cannot translate " + programState
					+ " with this backtranslation service, as there is no compatible ITranslator available");
		}

		// if (!current.peek().getSourceTraceElementClass().isAssignableFrom(programExecution.getTraceElementClass())
		// || !current.peek().getSourceExpressionClass().isAssignableFrom(programExecution.getExpressionClass())) {
		// throw new IllegalArgumentException("You cannot translate " + programExecution
		// + " with this backtranslation service, as the last ITranslator in this chain is not compatible");
		// }
		return translateProgramState(current, programState);
	}

	@SuppressWarnings("unchecked")
	private <SE, TE> ProgramState<TE> translateProgramState(final Stack<ITranslator<?, ?, ?, ?, ?, ?, ?>> remaining,
			final ProgramState<SE> programState) {
		if (remaining.isEmpty()) {
			return (ProgramState<TE>) programState;
		}
		final ITranslator<?, ?, SE, TE, ?, ?, ?> translator = (ITranslator<?, ?, SE, TE, ?, ?, ?>) remaining.pop();
		final ProgramState<TE> translated = translator.translateProgramState(programState);
		return translateProgramState(remaining, translated);
	}

	@Override
	public <SE> String translateProgramStateToString(final ProgramState<SE> programState) {
		final Stack<ITranslator<?, ?, ?, ?, ?, ?, ?>> current =
				prepareTranslatorStackAndCheckSourceExpression(programState.getClassOfExpression());
		final ITranslator<?, ?, ?, ?, ?, ?, ?> last = current.firstElement();
		return translateProgramStateToString(translateProgramState(current, programState), last);
	}

	private static <TE> String translateProgramStateToString(final ProgramState<TE> translateProgramState,
			final ITranslator<?, ?, ?, ?, ?, ?, ?> trans) {
		final ITranslator<?, ?, ?, TE, ?, ?, ?> last = (ITranslator<?, ?, ?, TE, ?, ?, ?>) trans;
		return translateProgramState.toString(x -> last.targetExpressionToString(x));
	}

	@Override
	public <STE, SE> IBacktranslatedCFG<?, ?> translateCFG(final IBacktranslatedCFG<?, STE> cfg) {
		final Stack<ITranslator<?, ?, ?, ?, ?, ?, ?>> current = new Stack<>();
		boolean canTranslate = false;
		for (final ITranslator<?, ?, ?, ?, ?, ?, ?> trans : mTranslationSequence) {
			current.push(trans);
			if (trans.getSourceTraceElementClass().isAssignableFrom(cfg.getTraceElementClass())) {
				canTranslate = true;
			}
		}
		if (!canTranslate) {
			throw new IllegalArgumentException("You cannot translate " + cfg
					+ " with this backtranslation service, as there is no compatible ITranslator available");
		}

		if (!current.peek().getSourceTraceElementClass().isAssignableFrom(cfg.getTraceElementClass())) {
			throw new IllegalArgumentException("You cannot translate " + cfg
					+ " with this backtranslation service, as the last ITranslator in this chain is not compatible");
		}
		return translateCFG(current, cfg);
	}

	@SuppressWarnings("unchecked")
	private <STE, TTE, SE, TE, SVL, TVL> IBacktranslatedCFG<TVL, TTE> translateCFG(
			final Stack<ITranslator<?, ?, ?, ?, ?, ?, ?>> remaining, final IBacktranslatedCFG<SVL, STE> cfg) {
		if (remaining.isEmpty()) {
			return (IBacktranslatedCFG<TVL, TTE>) cfg;
		}
		final ITranslator<STE, TTE, SE, TE, SVL, TVL, ?> translator =
				(ITranslator<STE, TTE, SE, TE, SVL, TVL, ?>) remaining.pop();
		final IBacktranslatedCFG<?, TTE> translated = translator.translateCFG(cfg);
		return translateCFG(remaining, translated);
	}

	@Override
	public <TE, SE, CTX> ProcedureContract<TE, ? extends TE> translateProcedureContract(
			final ProcedureContract<SE, ? extends SE> contract, final CTX context, final Class<SE> clazz) {
		final Stack<ITranslator<?, ?, ?, ?, ?, ?, ?>> current = prepareTranslatorStackAndCheckSourceExpression(clazz);
		return translateProcedureContract(current, contract, context);
	}

	@SuppressWarnings("unchecked")
	private <TE, SE, CTX> ProcedureContract<TE, ? extends TE> translateProcedureContract(
			final Stack<ITranslator<?, ?, ?, ?, ?, ?, ?>> remaining, final ProcedureContract<SE, ? extends SE> contract,
			final CTX context) {
		if (remaining.isEmpty()) {
			return (ProcedureContract<TE, ? extends TE>) contract;
		}
		final ITranslator<?, ?, SE, TE, ?, ?, CTX> tmp = (ITranslator<?, ?, SE, TE, ?, ?, CTX>) remaining.pop();
		return translateProcedureContract(remaining, tmp.translateProcedureContract(contract, context), context);
	}

	@Override
	public IBacktranslationService getTranslationServiceCopy() {
		return new ModelTranslationContainer(this);
	}

	@Override
	public String toString() {
		return CoreUtil.join(mTranslationSequence, ",");
	}

}
