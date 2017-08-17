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

import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslatedCFG;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.ITranslator;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
class ModelTranslationContainer implements IBacktranslationService {
	private final ArrayDeque<ITranslator<?, ?, ?, ?, ?, ?>> mTranslationSequence;

	protected ModelTranslationContainer() {
		mTranslationSequence = new ArrayDeque<>();
	}

	protected ModelTranslationContainer(final ModelTranslationContainer other) {
		mTranslationSequence = new ArrayDeque<>(other.mTranslationSequence);
	}

	@Override
	public <STE, TTE, SE, TE, SVL, TVL> void addTranslator(final ITranslator<STE, TTE, SE, TE, SVL, TVL> translator) {

		// enforce type compatibility
		if (mTranslationSequence.size() > 0) {
			final ITranslator<?, ?, ?, ?, ?, ?> last = mTranslationSequence.getLast();

			if (!isAllowedNext(last, translator)) {
				throw new IllegalArgumentException(
						"The supplied ITranslator is not compatible with the existing ones. It has to be compatible with "
								+ last + ", but it is " + translator);
			}
		}
		mTranslationSequence.addLast(translator);

	}

	private static boolean isAllowedNext(final ITranslator<?, ?, ?, ?, ?, ?> current,
			final ITranslator<?, ?, ?, ?, ?, ?> next) {
		// source is e.g. RcfgElement, target is e.g. BoogieASTNode
		// meaning, source is the output of the tool, target the input
		return current.getSourceExpressionClass() == next.getTargetExpressionClass()
				&& current.getSourceTraceElementClass() == next.getTargetTraceElementClass();
	}

	@Override
	public <SE, TE> TE translateExpression(final SE expression, final Class<SE> clazz) {
		final Stack<ITranslator<?, ?, ?, ?, ?, ?>> current = prepareExpressionStack(expression, clazz);
		return translateExpression(current, expression);
	}

	@Override
	public <SE> String translateExpressionToString(final SE expression, final Class<SE> clazz) {
		final Stack<ITranslator<?, ?, ?, ?, ?, ?>> current = prepareExpressionStack(expression, clazz);
		final ITranslator<?, ?, ?, ?, ?, ?> last = current.firstElement();
		return translateExpressionToString(translateExpression(current, expression), last);
	}

	@SuppressWarnings("unchecked")
	private static <TE> String translateExpressionToString(final TE expression,
			final ITranslator<?, ?, ?, ?, ?, ?> trans) {
		final ITranslator<?, ?, ?, TE, ?, ?> last = (ITranslator<?, ?, ?, TE, ?, ?>) trans;
		return last.targetExpressionToString(expression);
	}

	@SuppressWarnings("unchecked")
	private <TE, SE> TE translateExpression(final Stack<ITranslator<?, ?, ?, ?, ?, ?>> remaining, final SE expression) {
		if (remaining.isEmpty()) {
			return (TE) expression;
		}
		final ITranslator<?, ?, SE, TE, ?, ?> tmp = (ITranslator<?, ?, SE, TE, ?, ?>) remaining.pop();
		return translateExpression(remaining, tmp.translateExpression(expression));
	}

	private <SE> Stack<ITranslator<?, ?, ?, ?, ?, ?>> prepareExpressionStack(final SE expression,
			final Class<SE> clazz) {
		final Stack<ITranslator<?, ?, ?, ?, ?, ?>> current = new Stack<>();
		boolean canTranslate = false;
		for (final ITranslator<?, ?, ?, ?, ?, ?> trans : mTranslationSequence) {
			current.push(trans);
			if (trans.getSourceExpressionClass().isAssignableFrom(clazz)) {
				canTranslate = true;
			}
		}
		if (!canTranslate) {
			throw new IllegalArgumentException("You cannot translate " + expression.getClass().getName()
					+ " with this backtranslation service, as there is no compatible "
					+ "ITranslator available. Available translators: " + toString());
		}
		if (!current.peek().getSourceExpressionClass().isAssignableFrom(clazz)) {
			throw new IllegalArgumentException("You cannot translate " + expression.getClass().getName()
					+ " with this backtranslation service, as the last ITranslator in "
					+ "this chain is not compatible. Available translators: " + toString());
		}
		return current;
	}

	@Override
	public <STE> List<?> translateTrace(final List<STE> trace, final Class<STE> clazz) {
		final Stack<ITranslator<?, ?, ?, ?, ?, ?>> current = prepareTranslatorStack(clazz);
		return translateTrace(current, trace);
	}

	@Override
	public <STE> List<String> translateTraceToHumanReadableString(final List<STE> trace, final Class<STE> clazz) {
		final Stack<ITranslator<?, ?, ?, ?, ?, ?>> current = prepareTranslatorStack(clazz);
		final ITranslator<?, ?, ?, ?, ?, ?> last = current.firstElement();
		return translateTraceToString(translateTrace(current, trace), last);
	}

	@SuppressWarnings("unchecked")
	private static <TTE> List<String> translateTraceToString(final List<TTE> trace,
			final ITranslator<?, ?, ?, ?, ?, ?> trans) {
		final ITranslator<?, TTE, ?, ?, ?, ?> last = (ITranslator<?, TTE, ?, ?, ?, ?>) trans;
		return last.targetTraceToString(trace);
	}

	private <STE> Stack<ITranslator<?, ?, ?, ?, ?, ?>> prepareTranslatorStack(final Class<STE> clazz) {
		final Stack<ITranslator<?, ?, ?, ?, ?, ?>> current = new Stack<>();
		boolean canTranslate = false;
		for (final ITranslator<?, ?, ?, ?, ?, ?> trans : mTranslationSequence) {
			current.push(trans);
			if (trans.getSourceTraceElementClass().isAssignableFrom(clazz)) {
				canTranslate = true;
			}
		}
		if (!canTranslate) {
			throw new IllegalArgumentException("You cannot translate " + clazz.getSimpleName()
					+ " with this backtranslation service, as there is no compatible ITranslator available");
		}
		if (!current.peek().getSourceTraceElementClass().isAssignableFrom(clazz)) {
			throw new IllegalArgumentException("You cannot translate " + clazz.getSimpleName()
					+ " with this backtranslation service, as the last ITranslator in this chain is not compatible");
		}
		return current;
	}

	@SuppressWarnings("unchecked")
	private <TTE, STE> List<TTE> translateTrace(final Stack<ITranslator<?, ?, ?, ?, ?, ?>> remaining,
			final List<STE> trace) {
		if (remaining.isEmpty()) {
			return (List<TTE>) trace;
		}
		final ITranslator<STE, TTE, ?, ?, ?, ?> translator = (ITranslator<STE, TTE, ?, ?, ?, ?>) remaining.pop();
		return translateTrace(remaining, translator.translateTrace(trace));
	}

	@Override
	public <STE, SE> IProgramExecution<?, ?>
			translateProgramExecution(final IProgramExecution<STE, SE> programExecution) {
		final Stack<ITranslator<?, ?, ?, ?, ?, ?>> current = new Stack<>();
		boolean canTranslate = false;
		for (final ITranslator<?, ?, ?, ?, ?, ?> trans : mTranslationSequence) {
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
			final Stack<ITranslator<?, ?, ?, ?, ?, ?>> remaining, final IProgramExecution<STE, SE> programExecution) {
		if (remaining.isEmpty()) {
			return (IProgramExecution<TTE, TE>) programExecution;
		}
		final ITranslator<STE, TTE, SE, TE, ?, ?> translator = (ITranslator<STE, TTE, SE, TE, ?, ?>) remaining.pop();
		final IProgramExecution<TTE, TE> translated = translator.translateProgramExecution(programExecution);
		return translateProgramExecution(remaining, translated);
	}

	@Override
	public <STE, SE> IBacktranslatedCFG<?, ?> translateCFG(final IBacktranslatedCFG<?, STE> cfg) {
		final Stack<ITranslator<?, ?, ?, ?, ?, ?>> current = new Stack<>();
		boolean canTranslate = false;
		for (final ITranslator<?, ?, ?, ?, ?, ?> trans : mTranslationSequence) {
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
	private <STE, TTE, SE, TE, SVL, TVL> IBacktranslatedCFG<TVL, TTE>
			translateCFG(final Stack<ITranslator<?, ?, ?, ?, ?, ?>> remaining, final IBacktranslatedCFG<SVL, STE> cfg) {
		if (remaining.isEmpty()) {
			return (IBacktranslatedCFG<TVL, TTE>) cfg;
		}
		final ITranslator<STE, TTE, SE, TE, SVL, TVL> translator =
				(ITranslator<STE, TTE, SE, TE, SVL, TVL>) remaining.pop();
		final IBacktranslatedCFG<?, TTE> translated = translator.translateCFG(cfg);
		return translateCFG(remaining, translated);
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
