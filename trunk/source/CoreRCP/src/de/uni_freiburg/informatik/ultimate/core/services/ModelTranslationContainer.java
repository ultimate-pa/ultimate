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

package de.uni_freiburg.informatik.ultimate.core.services;

import java.util.ArrayDeque;
import java.util.List;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.core.services.model.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.util.Utils;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
class ModelTranslationContainer implements IBacktranslationService {
	private ArrayDeque<ITranslator<?, ?, ?, ?>> mTranslationSequence;

	protected ModelTranslationContainer() {
		mTranslationSequence = new ArrayDeque<>();
	}

	protected ModelTranslationContainer(ModelTranslationContainer other) {
		mTranslationSequence = new ArrayDeque<>(other.mTranslationSequence);
	}

	public <STE, TTE, SE, TE> void addTranslator(ITranslator<STE, TTE, SE, TE> translator) {

		// enforce type compatibility
		if (mTranslationSequence.size() > 0) {
			ITranslator<?, ?, ?, ?> last = mTranslationSequence.getLast();

			if (!isAllowedNext(last, translator)) {
				throw new IllegalArgumentException(
						"The supplied ITranslator is not compatible with the existing ones. It has to be compatible with "
								+ last + ", but it is " + translator);
			}
		}
		mTranslationSequence.addLast(translator);

	}

	private boolean isAllowedNext(ITranslator<?, ?, ?, ?> current, ITranslator<?, ?, ?, ?> next) {
		// source is e.g. RcfgElement, target is e.g. BoogieASTNode
		// meaning, source is the output of the tool, target the input
		return current.getSourceExpressionClass() == next.getTargetExpressionClass()
				&& current.getSourceTraceElementClass() == next.getTargetTraceElementClass();
	}

	@Override
	public <SE> Object translateExpression(SE expression, Class<SE> clazz) {
		Stack<ITranslator<?, ?, ?, ?>> current = prepareExpressionStack(expression, clazz);
		return translateExpression(current, expression);
	}

	@Override
	public <SE> String translateExpressionToString(SE expression, Class<SE> clazz) {
		Stack<ITranslator<?, ?, ?, ?>> current = prepareExpressionStack(expression, clazz);
		ITranslator<?, ?, ?, ?> last = current.firstElement();
		return translateExpressionToString(translateExpression(current, expression), last);
	}

	@SuppressWarnings("unchecked")
	private <TE> String translateExpressionToString(TE expression, ITranslator<?, ?, ?, ?> trans) {
		ITranslator<?, ?, ?, TE> last = (ITranslator<?, ?, ?, TE>) trans;
		return last.targetExpressionToString(expression);
	}

	@SuppressWarnings("unchecked")
	private <TE, SE> TE translateExpression(Stack<ITranslator<?, ?, ?, ?>> remaining, SE expression) {
		if (remaining.isEmpty()) {
			return (TE) expression;
		} else {
			ITranslator<?, ?, SE, TE> tmp = (ITranslator<?, ?, SE, TE>) remaining.pop();
			return translateExpression(remaining, tmp.translateExpression(expression));
		}
	}

	private <SE> Stack<ITranslator<?, ?, ?, ?>> prepareExpressionStack(SE expression, Class<SE> clazz) {
		Stack<ITranslator<?, ?, ?, ?>> current = new Stack<ITranslator<?, ?, ?, ?>>();
		boolean canTranslate = false;
		for (ITranslator<?, ?, ?, ?> trans : mTranslationSequence) {
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
	public <STE> List<?> translateTrace(List<STE> trace, Class<STE> clazz) {
		Stack<ITranslator<?, ?, ?, ?>> current = prepareTraceStack(trace, clazz);
		return translateTrace(current, trace);
	}

	@Override
	public <STE> List<String> translateTraceToHumanReadableString(List<STE> trace, Class<STE> clazz) {
		Stack<ITranslator<?, ?, ?, ?>> current = prepareTraceStack(trace, clazz);
		ITranslator<?, ?, ?, ?> last = current.firstElement();
		return translateTraceToString(translateTrace(current, trace), last);
	}

	@SuppressWarnings("unchecked")
	private <TTE> List<String> translateTraceToString(List<TTE> trace, ITranslator<?, ?, ?, ?> trans) {
		ITranslator<?, TTE, ?, ?> last = (ITranslator<?, TTE, ?, ?>) trans;
		return last.targetTraceToString(trace);
	}

	private <STE> Stack<ITranslator<?, ?, ?, ?>> prepareTraceStack(List<STE> trace, Class<STE> clazz) {
		Stack<ITranslator<?, ?, ?, ?>> current = new Stack<ITranslator<?, ?, ?, ?>>();
		boolean canTranslate = false;
		for (ITranslator<?, ?, ?, ?> trans : mTranslationSequence) {
			current.push(trans);
			if (trans.getSourceTraceElementClass().isAssignableFrom(clazz)) {
				canTranslate = true;
			}
		}
		if (!canTranslate) {
			throw new IllegalArgumentException("You cannot translate " + Utils.join(trace, ",")
					+ " with this backtranslation service, as there is no compatible ITranslator available");
		}
		if (!current.peek().getSourceTraceElementClass().isAssignableFrom(clazz)) {
			throw new IllegalArgumentException("You cannot translate " + Utils.join(trace, ",")
					+ " with this backtranslation service, as the last ITranslator in this chain is not compatible");
		}
		return current;
	}

	@SuppressWarnings("unchecked")
	private <TTE, STE> List<TTE> translateTrace(Stack<ITranslator<?, ?, ?, ?>> remaining, List<STE> trace) {
		if (remaining.isEmpty()) {
			return (List<TTE>) trace;
		} else {
			ITranslator<STE, TTE, ?, ?> translator = (ITranslator<STE, TTE, ?, ?>) remaining.pop();
			return translateTrace(remaining, translator.translateTrace(trace));
		}
	}

	@Override
	public <STE, SE> IProgramExecution<?, ?> translateProgramExecution(IProgramExecution<STE, SE> programExecution) {
		Stack<ITranslator<?, ?, ?, ?>> current = new Stack<ITranslator<?, ?, ?, ?>>();
		boolean canTranslate = false;
		for (ITranslator<?, ?, ?, ?> trans : mTranslationSequence) {
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
			Stack<ITranslator<?, ?, ?, ?>> remaining, IProgramExecution<STE, SE> programExecution) {
		if (remaining.isEmpty()) {
			return (IProgramExecution<TTE, TE>) programExecution;
		} else {
			ITranslator<STE, TTE, SE, TE> translator = (ITranslator<STE, TTE, SE, TE>) remaining.pop();
			IProgramExecution<TTE, TE> translated = translator.translateProgramExecution(programExecution);
//			assert programExecution.getLength() == 0 || translated.getLength() > 0;
			return translateProgramExecution(remaining, translated);
		}
	}

	@Override
	public IBacktranslationService getTranslationServiceCopy() {
		return new ModelTranslationContainer(this);
	}

	@Override
	public String toString() {
		return Utils.join(mTranslationSequence, ",");
	}
}
