package de.uni_freiburg.informatik.ultimate.core.services;

import java.util.LinkedList;
import java.util.List;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.util.Utils;

class ModelTranslationContainer implements IBacktranslationService {
	private LinkedList<ITranslator<?, ?, ?, ?>> mTranslationSequence;

	protected ModelTranslationContainer() {
		mTranslationSequence = new LinkedList<>();
	}

	protected ModelTranslationContainer(ModelTranslationContainer other) {
		mTranslationSequence = new LinkedList<>(other.mTranslationSequence);
	}

	public <STE, TTE, SE, TE> void addTranslator(ITranslator<STE, TTE, SE, TE> translator) {

		// enforce type compatibility
		if (mTranslationSequence.size() > 0) {
			ITranslator<?, ?, ?, ?> last = mTranslationSequence.getLast();

			if (!isAllowedNext(last, translator)) {
				throw new IllegalArgumentException("The supplied ITranslator is not compatible with the existing ones");
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
		Stack<ITranslator<?, ?, ?, ?>> current = new Stack<ITranslator<?, ?, ?, ?>>();
		boolean canTranslate = false;
		for (ITranslator<?, ?, ?, ?> trans : mTranslationSequence) {
			current.push(trans);
			if (trans.getSourceExpressionClass() == clazz) {
				canTranslate = true;
			}
		}
		if (!canTranslate) {
			throw new IllegalArgumentException("You cannot translate " + expression
					+ " with this backtranslation service, as there is no compatible ITranslator available");
		}
		if (current.peek().getSourceExpressionClass() != clazz) {
			throw new IllegalArgumentException("You cannot translate " + expression
					+ " with this backtranslation service, as the last ITranslator in this chain is not compatible");
		}

		return translateExpression(current, expression);
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

	@Override
	public <STE> List<?> translateTrace(List<STE> trace, Class<STE> clazz) {
		Stack<ITranslator<?, ?, ?, ?>> current = new Stack<ITranslator<?, ?, ?, ?>>();
		boolean canTranslate = false;
		for (ITranslator<?, ?, ?, ?> trans : mTranslationSequence) {
			current.push(trans);
			if (trans.getSourceTraceElementClass() == clazz) {
				canTranslate = true;
			}
		}
		if (!canTranslate) {
			throw new IllegalArgumentException("You cannot translate " + Utils.join(trace, ",")
					+ " with this backtranslation service, as there is no compatible ITranslator available");
		}
		if (current.peek().getSourceTraceElementClass() != clazz) {
			throw new IllegalArgumentException("You cannot translate " + Utils.join(trace, ",")
					+ " with this backtranslation service, as the last ITranslator in this chain is not compatible");
		}
		return translateTrace(current, trace);
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
			if (trans.getSourceTraceElementClass() == programExecution.getTraceElementClass()
					&& trans.getSourceExpressionClass() == programExecution.getExpressionClass()) {
				canTranslate = true;
			}
		}
		if (!canTranslate) {
			throw new IllegalArgumentException("You cannot translate " + programExecution
					+ " with this backtranslation service, as there is no compatible ITranslator available");
		}

		if (current.peek().getSourceTraceElementClass() != programExecution.getTraceElementClass()
				|| current.peek().getSourceExpressionClass() != programExecution.getExpressionClass()) {
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
			return translateProgramExecution(remaining, translator.translateProgramExecution(programExecution));
		}
	}

	@Override
	public IBacktranslationService getTranslationServiceCopy() {
		return new ModelTranslationContainer(this);
	}

	@Override
	public <SE> String translateExpressionToString(SE expression, Class<SE> clazz) {
		// TODO: The idea is the same as in translateTraceToString(..)
		throw new UnsupportedOperationException("Not yet implemented");
	}

	@Override
	public <STE> List<String> translateTraceToString(List<STE> trace, Class<STE> clazz) {
		// TODO: The idea is that a backtranslator may contain a reference to an
		// toString implementation (via some interface and some object) that can
		// be called after the actual back translation (i.e. the last/first
		// translator has such a toString, and it is called element-wise

		throw new UnsupportedOperationException("Not yet implemented");
	}

	@Override
	public String toString() {
		return Utils.join(mTranslationSequence, ",");
	}

}