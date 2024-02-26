package de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.util;

import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class IcfgAngelicProgramExecution<L extends IAction> implements IProgramExecution<L, Term> {

	private final boolean mAngelicStatus;
	private final IProgramExecution<L, Term> mProgramExecution;

	public IcfgAngelicProgramExecution(final IProgramExecution<L, Term> pe, final boolean angelicStatus) {
		mProgramExecution = pe;
		mAngelicStatus = angelicStatus;
	}

	public boolean getAngelicStatus() {
		return mAngelicStatus;
	}

	@Override
	public int getLength() {
		return mProgramExecution.getLength();
	}

	@Override
	public AtomicTraceElement<L> getTraceElement(final int index) {
		return mProgramExecution.getTraceElement(index);
	}

	@Override
	public ProgramState<Term> getProgramState(final int index) {
		return mProgramExecution.getProgramState(index);
	}

	@Override
	public ProgramState<Term> getInitialProgramState() {
		return mProgramExecution.getInitialProgramState();
	}

	@Override
	public Class<Term> getExpressionClass() {
		return mProgramExecution.getExpressionClass();
	}

	@Override
	public Class<? extends L> getTraceElementClass() {
		return mProgramExecution.getTraceElementClass();
	}

	@Override
	public IBacktranslationValueProvider<L, Term> getBacktranslationValueProvider() {
		return mProgramExecution.getBacktranslationValueProvider();
	}

	@Override
	public boolean isConcurrent() {
		return mProgramExecution.isConcurrent();
	}

}
