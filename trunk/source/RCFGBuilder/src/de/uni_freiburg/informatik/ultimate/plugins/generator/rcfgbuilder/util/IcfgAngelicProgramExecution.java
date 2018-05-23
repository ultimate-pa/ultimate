package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util;

import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;

public class IcfgAngelicProgramExecution implements IProgramExecution<IcfgEdge, Term> {

	private final boolean mAngelicStatus;
	private final IProgramExecution<IcfgEdge, Term> mProgramExecution;

	public IcfgAngelicProgramExecution(final IProgramExecution<IcfgEdge, Term> pe, final boolean angelicStatus) {
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
	public AtomicTraceElement<IcfgEdge> getTraceElement(final int index) {
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
	public Class<IcfgEdge> getTraceElementClass() {
		return mProgramExecution.getTraceElementClass();
	}

	@Override
	public IBacktranslationValueProvider<IcfgEdge, Term> getBacktranslationValueProvider() {
		return mProgramExecution.getBacktranslationValueProvider();
	}

}
