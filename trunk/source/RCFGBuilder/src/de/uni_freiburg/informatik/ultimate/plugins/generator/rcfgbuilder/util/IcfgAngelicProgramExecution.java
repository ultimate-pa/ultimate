package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util;

import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

public class IcfgAngelicProgramExecution implements IProgramExecution<IIcfgTransition<IcfgLocation>, Term> {

	private final boolean mAngelicStatus;
	private final IProgramExecution<IIcfgTransition<IcfgLocation>, Term> mProgramExecution;

	public IcfgAngelicProgramExecution(final IProgramExecution<IIcfgTransition<IcfgLocation>, Term> pe,
			final boolean angelicStatus) {
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
	public AtomicTraceElement<IIcfgTransition<IcfgLocation>> getTraceElement(final int index) {
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
	public Class<? extends IIcfgTransition<IcfgLocation>> getTraceElementClass() {
		return mProgramExecution.getTraceElementClass();
	}

	@Override
	public IBacktranslationValueProvider<IIcfgTransition<IcfgLocation>, Term> getBacktranslationValueProvider() {
		return mProgramExecution.getBacktranslationValueProvider();
	}

	@Override
	public boolean isConcurrent() {
		return mProgramExecution.isConcurrent();
	}

}
