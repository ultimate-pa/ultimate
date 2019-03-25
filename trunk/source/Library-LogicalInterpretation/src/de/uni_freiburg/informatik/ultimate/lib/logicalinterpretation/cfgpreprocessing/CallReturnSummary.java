package de.uni_freiburg.informatik.ultimate.lib.logicalinterpretation.cfgpreprocessing;

import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgSummaryTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;

public class CallReturnSummary implements IIcfgSummaryTransition<IcfgLocation> {

	private static final long serialVersionUID = -7088726231519978619L;

	private final IIcfgCallTransition<IcfgLocation> mCall;
	private	final IIcfgReturnTransition<IcfgLocation, IIcfgCallTransition<IcfgLocation>> mReturn;

	public CallReturnSummary(final IIcfgCallTransition<IcfgLocation> callEdge,
			final IIcfgReturnTransition<IcfgLocation, IIcfgCallTransition<IcfgLocation>> returnEdge) {
		mCall = callEdge;
		mReturn = returnEdge;
	}

	public IIcfgCallTransition<IcfgLocation> getCall() {
		return mCall;
	}

	public IIcfgReturnTransition<IcfgLocation, IIcfgCallTransition<IcfgLocation>> getReturn() {
		return mReturn;
	}

	@Override
	public IcfgLocation getSource() {
		return mCall.getSource();
	}

	@Override
	public IcfgLocation getTarget() {
		return mReturn.getTarget();
	}

	@Override
	public IPayload getPayload() {
		return null;
	}

	@Override
	public boolean hasPayload() {
		return false;
	}

	@Override
	public String getPrecedingProcedure() {
		return mCall.getPrecedingProcedure();
	}

	@Override
	public String getSucceedingProcedure() {
		return mReturn.getSucceedingProcedure();
	}

	@Override
	public UnmodifiableTransFormula getTransformula() {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean calledProcedureHasImplementation() {
		throw new UnsupportedOperationException();
	}

}
