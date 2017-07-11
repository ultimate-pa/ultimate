package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.arraytheory;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

public class SMTTheoryDomain implements IAbstractDomain<SMTTheoryState, IcfgEdge, IProgramVarOrConst> {
	
	private final SMTTheoryPostOperator mPostOperator;

	public SMTTheoryDomain(IUltimateServiceProvider services, CfgSmtToolkit csToolkit) {
		mPostOperator = new SMTTheoryPostOperator(services, csToolkit);
	}

	@Override
	public SMTTheoryState createTopState() {
		return mPostOperator.getStateFactory().getTopState();
	}

	@Override
	public SMTTheoryState createBottomState() {
		return mPostOperator.getStateFactory().getBottomState();
	}

	@Override
	public IAbstractStateBinaryOperator<SMTTheoryState> getWideningOperator() {
		return new IAbstractStateBinaryOperator<SMTTheoryState>() {
			@Override
			public SMTTheoryState apply(SMTTheoryState first, SMTTheoryState second) {
				return mPostOperator.getStateFactory().widen(first, second);
			}
		};
	}

	@Override
	public IAbstractPostOperator<SMTTheoryState, IcfgEdge, IProgramVarOrConst> getPostOperator() {
		return mPostOperator;
	}

	@Override
	public boolean useHierachicalPre() {
		return true;
	}
	
	

}
