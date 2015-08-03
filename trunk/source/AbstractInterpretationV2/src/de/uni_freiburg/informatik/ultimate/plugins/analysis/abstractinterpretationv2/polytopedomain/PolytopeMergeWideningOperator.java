package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.polytopedomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractWideningOperator;

public class PolytopeMergeWideningOperator 
	implements IAbstractMergeOperator<PolytopeState>, IAbstractWideningOperator<PolytopeState> 
{

	private final Logger mLogger;
	
	private final PolytopeDomain mDomain;
	
	public PolytopeMergeWideningOperator(Logger logger, PolytopeDomain domain)
	{
		mLogger = logger;
		mDomain = domain;
	}

	@Override
	public IAbstractState<PolytopeState> apply(IAbstractState<PolytopeState> a, IAbstractState<PolytopeState> b)
	{
		// TODO Auto-generated method stub
		return null;
	}
}
