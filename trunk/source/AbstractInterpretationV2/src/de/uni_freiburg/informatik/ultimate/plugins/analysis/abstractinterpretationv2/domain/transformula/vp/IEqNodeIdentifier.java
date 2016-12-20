package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

public interface IEqNodeIdentifier<ARRAYID> {

	
	public boolean isFunction();

	public ARRAYID getFunction();
	
	public boolean isLiteral();
}
