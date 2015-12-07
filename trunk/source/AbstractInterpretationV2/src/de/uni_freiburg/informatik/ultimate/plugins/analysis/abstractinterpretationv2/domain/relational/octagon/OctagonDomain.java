package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class OctagonDomain implements IAbstractDomain<OctagonDomainState, CodeBlock, IBoogieVar> {

	private final BoogieSymbolTable mSymbolTable;
	private final Logger mLogger;

	public OctagonDomain(Logger logger, BoogieSymbolTable symbolTable) {
		mLogger = logger;
		mSymbolTable = symbolTable;
	}

	@Override
	public OctagonDomainState createFreshState() {
		return OctagonDomainState.createFreshState();
	}

	@Override
	public IAbstractStateBinaryOperator<OctagonDomainState> getWideningOperator() {
		return new OctExponentialWideningOperator(new OctValue(Integer.MAX_VALUE));
	}

	@Override
	public IAbstractStateBinaryOperator<OctagonDomainState> getMergeOperator() {
		return new IAbstractStateBinaryOperator<OctagonDomainState>() {
			@Override
			public OctagonDomainState apply(OctagonDomainState first, OctagonDomainState second) {
				return first.join(second);
			}
		};
	}

	@Override
	public IAbstractPostOperator<OctagonDomainState, CodeBlock, IBoogieVar> getPostOperator() {
		return new OctPostOperator(mLogger, mSymbolTable);
	}
	
}