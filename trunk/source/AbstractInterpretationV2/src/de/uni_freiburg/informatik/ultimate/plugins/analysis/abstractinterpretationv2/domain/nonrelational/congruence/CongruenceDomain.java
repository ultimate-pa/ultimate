package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.congruence;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * 
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */

public class CongruenceDomain implements IAbstractDomain<CongruenceDomainState, CodeBlock, IBoogieVar> {	
	
	private final BoogieSymbolTable mSymbolTable;
	private final Logger mLogger;
	
	public CongruenceDomain(Logger logger, BoogieSymbolTable symbolTable) {
		mLogger = logger;
		mSymbolTable = symbolTable;
		
	}

	@Override
	public CongruenceDomainState createFreshState() {
		return new CongruenceDomainState(mLogger);
	}

	@Override
	public IAbstractStateBinaryOperator<CongruenceDomainState> getWideningOperator() {
		// Widening is the same as merge, so we don't need an extra operator
		return new CongruenceMergeOperator();
	}

	@Override
	public IAbstractStateBinaryOperator<CongruenceDomainState> getMergeOperator() {
		return new CongruenceMergeOperator();
	}

	@Override
	public IAbstractPostOperator<CongruenceDomainState, CodeBlock, IBoogieVar> getPostOperator() {
		return new CongruencePostOperator(mLogger, mSymbolTable);
	}

	@Override
	public int getDomainPrecision() {
		return 300;
	}
}
