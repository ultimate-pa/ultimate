package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Implementation of a simple widening operator that just returns a new interval of the form (-&infin; ; &infin;).
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class IntervalSimpleWideningOperator implements IAbstractStateBinaryOperator<CodeBlock, BoogieVar> {

	@Override
	public IAbstractState<CodeBlock, BoogieVar> apply(IAbstractState<CodeBlock, BoogieVar> first,
	        IAbstractState<CodeBlock, BoogieVar> second) {
		return new IntervalDomainState<CodeBlock, BoogieVar>();
	}

}
