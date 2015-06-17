package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class RcfgVariableProvider implements IVariableProvider<CodeBlock, BoogieVar> {

	@Override
	public IAbstractState<CodeBlock, BoogieVar> defineVariablesPre(CodeBlock current,
			IAbstractState<CodeBlock, BoogieVar> state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IAbstractState<CodeBlock, BoogieVar> defineVariablesPost(CodeBlock current,
			IAbstractState<CodeBlock, BoogieVar> state) {
		// TODO Auto-generated method stub
		return null;
	}

}
