package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;

public class InterproceduralSequentialComposition extends SequentialComposition {

	private static final long serialVersionUID = -1637790156358220366L;

	public InterproceduralSequentialComposition(ProgramPoint source,
			ProgramPoint target, Boogie2SMT boogie2smt, 
			ModifiableGlobalVariableManager modGlobVarManager, 
			boolean simplify, CodeBlock[] codeBlocks) {
		super(source, target, boogie2smt, modGlobVarManager, simplify, codeBlocks);
	}

	@Override
	protected void checkNumberOfCallsAndReturns(int numberCalls, int  numberReturns) {
		if(numberCalls <= numberReturns) {
			throw new IllegalArgumentException("more calls and returns required");
		}
	}
	
	
	
}
