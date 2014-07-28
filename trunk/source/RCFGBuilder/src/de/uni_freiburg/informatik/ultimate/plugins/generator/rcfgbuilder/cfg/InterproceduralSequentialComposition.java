package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;

public class InterproceduralSequentialComposition extends SequentialComposition {

	private static final long serialVersionUID = -1637790156358220366L;

	public InterproceduralSequentialComposition(ProgramPoint source,
			ProgramPoint target, Boogie2SMT boogie2smt, 
			ModifiableGlobalVariableManager modGlobVarManager, 
			boolean simplify, boolean extPqe, CodeBlock[] codeBlocks, Logger logger, IUltimateServiceProvider services) {
		super(source, target, boogie2smt, modGlobVarManager, simplify, extPqe, services, codeBlocks);
	}

	@Override
	protected void checkNumberOfCallsAndReturns(int numberCalls, int  numberReturns) {
		if(numberCalls <= numberReturns) {
			throw new IllegalArgumentException("more calls and returns required");
		}
	}
	
	
	
}
