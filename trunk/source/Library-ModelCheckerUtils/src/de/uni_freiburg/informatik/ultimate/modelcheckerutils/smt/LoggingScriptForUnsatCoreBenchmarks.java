package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.ArrayList;
import java.util.LinkedList;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class LoggingScriptForUnsatCoreBenchmarks extends
		LoggingScriptForNonIncrementalBenchmarks {
	

	private LinkedList<ArrayList<ISmtCommand>> m_CommandStackAtLastGetUnsatCore;

	public LoggingScriptForUnsatCoreBenchmarks(Script script,
			String baseFilename, String directory) {
		super(script, baseFilename, directory);
	}

	@Override
	public Term[] getUnsatCore() throws SMTLIBException,
			UnsupportedOperationException {
		Term[] result = super.getUnsatCore();
		m_CommandStackAtLastGetUnsatCore = deepCopyOfCommandStack();
		return result;
	}

	@Override
	public void exit() {
		if (m_CommandStackAtLastGetUnsatCore != null) {
			writeCommandStackToFile(constructFile("_UnsatCore"), m_CommandStackAtLastGetUnsatCore);
		}
		super.exit();
	}
	
	
	
	

}
