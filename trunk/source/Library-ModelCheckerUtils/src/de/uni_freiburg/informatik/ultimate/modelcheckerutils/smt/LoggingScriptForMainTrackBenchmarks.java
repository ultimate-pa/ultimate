package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.io.File;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;

public class LoggingScriptForMainTrackBenchmarks extends LoggingScriptForNonIncrementalBenchmarks {
	
	private int m_WrittenScriptCounter = 0;

	public LoggingScriptForMainTrackBenchmarks(Script script,
			String baseFilename, String directory) {
		super(script, baseFilename, directory);
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		LBool sat = super.checkSat();
		if (sat == LBool.UNKNOWN) {
			File file = constructFile("_" + String.valueOf(m_WrittenScriptCounter));
			writeCommandStackToFile(file, m_CommandStack);
			m_WrittenScriptCounter++;
		}
		return sat;
	}
	
	

}
