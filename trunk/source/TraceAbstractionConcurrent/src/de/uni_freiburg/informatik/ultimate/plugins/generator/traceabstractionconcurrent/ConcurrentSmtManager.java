package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent;

import java.util.HashSet;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Smt2Boogie;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceValues.Solver;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public class ConcurrentSmtManager extends SmtManager {

	
	public ConcurrentSmtManager(Smt2Boogie smt2Boogie, Solver solver,
			Map<String, ASTType> globalVars, boolean dumpFormulaToFile,
			String dumpPath) {
		super(smt2Boogie, solver, globalVars, dumpFormulaToFile, dumpPath);
		// TODO Auto-generated constructor stub
	}

	ProdState getNewProdState(List<IPredicate> programPoints) {
		return new ProdState(m_SerialNumber++, programPoints, super.getScript().term("true"),new HashSet<BoogieVar>(0));
	}
}
