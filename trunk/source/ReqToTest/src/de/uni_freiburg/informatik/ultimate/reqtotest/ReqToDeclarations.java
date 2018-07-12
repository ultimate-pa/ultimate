package de.uni_freiburg.informatik.ultimate.reqtotest;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeGlob;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.BndResponsePatternUT;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InvariantPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.pea2boogie.CddToSmt;

public class ReqToDeclarations {

	private final ILogger mLogger;
	private final ReqSymbolExpressionTable mReqSymbolExpressionTable;
	
	public ReqToDeclarations(final ILogger logger){
		mLogger = logger;
		mReqSymbolExpressionTable = new ReqSymbolExpressionTable(logger);
	}
	
	public ReqSymbolExpressionTable patternListToBuechi(List<PatternType> patternList){
		for (PatternType pattern: patternList) {
			if (pattern instanceof InitializationPattern) {
				mReqSymbolExpressionTable.extractVariablesFromInit((InitializationPattern)pattern);
			} 
		}
		return mReqSymbolExpressionTable;
	}	
}
