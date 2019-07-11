package de.uni_freiburg.informatik.ultimate.reqtotest.req;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;

public class ReqToDeclarations {

	private final ILogger mLogger;
	private final Req2TestReqSymbolTable mReqSymbolExpressionTable;
	
	public ReqToDeclarations(final ILogger logger){
		mLogger = logger;
		mReqSymbolExpressionTable = new Req2TestReqSymbolTable(logger);
	}
	
	public Req2TestReqSymbolTable initPatternToSymbolTable(List<PatternType> patternList){
		for (PatternType pattern: patternList) {
			if (pattern instanceof InitializationPattern) {
				mReqSymbolExpressionTable.extractVariablesFromInit((InitializationPattern)pattern);
			} 
		}
		return mReqSymbolExpressionTable;
	}	
}
