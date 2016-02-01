package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;

public class OctAssumeProcessor {

	private final Logger mLogger;
	private final BoogieSymbolTable mSymbolTable;

	private List<OctagonDomainState> mOldStates;
	private List<OctagonDomainState> mNewStates;
	
	public OctAssumeProcessor(Logger logger, BoogieSymbolTable symbolTable) {
		mLogger = logger;
		mSymbolTable = symbolTable;
	}
	
	public List<OctagonDomainState> assume(List<OctagonDomainState> oldStates, Expression assumption) {
	
		// TODO assume
		
		return oldStates; // safe over-approximation
	}
}
