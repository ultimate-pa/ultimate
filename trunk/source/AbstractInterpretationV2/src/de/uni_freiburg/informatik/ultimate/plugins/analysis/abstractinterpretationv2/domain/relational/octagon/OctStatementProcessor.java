package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;

public class OctStatementProcessor extends BoogieVisitor {

	private final Logger mLogger;
	private final BoogieSymbolTable mSymbolTable;
	
	private OctagonDomainState mOldState;
	private OctagonDomainState mNewState;
	
	public OctStatementProcessor(Logger logger, BoogieSymbolTable symbolTable) {
		mLogger = logger;
		mSymbolTable = symbolTable;
	}

	public OctagonDomainState process(OctagonDomainState oldState, Statement statement) {
		mOldState = oldState;

		// TODO implement
		
		throw new UnsupportedOperationException("post operator not implemented");
	}

}
