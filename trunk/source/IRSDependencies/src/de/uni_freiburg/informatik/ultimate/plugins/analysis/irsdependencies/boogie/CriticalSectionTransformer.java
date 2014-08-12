package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.boogie;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.structure.WrapperNode;

public class CriticalSectionTransformer extends BoogieTransformer {
	
	protected SymbolTable mSymbolTable;
	private final Logger mLogger;
	
	public CriticalSectionTransformer(SymbolTable symbolTable, Logger logger) {
		mSymbolTable = symbolTable;
		mLogger = logger;
	}

	public boolean process(IElement root)
	{
		if (root instanceof WrapperNode) {
			Unit unit = (Unit) ((WrapperNode) root).getBacking();
			Declaration[] declarations = unit.getDeclarations();

			for (Declaration decl : declarations) {
				processDeclaration(decl);
			}
			return false;
		}
		else {
			return true;
		}
	}
	
	@Override
	protected Declaration processDeclaration(Declaration decl) {
		mLogger.debug(decl);
		return super.processDeclaration(decl);
	}
	
	@Override
	protected Body processBody(Body body) {
		mLogger.debug(body);
		return super.processBody(body);
	}
	
	@Override
	protected Statement processStatement(Statement statement) {
		mLogger.debug(statement);
		return super.processStatement(statement);
	}

}
