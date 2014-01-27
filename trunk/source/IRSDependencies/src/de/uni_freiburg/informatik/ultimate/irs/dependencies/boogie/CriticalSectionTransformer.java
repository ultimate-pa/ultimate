package de.uni_freiburg.informatik.ultimate.irs.dependencies.boogie;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.irs.dependencies.Activator;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.structure.WrapperNode;

public class CriticalSectionTransformer extends BoogieTransformer {
	
	protected SymbolTable mSymbolTable;
	private static Logger sLogger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);
	
	public CriticalSectionTransformer(SymbolTable symbolTable) {
		mSymbolTable = symbolTable;
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
		sLogger.debug(decl);
		return super.processDeclaration(decl);
	}
	
	@Override
	protected Body processBody(Body body) {
		sLogger.debug(body);
		return super.processBody(body);
	}
	
	@Override
	protected Statement processStatement(Statement statement) {
		sLogger.debug(statement);
		return super.processStatement(statement);
	}

}
