package de.uni_freiburg.informatik.ultimate.irs.dependencies.observers;

import de.uni_freiburg.informatik.ultimate.irs.dependencies.boogie.CriticalSectionTransformer;
import de.uni_freiburg.informatik.ultimate.irs.dependencies.boogie.SymbolTable;
import de.uni_freiburg.informatik.ultimate.model.IElement;

public class ASTDependencyFinder extends BaseObserver{

	protected final SymbolTable mSymbolTable;
	
	public ASTDependencyFinder(SymbolTable symbolTable) {
		super();
		mSymbolTable = symbolTable;
	}

	public boolean process(IElement root) {
		return new CriticalSectionTransformer(mSymbolTable).process(root);
	}

}
