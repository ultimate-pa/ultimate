package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.observers;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.BaseObserver;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.boogie.CriticalSectionTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.boogie.SymbolTable;

public class ASTDependencyFinder extends BaseObserver{

	protected final SymbolTable mSymbolTable;
	private final Logger mLogger;
	
	public ASTDependencyFinder(SymbolTable symbolTable, Logger logger) {
		super();
		mSymbolTable = symbolTable;
		mLogger = logger;
	}

	public boolean process(IElement root) {
		return new CriticalSectionTransformer(mSymbolTable, mLogger).process(root);
	}

}
