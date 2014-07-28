package de.uni_freiburg.informatik.ultimate.irsdependencies.observers;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.BaseObserver;
import de.uni_freiburg.informatik.ultimate.irsdependencies.boogie.SymbolTable;
import de.uni_freiburg.informatik.ultimate.irsdependencies.boogie.SymbolTableTransformer;
import de.uni_freiburg.informatik.ultimate.model.IElement;

public class SymbolTableCreator extends BaseObserver
{
	protected SymbolTable mSymbolTable;
	private final Logger mLogger;

	public SymbolTableCreator(Logger logger) {
		mLogger = logger;
	}
	
	@Override
	public void init()
	{
		super.init();
		mSymbolTable = new SymbolTable();
	}
	
	public SymbolTable getSymbolTable()
	{
		return mSymbolTable;
	}

	@Override
	public boolean process(IElement root)
	{
		SymbolTableTransformer transformer = new SymbolTableTransformer(mLogger);
		boolean finished = transformer.process(root);
		mSymbolTable = transformer.getSymbolTable();
		return finished;
	}

}
