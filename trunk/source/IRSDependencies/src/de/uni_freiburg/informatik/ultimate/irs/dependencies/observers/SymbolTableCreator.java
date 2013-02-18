package de.uni_freiburg.informatik.ultimate.irs.dependencies.observers;

import de.uni_freiburg.informatik.ultimate.irs.dependencies.boogie.SymbolTable;
import de.uni_freiburg.informatik.ultimate.irs.dependencies.boogie.SymbolTableTransformer;
import de.uni_freiburg.informatik.ultimate.model.IElement;

public class SymbolTableCreator extends BaseObserver
{
	protected SymbolTable mSymbolTable;

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
		SymbolTableTransformer transformer = new SymbolTableTransformer();
		boolean finished = transformer.process(root);
		mSymbolTable = transformer.getSymbolTable();
		return finished;
	}

}
