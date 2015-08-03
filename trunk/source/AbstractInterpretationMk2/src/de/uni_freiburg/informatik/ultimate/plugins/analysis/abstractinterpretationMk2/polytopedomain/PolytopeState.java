package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.polytopedomain;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.AbstractVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractState;



public class PolytopeState 
	implements IAbstractState<PolytopeState> 
{
	

	private boolean mIsBottom;
	private boolean mIsTop;
	
	public PolytopeState()
	{
		mIsBottom = false;
		mIsTop = false;
		
		throw new NotImplementedException();
	}

	@Override
	public boolean isSuper(IAbstractState<PolytopeState> state)
	{
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public void DeclareVariable(AbstractVariable variable)
	{
		// TODO Auto-generated method stub
		
	}

	@Override
	public void RemoveVariable(AbstractVariable variable)
	{
		// TODO Auto-generated method stub
		
	}

	@Override
	public IAbstractState<PolytopeState> copy()
	{
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isBottom()
	{
		if(mIsBottom || false) // TODO: check if this is bottom
		{
			mIsBottom = true;
			return true;
		}
		throw new NotImplementedException();
	}

	@Override
	public boolean isTop()
	{
		if(mIsTop || false) // TODO: check if this is top
		{
			mIsTop = true;
			return true;
		}
		throw new NotImplementedException();	
	}

	@Override
	public PolytopeState getConcrete()
	{		
		return this;
	}
}